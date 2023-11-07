use arc_swap::ArcSwapOption;
use either::Either;
use fnv::FnvHashMap as HashMap;
use std::mem::ManuallyDrop;
use std::rc::Rc;
use std::sync::Arc;
use thiserror::Error;

use crate::*;

/// parses the language of `delim Val Val | atom`. doesn't blow the stack! atom is
/// constructed by ret of a token. when a delim is done parsing we combine with
/// comb. use next to get more tokens. ez pz.
pub fn parse_double_thingy<Val, Tok, Err>(
    mut next: impl FnMut() -> Result<Tok, Err>,
    tok_is_delim: impl Fn(&Tok) -> bool,
    comb: impl Fn(Val, Val) -> Val,
    ret: impl Fn(Tok) -> Val,
) -> Result<Val, Err> {
    #[derive(Clone)]
    enum What {
        Start,
        Finish,
    }
    use What::*;
    let mut stack = vec![Start];
    let mut valstack = vec![];
    while let Some(op) = stack.pop() {
        match op {
            Start => {
                let val = next()?;
                if tok_is_delim(&val) {
                    stack.push(Finish);
                    stack.push(Start);
                    stack.push(Start);
                }
                valstack.push(ret(val));
            }
            Finish => {
                let rhs = valstack.pop();
                let lhs = valstack.pop();
                valstack.push(comb(lhs.unwrap(), rhs.unwrap()));
            }
        }
    }
    Ok(valstack.pop().unwrap())
}

type SymbolMap<'a> = &'a mut HashMap<Arc<String>, ThunkData>;

pub struct Parser<'a, S, I: Iterator<Item = S>> {
    tokens: I,
    heap: &'a crate::Heap,
    defined_symbols: SymbolMap<'a>,
}

#[derive(Error, Debug)]
pub enum ParsingError {
    #[error("Input closed")]
    Eof,
    #[error("cmd parsing error: {}", .0)]
    BadCmd(&'static str),
    #[error("was expecting {:?} but found {}", .0, .1)]
    Expecting(Expectable, Ref),
    #[error("needed a name on lhs of cmd but found {}", .0)]
    NameRequired(Ref),
}

#[derive(Debug, Clone)]
pub enum Expectable {
    ByType(Ty),
    Exact(Ref),
    // could also have exactly-one-of, maybe some others? idk.
}

impl<'a, S, I: Iterator<Item = S>> Parser<'a, S, I>
where
    S: std::ops::Deref<Target = str>,
{
    pub fn new(
        tokens: I,
        heap: &'a crate::Heap,
        defined_symbols: SymbolMap<'a>,
    ) -> Parser<'a, S, I> {
        Parser {
            defined_symbols,
            heap,
            tokens,
        }
    }

    pub fn parse_expr(&mut self) -> Result<ApplicativeForm, ParsingError> {
        let hp = self.heap;
        parse_double_thingy(
            || self.next(),
            |t| t.value == Ref::prim(Primitive::Ap).value,
            |lv, rv| hp.ee(lv, rv),
            |tok| ApplicativeForm::Ref(tok),
        )
    }

    fn expect(&mut self, e: Expectable) -> Result<Ref, ParsingError> {
        use TaggedObjView::*;
        let atom = self.next()?;
        let maybe_atom = match (atom.deref(), e.clone()) {
            (_, Expectable::Exact(desired)) => {
                if atom == desired {
                    Ok(atom)
                } else {
                    Err(atom)
                }
            }
            // Lits are numbers
            (SmallNum(_), Expectable::ByType(Ty::Num))
            | (BigNum(_), Expectable::ByType(Ty::Num)) => Ok(atom),
            (SmallNum(_), Expectable::ByType(_)) | (BigNum(_), Expectable::ByType(_)) => Err(atom),
            // Everything is an atom.
            (a, Expectable::ByType(Ty::Ref)) => Ok(atom),
            // Prims are prims and also symbols
            (Builtin(_), Expectable::ByType(Ty::Prim))
            | (Builtin(_), Expectable::ByType(Ty::Sym)) => Ok(atom),
            // Symbols are symbols, and also heap objects
            (Symbol(_, _), Expectable::ByType(Ty::Sym))
            | (Symbol(_, _), Expectable::ByType(Ty::HeapObj)) => Ok(atom),
            // Everything else is a heap object
            (_, Expectable::ByType(Ty::HeapObj)) => Ok(atom),
            (_, _) => Err(atom),
        };
        match maybe_atom {
            Ok(a) => Ok(a),
            Err(a) => Err(ParsingError::Expecting(e, a)),
        }
    }

    pub fn parse_cmd(&mut self) -> Result<(Arc<String>, ThunkData), ParsingError> {
        let n = self.expect(Expectable::ByType(Ty::Sym))?;
        let _eq = self.expect(Expectable::Exact(Ref::prim(Primitive::Define)))?;
        let body = self.parse_expr()?;
        match n.deref() {
            TaggedObjView::Symbol(td, name) => {
                let th = self.heap.thunk(body);
                td.finish_result(th);
                Ok((name.clone(), td.clone()))
            }
            _ => Err(ParsingError::NameRequired(n)),
        }
    }

    /// Parse an atom out of a token.
    fn next(&mut self) -> Result<Ref, ParsingError> {
        use Primitive::*;
        Ok(Ref::prim(
            match &*self
                .tokens
                .next()
                .ok_or(ParsingError::Eof)?
                .to_ascii_lowercase()
            {
                "inc" => Inc,
                "dec" => Dec,
                "add" => Add,
                "mul" => Mul,
                "div" => Div,
                "eq" => Eq,
                "lt" => Lt,
                "mod" => Mod,
                "dem" => Demod,
                "send" => Send,
                "neg" => Neg,
                "ap" => Ap,
                "s" => S,
                "c" => C,
                "b" => B,
                "t" => T,
                "f" => F,
                "pwr2" => Pwr2,
                "i" => I,
                "vec" | "cons" => Cons,
                "car" => Car,
                "cdr" => Cdr,
                "nil" => Nil,
                "isnil" => IsNil,
                "draw" => Draw,
                "multipledraw" => Multidraw,
                "if0" => If0,
                "=" => Define,
                s => match s.parse::<num::BigInt>() {
                    Ok(n) => return Ok(self.heap.num(Arc::new(n))),
                    Err(_) => {
                        let name = Arc::new(s.to_owned());
                        let sym_freevar = self.heap.allocate(
                            RefTag::Extended,
                            ObjData {
                                extended: ManuallyDrop::new(ExtendedData::FreeVariable(
                                    name.clone(),
                                )),
                            },
                        );
                        let td = ThunkData(ArcSwapOption::from_pointee(Either::Right(sym_freevar)));
                        self.defined_symbols
                            .entry(name.clone())
                            .or_insert_with(|| td.clone());
                        return Ok(self.heap.allocate(
                            RefTag::Thunk,
                            ObjData {
                                thunk: ManuallyDrop::new(ThunkData(ArcSwapOption::from_pointee(
                                    Either::Right(sym_freevar),
                                ))),
                            },
                        ));
                    }
                },
            },
        ))
    }
}

pub fn expr(s: &str, heap: &crate::Heap, map: SymbolMap) -> Result<ApplicativeForm, ParsingError> {
    Parser::new(s.split_ascii_whitespace(), heap, map).parse_expr()
}

pub fn cmd(
    s: &str,
    heap: &crate::Heap,
    map: SymbolMap,
) -> Result<(Arc<String>, ThunkData), ParsingError> {
    Parser::new(s.split_ascii_whitespace(), heap, map).parse_cmd()
}

/// parse newline-separated list of a = b commands
pub fn cmds(
    s: &str,
    heap: &crate::Heap,
    map: SymbolMap,
) -> Result<Vec<(Arc<String>, ThunkData)>, ParsingError> {
    s.lines().map(|l| cmd(l, heap, map)).collect()
}
