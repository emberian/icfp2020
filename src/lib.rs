#![feature(
    try_trait,
    label_break_value,
    generators,
    generator_trait,
    untagged_unions,
    maybe_uninit_ref
)]

const GALAXY: &str = include_str!("galaxy.txt");

#[path = "machine.rs"]
mod machine;
#[path = "repl.rs"]
mod repl_;

pub use repl_::repl;

mod graph;
pub mod parse;

//pub mod machine {
//    pub use crate::mach::{
//        aa, ae, ea, ee, Ty, Continuation, DataVisitor, Engine, EngineError,
//        EngineErrorKind, ForceArgsState, ForceListState,
//        State, Ty,
//    };
//}
//

pub use graph::{
    ApplicativeForm, Arity, ExtendedData, FunDef, Heap, ObjData, PartialData, Ref, RefList, RefTag,
    TaggedData, TaggedObjView, ThunkData,
};
pub use machine::{
    Continuation, Engine, EngineError, EngineErrorKind, ForceArgsState, ForceListState, Primitive,
    State, Ty,
};

enum TestTrace {
    ParseFail(String, String, parse::ParsingError),
    CheckFailed(String, String, String),
    EvalFailed(String, machine::EngineError),
}
pub struct TestReport {
    reports: Vec<TestTrace>,
}

impl std::fmt::Debug for TestReport {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let fail_count = self.reports.len();
        for rep in &self.reports {
            match rep {
                ParseFail(lhs, _, err) => writeln!(f, "error while parsing {}: {}", lhs, err)?,
                CheckFailed(lhs, rhs, result) => {
                    writeln!(f, "result mismatch: {} -> {} != {}", lhs, result, rhs)?
                }
                EvalFailed(lhs, err) => writeln!(f, "error while evaluating {}: {}", lhs, err)?,
            }
            writeln!(f, "-----------------------------------------")?
        }
        writeln!(f, "{} tests failed", fail_count)
    }
}
use TestTrace::*;

#[test]
fn basic_tests() -> Result<(), TestReport> {
    self_test()
}

pub fn self_test() -> Result<(), TestReport> {
    use machine::*;
    let test_cases = vec![
        ("4", "4"),
        ("-3", "-3"),
        ("ap inc 0", "1"),
        ("ap inc -1", "0"),
        ("ap dec 0", "-1"),
        ("ap ap add 42 42", "84"),
        ("ap ap mul 4 -3", "-12"),
        ("ap ap div -5 3", "-1"),
        ("ap neg 888", "-888"),
        ("ap ap mul 4 2", "8"),
        ("ap ap mul 3 4", "12"),
        ("ap ap mul 3 -2", "-6"),
        ("ap ap div 4 2", "2"),
        ("ap ap div 4 3", "1"),
        ("ap ap div 4 4", "1"),
        ("ap ap div 4 5", "0"),
        ("ap ap div 5 2", "2"),
        ("ap ap div 6 -2", "-3"),
        ("ap ap div 5 -3", "-1"),
        ("ap ap div -5 3", "-1"),
        ("ap ap div -5 -3", "1"),
        ("ap ap eq 1 -1", "f"),
        ("ap ap eq 1 0", "f"),
        ("ap ap eq 1 1", "t"),
        ("ap ap eq 1 2", "f"),
        ("ap ap lt 0 -1", "f"),
        ("ap ap lt 0 0", "f"),
        ("ap ap lt 0 2", "t"),
        ("ap ap lt 1 1", "f"),
        ("ap ap lt 1 2", "t"),
        ("ap ap lt 2 1", "f"),
        ("ap ap lt 2 2", "f"),
        ("ap ap lt 2 4", "t"),
        ("ap ap lt 20 20", "f"),
        ("ap ap lt 21 20", "f"),
        ("ap ap lt -19 -20", "f"),
        ("ap ap lt -20 -20", "f"),
        ("ap ap lt -21 -20", "t"),
        ("ap neg 0", "0"),
        ("ap neg 1", "-1"),
        ("ap neg -1", "1"),
        ("ap neg 2", "-2"),
        ("ap neg -2", "2"),
        ("ap inc ap inc 0", "2"),
        ("ap inc ap inc ap inc 0", "3"),
        ("ap inc ap dec 42", "42"),
        ("ap dec ap inc 42", "42"),
        ("ap dec ap ap add 90 1", "90"),
        ("ap ap add ap ap add 2 3 4", "9"),
        ("ap ap add 2 ap ap add 3 4", "9"),
        ("ap ap add ap ap mul 2 3 4", "10"),
        ("ap ap mul 2 ap ap add 3 4", "14"),
        ("ap ap ap s x0 x1 x2", "ap ap x0 x2 ap x1 x2"),
        ("ap ap ap s add inc 1", "3"),
        ("ap ap ap s mul ap add 1 6", "42"),
        ("ap ap ap c x0 x1 x2", "ap ap x0 x2 x1"),
        ("ap ap ap c add 1 2", "3"),
        ("ap ap ap b x0 x1 x2", "ap x0 ap x1 x2"),
        ("ap ap t x0 x1", "x0"),
        ("ap ap t 1 5", "1"),
        ("ap ap t t i", "t"),
        ("ap ap t t ap inc 5", "t"),
        ("ap ap t ap inc 5 t", "6"),
        ("ap ap f x0 x1", "x1"),
        ("ap i x0", "x0"),
        ("ap i 1", "1"),
        ("ap i i", "i"),
        ("ap i add", "add"),
        ("ap i ap add 1", "ap add 1"),
        ("ap nil x0", "t"),
        ("ap isnil nil", "t"),
        ("ap isnil ap ap cons x0 x1", "f"),
        ("ap isnil ap ap cons x0 x1", "f"),
        ("ap cdr ap ap cons 0 nil", "nil"),
        ("ap ap ap if0 0 x0 x1", "x0"),
        ("ap ap ap if0 1 x0 x1", "x1"),
        (
            r#"foo = isnil
            ap foo nil"#,
            "t",
        ),
        (
            r#"foo = cons
            ap ap foo 1 nil"#,
            "ap ap cons 1 nil",
        ),
        (
            r#"foo = ap ap cons 0 foo
            ap car foo"#,
            "0",
        ),
    ];
    let mut results = vec![];
    'outer: for (lhs, rhs) in test_cases {
        let mut defs = fnv::FnvHashMap::default();
        let eng = Engine::new();
        let lines: Vec<&str> = lhs.lines().collect();

        let expr;
        if lines.len() > 1 {
            let (runnable, defines) = lines.split_last().unwrap();
            for def in defines {
                match parse::cmd(def.trim(), &eng.state.heap, &mut defs) {
                    Ok((name, cell)) => {
                        eng.state.add_definition(name, cell);
                    }
                    Err(e) => {
                        results.push(ParseFail(def.to_string(), rhs.into(), e));
                        continue 'outer;
                    }
                };
            }

            expr = runnable;
        } else {
            expr = &lines[0];
        }

        let result = match parse::expr(expr, &eng.state.heap, &mut defs) {
            Ok(expr) => eng.eval(expr),
            Err(e) => {
                results.push(ParseFail(lhs.into(), rhs.into(), e));
                continue;
            }
        };
        match result {
            Ok(result) => {
                let s = format!("{}", result).to_ascii_lowercase();
                if s != rhs.to_ascii_lowercase() {
                    results.push(CheckFailed(lhs.into(), rhs.into(), s));
                }
            }
            Err(e) => results.push(EvalFailed(lhs.into(), e)),
        }
    }

    if results.is_empty() {
    } else {
    }
    Ok(())
}
