use crate::*;

pub fn repl<R>(e: &Engine, mut readline: R) -> Result<(), EngineError>
where
    R: FnMut(&str) -> Option<String>,
{
    let filter = tracing_subscriber::EnvFilter::new("embershot=trace")
        // Set the base level when not matched by other directives to WARN.
        .add_directive(tracing_subscriber::filter::LevelFilter::WARN.into());

    let sub = tracing_subscriber::fmt()
        .with_max_level(tracing::Level::TRACE)
        .with_env_filter(filter)
        .without_time()
        .with_span_events(tracing_subscriber::fmt::format::FmtSpan::CLOSE)
        .finish();

    let tracer = tracing::Dispatch::new(sub);
    let empty_tracer = tracing::Dispatch::none();

    let mut to_trace_with = &empty_tracer;
    let mut trace = false;

    loop {
        let s = match readline("<- ") {
            Some(s) => s,
            None => {
                return Err(EngineError::without_debug(EngineErrorKind::Mistake(
                    "readline failed?",
                )))
            }
        };

        let mut tokens = s.split_ascii_whitespace();
        // super secret repl control mode.
        match tokens.next().unwrap_or("nah fam").trim() {
            "!trace" => {
                trace = !trace;
                println!(
                    "trace is now {}",
                    if trace {
                        to_trace_with = &tracer;
                        "on"
                    } else {
                        to_trace_with = &empty_tracer;
                        "off"
                    }
                );
                continue;
            }
            "!notrace" => {
                to_trace_with = &empty_tracer;
                continue;
            }
            "!galaxy" => {
                let _ = e.load_galaxy();
                continue;
            }
            "!selftest" => {
                match crate::self_test() {
                    Ok(_) => {}
                    Err(report) => println!("{:?}", report),
                }
                continue;
            }
            "!dumpstate" => {
                eprintln!("{:?}", e);
                continue;
            }
            "quit" => break,
            _ => {}
        }

        // ingest variable definitions
        let second_token = tokens.next();
        if let Some("=") = second_token {
            let (name, cell) = crate::parse::cmd(
                s.trim(),
                &e.state.heap,
                &mut *e.state.definitions.borrow_mut(),
            )?;
            e.state.add_definition(name, cell);
            continue;
        }

        let res = tracing::dispatcher::with_default(to_trace_with, || e.exec(&s));

        match res {
            Ok(res) => {
                if trace {
                    println!("=> {:?}", res)
                } else {
                    println!("=> {}", res)
                }
            }
            Err(e) => eprintln!("error: {}", e),
        }
    }

    Ok(())
}
