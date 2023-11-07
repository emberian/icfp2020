#![feature(try_trait, generators, generator_trait)]

extern crate embershot;

use rustyline::{error::ReadlineError, Editor};

fn main() -> Result<(), embershot::EngineError> {
    let e = embershot::Engine::new();

    match embershot::self_test() {
        Ok(_) => println!("self-test passed, welcome to the repl!"),
        _ => println!(":( self-test failed ): you're on your own, good luck!"),
    }

    let mut rl = Editor::<()>::new();

    embershot::repl(&e, |prompt| match rl.readline(prompt) {
        Ok(line) => {
            rl.add_history_entry(line.as_str());
            Some(line)
        }
        Err(ReadlineError::Interrupted) => {
            println!("CTRL-C");
            None
        }
        Err(ReadlineError::Eof) => {
            println!("CTRL-D");
            None
        }
        Err(err) => {
            println!("Error: {:?}", err);
            None
        }
    })
}
