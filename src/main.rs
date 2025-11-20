use std::env;
use std::fs;
use std::path::PathBuf;
use clap::{Parser, Subcommand};
use miette::{WrapErr, IntoDiagnostic};

use codecrafters_interpreter::*;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    Tokenize { filename: PathBuf },
}

fn main() -> miette::Result<()>{
    let args = Args::parse();

    match args.command {
        Commands::Tokenize{ filename } => {
            let mut any_cc_err = false;
            let file_contents = fs::read_to_string(&filename)
            .into_diagnostic()
            .wrap_err_with(|| format!("reading file {} failed", filename.display()))?;

            for token in Lexer::new(&file_contents) {
                let token = match token {
                    Ok(t) => t,
                    Err(e) => {
                        eprintln!("{e:?}");
                        if let Some(unrecognized) = e.downcast_ref::<lexing::SingleTokenError>() {
                            any_cc_err = true;
                            eprintln!(
                                "[line {}] Error: Unexpected character: {}",
                                unrecognized.line(),
                                unrecognized.token
                            );
                        } else if let Some(unterminated) =
                            e.downcast_ref::<lexing::StringTerminationError>()
                        {
                            any_cc_err = true;
                            eprintln!("[line {}] Error: Unterminated string.", unterminated.line());
                        }
                        continue;
                    }
                };
                println!("{token}");
            }
            println!("EOF  null");
        }
    }
    Ok(())
}
