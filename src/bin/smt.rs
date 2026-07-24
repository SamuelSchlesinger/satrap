use std::io::{self, BufReader, BufWriter};
use std::process::ExitCode;

fn main() -> ExitCode {
    let stdin = io::stdin();
    let stdout = io::stdout();
    let input = BufReader::new(stdin.lock());
    let output = BufWriter::new(stdout.lock());

    if let Err(error) = sat::smt::run(input, output) {
        eprintln!("{error}");
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
