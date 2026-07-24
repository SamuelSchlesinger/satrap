use std::io::{BufRead, BufReader, Write};
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

#[test]
fn responds_and_flushes_before_reading_the_next_command() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_smt"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("SMT executable should start");
    let mut input = child.stdin.take().expect("piped stdin");
    let output = child.stdout.take().expect("piped stdout");

    writeln!(input, "(echo \"ready\")").unwrap();
    input.flush().unwrap();

    let (sender, receiver) = mpsc::channel();
    thread::spawn(move || {
        let mut reader = BufReader::new(output);
        let mut line = String::new();
        let result = reader.read_line(&mut line).map(|_| line);
        sender.send(result).ok();
    });

    let line = match receiver.recv_timeout(Duration::from_secs(2)) {
        Ok(result) => result.expect("response should be readable"),
        Err(error) => {
            child.kill().ok();
            child.wait().ok();
            panic!("solver did not flush its response while stdin remained open: {error}");
        }
    };
    assert_eq!(line, "\"ready\"\n");

    writeln!(input, "(exit)").unwrap();
    drop(input);
    assert!(child.wait().expect("solver should exit").success());
}

#[test]
fn core_boolean_protocol_has_standard_model_shape_and_continues_after_errors() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_smt"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("SMT executable should start");
    let mut input = child.stdin.take().expect("piped stdin");
    write!(
        input,
        "(set-option :produce-models true)
         (set-logic QF_BOOL)
         (declare-const p Bool)
         (push 1)
         (declare-const p Bool)
         (check-sat)
         (get-model)
         (exit)"
    )
    .unwrap();
    drop(input);

    let output = child.wait_with_output().expect("solver should finish");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.starts_with("(error \"symbol `p` is already defined\")\nsat\n"));
    assert!(stdout.contains("(\n  (define-fun p () Bool false)\n)\n"));
    assert!(!stdout.contains("(model"));
}
