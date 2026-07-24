#![no_main]

use std::io::{BufReader, Cursor};

use libfuzzer_sys::fuzz_target;
use sat::smt;

fuzz_target!(|data: &[u8]| {
    if data.len() > 64 * 1024 {
        return;
    }
    let mut output = Vec::new();
    let _ = smt::run(BufReader::new(Cursor::new(data)), &mut output);
});
