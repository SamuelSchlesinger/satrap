use std::fmt;
use std::io::Write;

use crate::Lit;

pub(crate) struct DratWriter {
    output: Option<Box<dyn Write + Send>>,
    line: Vec<u8>,
    error: Option<String>,
}

impl DratWriter {
    pub(crate) const fn disabled() -> Self {
        Self {
            output: None,
            line: Vec::new(),
            error: None,
        }
    }

    pub(crate) fn enable<W: Write + Send + 'static>(&mut self, output: W) {
        self.output = Some(Box::new(output));
        self.error = None;
    }

    pub(crate) fn add_clause(&mut self, clause: &[Lit]) {
        self.write_step(b"", clause);
    }

    /// Emits a `d` deletion step so checkers can drop the clause instead of
    /// carrying every deleted clause through the remaining proof.
    pub(crate) fn delete_clause(&mut self, clause: &[Lit]) {
        self.write_step(b"d ", clause);
    }

    fn write_step(&mut self, prefix: &[u8], clause: &[Lit]) {
        if self.output.is_none() || self.error.is_some() {
            return;
        }

        self.line.clear();
        self.line.extend_from_slice(prefix);
        for &literal in clause {
            push_i64(&mut self.line, literal.to_dimacs());
            self.line.push(b' ');
        }
        self.line.extend_from_slice(b"0\n");
        if let Err(error) = self
            .output
            .as_mut()
            .expect("output checked above")
            .write_all(&self.line)
        {
            self.error = Some(error.to_string());
        }
    }

    pub(crate) fn finish(&mut self) {
        if self.error.is_some() {
            return;
        }
        if let Some(output) = &mut self.output {
            if let Err(error) = output.flush() {
                self.error = Some(error.to_string());
            }
        }
    }

    pub(crate) fn error(&self) -> Option<&str> {
        self.error.as_deref()
    }
}

impl fmt::Debug for DratWriter {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("DratWriter")
            .field("enabled", &self.output.is_some())
            .field("error", &self.error)
            .finish_non_exhaustive()
    }
}

fn push_i64(output: &mut Vec<u8>, value: i64) {
    let negative = value < 0;
    let mut magnitude = value.unsigned_abs();
    if negative {
        output.push(b'-');
    }

    let start = output.len();
    loop {
        output.push(b'0' + (magnitude % 10) as u8);
        magnitude /= 10;
        if magnitude == 0 {
            break;
        }
    }
    output[start..].reverse();
}

#[cfg(test)]
mod tests {
    use super::{DratWriter, push_i64};
    use crate::{Lit, Var};

    #[test]
    fn writes_addition_and_deletion_steps() {
        #[derive(Clone)]
        struct SharedBuffer(std::sync::Arc<std::sync::Mutex<Vec<u8>>>);

        impl std::io::Write for SharedBuffer {
            fn write(&mut self, buffer: &[u8]) -> std::io::Result<usize> {
                self.0.lock().unwrap().extend_from_slice(buffer);
                Ok(buffer.len())
            }

            fn flush(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }

        let buffer = SharedBuffer(std::sync::Arc::default());
        let mut writer = DratWriter::disabled();
        writer.enable(buffer.clone());
        let a = Lit::positive(Var::new(0));
        let b = Lit::negative(Var::new(1));
        writer.add_clause(&[a, b]);
        writer.delete_clause(&[a, b]);
        writer.add_clause(&[]);
        writer.finish();
        assert_eq!(writer.error(), None);
        assert_eq!(
            String::from_utf8(buffer.0.lock().unwrap().clone()).unwrap(),
            "1 -2 0\nd 1 -2 0\n0\n"
        );
    }

    #[test]
    fn formats_signed_integers_without_allocation_per_number() {
        let mut output = Vec::new();
        for value in [0, 1, -1, 2_147_483_648, -2_147_483_648] {
            push_i64(&mut output, value);
            output.push(b' ');
        }
        assert_eq!(
            String::from_utf8(output).unwrap(),
            "0 1 -1 2147483648 -2147483648 "
        );
    }
}
