//! DIMACS CNF parsing.

use std::error::Error;
use std::fmt;

use crate::Lit;
use crate::types::MAX_VARIABLES;

/// An owned CNF formula parsed from DIMACS.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Formula {
    /// Number of variables declared by the `p cnf` header.
    pub variable_count: usize,
    /// Clauses in input order.
    pub clauses: Vec<Vec<Lit>>,
}

/// A DIMACS syntax or validation error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseError {
    line: usize,
    column: usize,
    message: String,
}

impl ParseError {
    /// One-based source line at which the error was detected.
    #[must_use]
    pub const fn line(&self) -> usize {
        self.line
    }

    /// One-based source column at which the error was detected.
    #[must_use]
    pub const fn column(&self) -> usize {
        self.column
    }

    fn at(token: Token<'_>, message: impl Into<String>) -> Self {
        Self {
            line: token.line,
            column: token.column,
            message: message.into(),
        }
    }

    fn eof(lexer: &Lexer<'_>, message: impl Into<String>) -> Self {
        Self {
            line: lexer.line,
            column: lexer.position.saturating_sub(lexer.line_start) + 1,
            message: message.into(),
        }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "DIMACS error at {}:{}: {}",
            self.line, self.column, self.message
        )
    }
}

impl Error for ParseError {}

/// Parses one DIMACS CNF formula.
///
/// A `c` token skips the rest of its line, and a line whose first token starts
/// with `c` is skipped entirely, so both `c comment` and `c=====` comment
/// styles found in benchmark corpora are accepted. A line whose first token
/// starts with `%` ends the input, accepting the SATLIB `%` trailer. Clauses
/// may span lines, but every clause must end in `0`, and the declared clause
/// count and variable bound are enforced.
pub fn parse(input: &[u8]) -> Result<Formula, ParseError> {
    let mut lexer = Lexer::new(input);

    let problem = next_required(&mut lexer, "expected `p cnf` header")?;
    expect_token(problem, b"p", "expected `p cnf` header")?;
    let format = next_required(&mut lexer, "expected `cnf` after `p`")?;
    expect_token(format, b"cnf", "expected `cnf` after `p`")?;

    let variables_token = next_required(&mut lexer, "expected variable count")?;
    let variable_count = parse_usize(variables_token, "variable count")?;
    if variable_count > MAX_VARIABLES {
        return Err(ParseError::at(
            variables_token,
            "variable count exceeds the solver's packed-literal limit",
        ));
    }

    let clauses_token = next_required(&mut lexer, "expected clause count")?;
    let expected_clauses = parse_usize(clauses_token, "clause count")?;
    let mut clauses = Vec::with_capacity(expected_clauses);
    let mut clause = Vec::new();

    while let Some(token) = lexer.next_token() {
        let value = parse_i64(token)?;
        if value == 0 {
            clauses.push(std::mem::take(&mut clause));
            if clauses.len() > expected_clauses {
                return Err(ParseError::at(
                    token,
                    format!("found more than the declared {expected_clauses} clauses"),
                ));
            }
            continue;
        }

        let magnitude = value.unsigned_abs();
        if magnitude == 0 || magnitude > variable_count as u64 {
            return Err(ParseError::at(
                token,
                format!("literal {value} exceeds the declared variable range 1..={variable_count}"),
            ));
        }
        clause
            .push(Lit::from_dimacs(value).ok_or_else(|| {
                ParseError::at(token, "literal exceeds the packed-literal range")
            })?);
    }

    if !clause.is_empty() {
        return Err(ParseError::eof(
            &lexer,
            "last clause is missing its terminating `0`",
        ));
    }
    if clauses.len() != expected_clauses {
        return Err(ParseError::eof(
            &lexer,
            format!(
                "header declares {expected_clauses} clauses, but input contains {}",
                clauses.len()
            ),
        ));
    }

    Ok(Formula {
        variable_count,
        clauses,
    })
}

fn next_required<'a>(
    lexer: &mut Lexer<'a>,
    message: &'static str,
) -> Result<Token<'a>, ParseError> {
    lexer
        .next_token()
        .ok_or_else(|| ParseError::eof(lexer, message))
}

fn expect_token(
    token: Token<'_>,
    expected: &[u8],
    message: &'static str,
) -> Result<(), ParseError> {
    if token.bytes == expected {
        Ok(())
    } else {
        Err(ParseError::at(token, message))
    }
}

fn parse_usize(token: Token<'_>, description: &'static str) -> Result<usize, ParseError> {
    let value = parse_u64(token)
        .map_err(|()| ParseError::at(token, format!("invalid nonnegative {description}")))?;
    usize::try_from(value)
        .map_err(|_| ParseError::at(token, format!("{description} does not fit in memory")))
}

fn parse_u64(token: Token<'_>) -> Result<u64, ()> {
    if token.bytes.is_empty() {
        return Err(());
    }
    let mut value = 0_u64;
    for &byte in token.bytes {
        if !byte.is_ascii_digit() {
            return Err(());
        }
        value = value
            .checked_mul(10)
            .and_then(|current| current.checked_add(u64::from(byte - b'0')))
            .ok_or(())?;
    }
    Ok(value)
}

fn parse_i64(token: Token<'_>) -> Result<i64, ParseError> {
    let (negative, digits) = match token.bytes {
        [b'-', rest @ ..] => (true, rest),
        [b'+', rest @ ..] => (false, rest),
        bytes => (false, bytes),
    };
    let magnitude = parse_u64(Token {
        bytes: digits,
        ..token
    })
    .map_err(|()| ParseError::at(token, "expected an integer literal or `0`"))?;

    if negative {
        if magnitude == (i64::MAX as u64) + 1 {
            Ok(i64::MIN)
        } else {
            let value = i64::try_from(magnitude)
                .map_err(|_| ParseError::at(token, "integer literal is out of range"))?;
            Ok(-value)
        }
    } else {
        i64::try_from(magnitude)
            .map_err(|_| ParseError::at(token, "integer literal is out of range"))
    }
}

#[derive(Clone, Copy)]
struct Token<'a> {
    bytes: &'a [u8],
    line: usize,
    column: usize,
}

struct Lexer<'a> {
    input: &'a [u8],
    position: usize,
    line: usize,
    line_start: usize,
}

impl<'a> Lexer<'a> {
    const fn new(input: &'a [u8]) -> Self {
        Self {
            input,
            position: 0,
            line: 1,
            line_start: 0,
        }
    }

    fn next_token(&mut self) -> Option<Token<'a>> {
        loop {
            self.skip_ascii_whitespace();
            if self.position == self.input.len() {
                return None;
            }

            let start = self.position;
            let line = self.line;
            let column = start - self.line_start + 1;
            while self.position < self.input.len()
                && !self.input[self.position].is_ascii_whitespace()
            {
                self.position += 1;
            }

            let bytes = &self.input[start..self.position];
            // No valid DIMACS token starts a line with `c` or `%`: `p` leads
            // the header, `cnf` never begins a line, and literals are signed
            // integers. Treating them as a comment and an end-of-input trailer
            // accepts the `c=====` and SATLIB `%` styles common in corpora.
            if bytes == b"c" || (column == 1 && bytes[0] == b'c') {
                self.skip_to_next_line();
                continue;
            }
            if column == 1 && bytes[0] == b'%' {
                self.position = self.input.len();
                return None;
            }
            return Some(Token {
                bytes,
                line,
                column,
            });
        }
    }

    fn skip_ascii_whitespace(&mut self) {
        while self.position < self.input.len() && self.input[self.position].is_ascii_whitespace() {
            if self.input[self.position] == b'\n' {
                self.line += 1;
                self.line_start = self.position + 1;
            }
            self.position += 1;
        }
    }

    fn skip_to_next_line(&mut self) {
        while self.position < self.input.len() {
            let byte = self.input[self.position];
            self.position += 1;
            if byte == b'\n' {
                self.line += 1;
                self.line_start = self.position;
                break;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::parse;

    #[test]
    fn parses_comments_wrapped_clauses_and_empty_clauses() {
        let input = b"c heading\n p cnf 3 3\n1 -2\n3 0 c tail\n2 0\n0\n";
        let formula = parse(input).unwrap();
        assert_eq!(formula.variable_count, 3);
        assert_eq!(formula.clauses.len(), 3);
        assert_eq!(
            formula.clauses[0]
                .iter()
                .map(|literal| literal.to_dimacs())
                .collect::<Vec<_>>(),
            [1, -2, 3]
        );
        assert!(formula.clauses[2].is_empty());
    }

    #[test]
    fn parses_fused_comment_lines_and_satlib_trailer() {
        let input = b"c heading\nc=====\np cnf 3 2\n1 -2 0\n2 3 0\n%\n0\n";
        let formula = parse(input).unwrap();
        assert_eq!(formula.variable_count, 3);
        assert_eq!(formula.clauses.len(), 2);

        // A fused comment token is only recognized at the start of a line, so
        // it can never swallow the `cnf` header keyword.
        assert!(parse(b"p cnf 1 1\nc1 0\n").is_err());
        assert!(parse(b"p cnf 1 1\n1 %\n").is_err());
    }

    #[test]
    fn rejects_count_mismatches_and_missing_terminator() {
        let error = parse(b"p cnf 2 2\n1 0\n").unwrap_err();
        assert!(error.to_string().contains("declares 2 clauses"));

        let error = parse(b"p cnf 2 1\n1 -2\n").unwrap_err();
        assert!(error.to_string().contains("missing its terminating"));
    }

    #[test]
    fn rejects_literals_outside_declared_range() {
        let error = parse(b"p cnf 2 1\n3 0\n").unwrap_err();
        assert_eq!(error.line(), 2);
        assert_eq!(error.column(), 1);
        assert!(error.to_string().contains("declared variable range"));
    }

    #[test]
    fn rejects_malformed_header_and_tokens() {
        assert!(parse(b"p sat 1 0\n").is_err());
        assert!(parse(b"p cnf -1 0\n").is_err());
        assert!(parse(b"p cnf 1 1\nx 0\n").is_err());
    }
}
