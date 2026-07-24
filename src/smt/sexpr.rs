use std::error::Error;
use std::fmt;
use std::io::BufRead;

const MAX_NESTING: usize = 10_000;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SExpr {
    Atom(Atom),
    List(Vec<SExpr>),
}

impl SExpr {
    pub(crate) fn symbol(&self) -> Option<&str> {
        let Self::Atom(atom) = self else {
            return None;
        };
        (atom.kind == AtomKind::Symbol).then_some(atom.text.as_str())
    }

    pub(crate) fn word(&self) -> Option<&str> {
        let Self::Atom(atom) = self else {
            return None;
        };
        matches!(atom.kind, AtomKind::Symbol | AtomKind::Reserved).then_some(atom.text.as_str())
    }

    pub(crate) fn keyword(&self) -> Option<&str> {
        let Self::Atom(atom) = self else {
            return None;
        };
        (atom.kind == AtomKind::Keyword).then_some(atom.text.as_str())
    }

    pub(crate) fn string(&self) -> Option<&str> {
        let Self::Atom(atom) = self else {
            return None;
        };
        (atom.kind == AtomKind::String).then_some(atom.text.as_str())
    }

    pub(crate) fn numeral(&self) -> Option<&str> {
        let Self::Atom(atom) = self else {
            return None;
        };
        (atom.kind == AtomKind::Numeral).then_some(atom.text.as_str())
    }

    pub(crate) fn decimal(&self) -> Option<&str> {
        let Self::Atom(atom) = self else {
            return None;
        };
        (atom.kind == AtomKind::Decimal).then_some(atom.text.as_str())
    }

    pub(crate) fn binary(&self) -> Option<&str> {
        let Self::Atom(atom) = self else {
            return None;
        };
        (atom.kind == AtomKind::Binary).then_some(atom.text.as_str())
    }

    pub(crate) fn hexadecimal(&self) -> Option<&str> {
        let Self::Atom(atom) = self else {
            return None;
        };
        (atom.kind == AtomKind::Hexadecimal).then_some(atom.text.as_str())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Atom {
    pub(crate) text: String,
    pub(crate) kind: AtomKind,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum AtomKind {
    Symbol,
    Reserved,
    Keyword,
    Numeral,
    Decimal,
    Hexadecimal,
    Binary,
    String,
}

#[derive(Debug)]
pub(crate) struct ParseError {
    line: usize,
    column: usize,
    message: String,
    recoverable: bool,
}

impl ParseError {
    fn new(line: usize, column: usize, message: impl Into<String>) -> Self {
        Self {
            line,
            column,
            message: message.into(),
            recoverable: true,
        }
    }

    fn input(line: usize, column: usize, message: impl Into<String>) -> Self {
        Self {
            line,
            column,
            message: message.into(),
            recoverable: false,
        }
    }

    pub(crate) fn is_recoverable(&self) -> bool {
        self.recoverable
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "SMT-LIB parse error at {}:{}: {}",
            self.line, self.column, self.message
        )
    }
}

impl Error for ParseError {}

pub(crate) struct Reader<R> {
    input: R,
    lookahead: Option<u8>,
    line: usize,
    column: usize,
    open_lists: usize,
    // Recovery is deferred until `next` so the caller can flush the error
    // response before waiting for the rest of an interactive command.
    recovery: Option<Recovery>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Recovery {
    List,
    String,
    QuotedSymbol,
    UnexpectedClose,
}

impl<R: BufRead> Reader<R> {
    pub(crate) fn new(input: R) -> Self {
        Self {
            input,
            lookahead: None,
            line: 1,
            column: 1,
            open_lists: 0,
            recovery: None,
        }
    }

    pub(crate) fn next(&mut self) -> Result<Option<SExpr>, ParseError> {
        self.recover_pending()?;
        self.skip_trivia()?;
        if self.peek()?.is_none() {
            return Ok(None);
        }
        match self.parse_expr(0) {
            Ok(expression) => Ok(Some(expression)),
            Err(error) => {
                if error.is_recoverable() && self.recovery.is_none() && self.open_lists > 0 {
                    self.recovery = Some(Recovery::List);
                }
                Err(error)
            }
        }
    }

    fn parse_expr(&mut self, depth: usize) -> Result<SExpr, ParseError> {
        if depth > MAX_NESTING {
            return Err(self.error("maximum S-expression nesting exceeded"));
        }
        match self.peek()? {
            Some(b'(') => {
                self.bump()?;
                self.open_lists += 1;
                let mut items = Vec::new();
                loop {
                    self.skip_trivia()?;
                    match self.peek()? {
                        Some(b')') => {
                            self.bump()?;
                            self.open_lists -= 1;
                            return Ok(SExpr::List(items));
                        }
                        None => return Err(self.error("unterminated list")),
                        _ => items.push(self.parse_expr(depth + 1)?),
                    }
                }
            }
            Some(b')') => {
                self.recovery = Some(Recovery::UnexpectedClose);
                Err(self.error("unexpected `)`"))
            }
            Some(b'"') => self.parse_string(),
            Some(b'|') => self.parse_quoted_symbol(),
            Some(_) => self.parse_atom(),
            None => Err(self.error("expected an S-expression")),
        }
    }

    fn parse_string(&mut self) -> Result<SExpr, ParseError> {
        self.bump()?;
        let mut bytes = Vec::new();
        loop {
            match self.bump()? {
                Some(b'"') => {
                    if self.peek()? == Some(b'"') {
                        self.bump()?;
                        bytes.push(b'"');
                    } else {
                        let text = String::from_utf8(bytes)
                            .map_err(|_| self.error("string literal is not valid UTF-8"))?;
                        return Ok(SExpr::Atom(Atom {
                            text,
                            kind: AtomKind::String,
                        }));
                    }
                }
                Some(byte) if is_printable_or_whitespace(byte) => bytes.push(byte),
                Some(_) => {
                    self.recovery = Some(Recovery::String);
                    return Err(self.error("invalid character in string literal"));
                }
                None => {
                    self.recovery = Some(Recovery::String);
                    return Err(self.error("unterminated string literal"));
                }
            }
        }
    }

    fn parse_quoted_symbol(&mut self) -> Result<SExpr, ParseError> {
        self.bump()?;
        let mut bytes = Vec::new();
        loop {
            match self.bump()? {
                Some(b'|') => {
                    let text = String::from_utf8(bytes)
                        .map_err(|_| self.error("quoted symbol is not valid UTF-8"))?;
                    return Ok(SExpr::Atom(Atom {
                        text,
                        kind: AtomKind::Symbol,
                    }));
                }
                Some(b'\\') => {
                    self.recovery = Some(Recovery::QuotedSymbol);
                    return Err(self.error("backslash is not allowed in a quoted symbol"));
                }
                Some(byte) if is_printable_or_whitespace(byte) => bytes.push(byte),
                Some(_) => {
                    self.recovery = Some(Recovery::QuotedSymbol);
                    return Err(self.error("invalid character in quoted symbol"));
                }
                None => {
                    self.recovery = Some(Recovery::QuotedSymbol);
                    return Err(self.error("unterminated quoted symbol"));
                }
            }
        }
    }

    fn parse_atom(&mut self) -> Result<SExpr, ParseError> {
        let mut bytes = Vec::new();
        while let Some(byte) = self.peek()? {
            if is_whitespace(byte) || matches!(byte, b'(' | b')' | b';') {
                break;
            }
            bytes.push(self.bump()?.expect("peeked byte must remain available"));
        }
        if bytes.is_empty() {
            return Err(self.error("expected an atom"));
        }
        let text = String::from_utf8(bytes)
            .map_err(|_| self.error("only UTF-8 SMT-LIB input is supported"))?;
        let kind = if is_numeral(&text) {
            AtomKind::Numeral
        } else if is_decimal(&text) {
            AtomKind::Decimal
        } else if text.strip_prefix("#x").is_some_and(|digits| {
            !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_hexdigit())
        }) {
            AtomKind::Hexadecimal
        } else if text.strip_prefix("#b").is_some_and(|digits| {
            !digits.is_empty() && digits.bytes().all(|byte| matches!(byte, b'0' | b'1'))
        }) {
            AtomKind::Binary
        } else if let Some(keyword) = text.strip_prefix(':') {
            if keyword.is_empty() || !keyword.bytes().all(is_symbol_byte) {
                return Err(self.error("invalid keyword"));
            }
            AtomKind::Keyword
        } else if is_reserved_word(&text) {
            AtomKind::Reserved
        } else if is_simple_symbol(&text) {
            AtomKind::Symbol
        } else {
            return Err(self.error(format!("invalid SMT-LIB token `{text}`")));
        };
        Ok(SExpr::Atom(Atom { text, kind }))
    }

    fn skip_trivia(&mut self) -> Result<(), ParseError> {
        loop {
            while self.peek()?.is_some_and(is_whitespace) {
                self.bump()?;
            }
            if self.peek()? != Some(b';') {
                return Ok(());
            }
            while let Some(byte) = self.bump()? {
                if byte == b'\n' {
                    break;
                }
            }
        }
    }

    fn peek(&mut self) -> Result<Option<u8>, ParseError> {
        if self.lookahead.is_none() {
            let buffer = match self.input.fill_buf() {
                Ok(buffer) => buffer,
                Err(error) => {
                    return Err(ParseError::input(
                        self.line,
                        self.column,
                        format!("input error: {error}"),
                    ));
                }
            };
            if let Some(&byte) = buffer.first() {
                self.lookahead = Some(byte);
                self.input.consume(1);
            }
        }
        Ok(self.lookahead)
    }

    fn bump(&mut self) -> Result<Option<u8>, ParseError> {
        let byte = self.peek()?;
        self.lookahead = None;
        if byte == Some(b'\n') {
            self.line += 1;
            self.column = 1;
        } else if byte.is_some() {
            self.column += 1;
        }
        Ok(byte)
    }

    fn error(&self, message: impl Into<String>) -> ParseError {
        ParseError::new(self.line, self.column, message)
    }

    fn recover_pending(&mut self) -> Result<(), ParseError> {
        let Some(recovery) = self.recovery.take() else {
            return Ok(());
        };
        match recovery {
            Recovery::String => self.skip_string_remainder()?,
            Recovery::QuotedSymbol => self.skip_quoted_symbol_remainder()?,
            Recovery::UnexpectedClose => {
                self.bump()?;
            }
            Recovery::List => {}
        }
        self.skip_open_lists()
    }

    fn skip_string_remainder(&mut self) -> Result<(), ParseError> {
        while let Some(byte) = self.bump()? {
            if byte != b'"' {
                continue;
            }
            if self.peek()? == Some(b'"') {
                self.bump()?;
            } else {
                break;
            }
        }
        Ok(())
    }

    fn skip_quoted_symbol_remainder(&mut self) -> Result<(), ParseError> {
        while let Some(byte) = self.bump()? {
            if byte == b'|' {
                break;
            }
        }
        Ok(())
    }

    fn skip_open_lists(&mut self) -> Result<(), ParseError> {
        while self.open_lists > 0 {
            let Some(byte) = self.bump()? else {
                self.open_lists = 0;
                break;
            };
            match byte {
                b'(' => self.open_lists += 1,
                b')' => self.open_lists -= 1,
                b'"' => self.skip_string_remainder()?,
                b'|' => self.skip_quoted_symbol_remainder()?,
                b';' => {
                    while let Some(byte) = self.bump()? {
                        if byte == b'\n' {
                            break;
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }
}

fn is_whitespace(byte: u8) -> bool {
    matches!(byte, b'\t' | b'\n' | b'\r' | b' ')
}

fn is_printable_or_whitespace(byte: u8) -> bool {
    is_whitespace(byte) || matches!(byte, b' '..=b'~' | 128..=u8::MAX)
}

fn is_symbol_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric()
        || matches!(
            byte,
            b'~' | b'!'
                | b'@'
                | b'$'
                | b'%'
                | b'^'
                | b'&'
                | b'*'
                | b'_'
                | b'-'
                | b'+'
                | b'='
                | b'<'
                | b'>'
                | b'.'
                | b'?'
                | b'/'
        )
}

fn is_simple_symbol(text: &str) -> bool {
    !text.is_empty() && !text.as_bytes()[0].is_ascii_digit() && text.bytes().all(is_symbol_byte)
}

fn is_numeral(text: &str) -> bool {
    text == "0"
        || (text
            .as_bytes()
            .first()
            .is_some_and(|byte| matches!(byte, b'1'..=b'9'))
            && text.bytes().all(|byte| byte.is_ascii_digit()))
}

fn is_decimal(text: &str) -> bool {
    let Some((integer, fractional)) = text.split_once('.') else {
        return false;
    };
    !fractional.is_empty()
        && is_numeral(integer)
        && fractional.bytes().all(|byte| byte.is_ascii_digit())
}

pub(crate) fn is_reserved_word(text: &str) -> bool {
    matches!(
        text,
        "BINARY"
            | "DECIMAL"
            | "HEXADECIMAL"
            | "NUMERAL"
            | "STRING"
            | "_"
            | "!"
            | "as"
            | "lambda"
            | "let"
            | "exists"
            | "forall"
            | "match"
            | "par"
            | "assert"
            | "check-sat"
            | "check-sat-assuming"
            | "declare-const"
            | "declare-datatype"
            | "declare-datatypes"
            | "declare-fun"
            | "declare-sort"
            | "declare-sort-parameter"
            | "define-const"
            | "define-fun"
            | "define-fun-rec"
            | "define-funs-rec"
            | "define-sort"
            | "echo"
            | "exit"
            | "get-assertions"
            | "get-assignment"
            | "get-info"
            | "get-model"
            | "get-option"
            | "get-proof"
            | "get-unsat-assumptions"
            | "get-unsat-core"
            | "get-value"
            | "pop"
            | "push"
            | "reset"
            | "reset-assertions"
            | "set-info"
            | "set-logic"
            | "set-option"
    )
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use super::{Atom, AtomKind, Reader, SExpr};

    #[test]
    fn reads_one_top_level_expression_at_a_time() {
        let input = b"; heading\n(set-logic QF_UF)\n(assert (or p |q q|))";
        let mut reader = Reader::new(Cursor::new(input));
        assert_eq!(
            reader.next().unwrap(),
            Some(SExpr::List(vec![
                SExpr::Atom(Atom {
                    text: "set-logic".into(),
                    kind: AtomKind::Reserved,
                }),
                SExpr::Atom(Atom {
                    text: "QF_UF".into(),
                    kind: AtomKind::Symbol,
                }),
            ]))
        );
        assert!(matches!(reader.next().unwrap(), Some(SExpr::List(_))));
        assert_eq!(reader.next().unwrap(), None);
    }

    #[test]
    fn decodes_doubled_quotes_without_consuming_the_next_command() {
        let mut reader = Reader::new(Cursor::new(b"(echo \"a\"\"b\")(exit)"));
        let Some(SExpr::List(echo)) = reader.next().unwrap() else {
            panic!("expected echo command");
        };
        assert_eq!(echo[1].string(), Some("a\"b"));
        assert!(matches!(reader.next().unwrap(), Some(SExpr::List(_))));
    }

    #[test]
    fn rejects_unbalanced_input() {
        let mut reader = Reader::new(Cursor::new(b"(assert true"));
        assert!(
            reader
                .next()
                .unwrap_err()
                .to_string()
                .contains("unterminated")
        );
        assert_eq!(reader.next().unwrap(), None);
    }

    #[test]
    fn recovers_after_a_malformed_nested_token() {
        let mut reader = Reader::new(Cursor::new(
            b"(assert (and true #b012 (or false true))) (echo \"recovered\")",
        ));
        assert!(
            reader
                .next()
                .unwrap_err()
                .to_string()
                .contains("invalid SMT-LIB token `#b012`")
        );
        let Some(SExpr::List(echo)) = reader.next().unwrap() else {
            panic!("expected the command after the malformed expression");
        };
        assert_eq!(echo[0].word(), Some("echo"));
        assert_eq!(echo[1].string(), Some("recovered"));
        assert_eq!(reader.next().unwrap(), None);
    }

    #[test]
    fn recovery_respects_strings_comments_and_quoted_symbols() {
        let input = b"(assert (= |bad\\name| (f \")\" ; ignored )\n |(|))) (exit)";
        let mut reader = Reader::new(Cursor::new(input));
        assert!(
            reader
                .next()
                .unwrap_err()
                .to_string()
                .contains("backslash is not allowed")
        );
        let Some(SExpr::List(exit)) = reader.next().unwrap() else {
            panic!("expected exit after malformed quoted symbol");
        };
        assert_eq!(exit[0].word(), Some("exit"));
        assert_eq!(reader.next().unwrap(), None);
    }

    #[test]
    fn recovers_from_inside_an_invalid_string() {
        let mut input = b"(echo \"bad".to_vec();
        input.push(0);
        input.extend_from_slice(b"tail\") (exit)");
        let mut reader = Reader::new(Cursor::new(input));
        assert!(
            reader
                .next()
                .unwrap_err()
                .to_string()
                .contains("invalid character in string literal")
        );
        let Some(SExpr::List(exit)) = reader.next().unwrap() else {
            panic!("expected exit after invalid string");
        };
        assert_eq!(exit[0].word(), Some("exit"));
    }

    #[test]
    fn consumes_an_unexpected_top_level_close_before_continuing() {
        let mut reader = Reader::new(Cursor::new(b") (exit)"));
        assert!(
            reader
                .next()
                .unwrap_err()
                .to_string()
                .contains("unexpected")
        );
        let Some(SExpr::List(exit)) = reader.next().unwrap() else {
            panic!("expected exit after unexpected close");
        };
        assert_eq!(exit[0].word(), Some("exit"));
    }

    #[test]
    fn preserves_utf8_in_strings_and_quoted_symbols() {
        let mut reader = Reader::new(Cursor::new(
            "(echo \"Grüß dich λ\") (assert |wahr λ|)".as_bytes(),
        ));
        let Some(SExpr::List(echo)) = reader.next().unwrap() else {
            panic!("expected echo command");
        };
        assert_eq!(echo[1].string(), Some("Grüß dich λ"));
        let Some(SExpr::List(assertion)) = reader.next().unwrap() else {
            panic!("expected assertion command");
        };
        assert_eq!(assertion[1].symbol(), Some("wahr λ"));
    }

    #[test]
    fn classifies_constants_and_rejects_invalid_tokens() {
        let mut reader = Reader::new(Cursor::new(b"(#b010 #xA0 17 1.50)"));
        let Some(SExpr::List(items)) = reader.next().unwrap() else {
            panic!("expected constant list");
        };
        assert_eq!(items[0].binary(), Some("#b010"));
        assert_eq!(items[1].hexadecimal(), Some("#xA0"));
        assert_eq!(items[2].numeral(), Some("17"));

        for invalid in [
            b"00".as_slice(),
            b"abc\"def".as_slice(),
            b"#b012".as_slice(),
        ] {
            let mut reader = Reader::new(Cursor::new(invalid));
            assert!(reader.next().is_err(), "{invalid:?} should be rejected");
        }
    }
}
