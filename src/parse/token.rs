#[derive(Debug, Copy, Clone, Default)]
pub struct Lexeme<'source> {
    pub token: Token,
    pub text: &'source str,
    pub line: usize,
}

impl Lexeme<'_> {
    pub fn to_owned(&self) -> LexemeOwned {
        LexemeOwned {
            token: self.token,
            text: String::from(self.text),
            line: self.line,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct LexemeOwned {
    pub token: Token,
    pub text: String,
    pub line: usize,
}

#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, Hash)]
pub enum Token {
    // Single-character tokens
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Slash,
    Star,
    Percent,

    // One- or two-character tokens
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    // Literals
    Identifier,
    String,
    Integer,
    Float,

    // Keywords
    And,
    Break,
    Continue,
    Else,
    False,
    Func,
    If,
    Let,
    Loop,
    Nil,
    Object,
    Or,
    Return,
    True,

    // Synthetic tokens
    #[default]
    Error,
    Eof,
}
