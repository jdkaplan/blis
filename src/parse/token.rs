#[derive(Debug, Copy, Clone, Default)]
pub struct Lexeme<'source> {
    pub token: Token,
    pub text: &'source str,
    pub line: usize,
}

#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, Hash)]
pub enum Token {
    // Single-character tokens
    LeftParen,
    RightParen,
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
    Or,
    Return,
    True,

    // Synthetic tokens
    #[default]
    Error,
    Eof,
}
