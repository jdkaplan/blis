use serde::Serialize;

#[derive(Debug, Copy, Clone, Default, Serialize)]
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

#[derive(Debug, Clone, Default, Serialize)]
pub struct LexemeOwned {
    pub token: Token,
    pub text: String,
    pub line: usize,
}

#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, Hash, Serialize)]
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
    Or,
    Return,
    Self_,
    True,
    Type,
    With,

    // Synthetic tokens
    #[default]
    Eof,
    ErrorUnterminatedString,
    ErrorUnrecognizedCharacter,
}

impl Token {
    pub fn is_error(&self) -> bool {
        matches!(
            self,
            Token::ErrorUnterminatedString | Token::ErrorUnrecognizedCharacter
        )
    }

    pub fn match_keyword(text: &str) -> Option<Self> {
        match text {
            "and" => Some(Token::And),
            "break" => Some(Token::Break),
            "continue" => Some(Token::Continue),
            "else" => Some(Token::Else),
            "false" => Some(Token::False),
            "func" => Some(Token::Func),
            "if" => Some(Token::If),
            "let" => Some(Token::Let),
            "loop" => Some(Token::Loop),
            "nil" => Some(Token::Nil),
            "or" => Some(Token::Or),
            "return" => Some(Token::Return),
            "self" => Some(Token::Self_),
            "true" => Some(Token::True),
            "type" => Some(Token::Type),
            "with" => Some(Token::With),
            _ => None,
        }
    }
}
