use std::path::Path;

pub type ParseResult<T> = Result<T, (Option<T>, ParseErrors)>;

pub type ParseErrors = Vec<ParseError>;

#[derive(thiserror::Error, Debug)]
#[error("parse error")]
pub struct ParseError;

pub struct File {
    pub name: String,
    pub decls: Vec<Decl>,
}

pub enum Decl {
    Stmt(Stmt),
}

pub enum Stmt {
    Expr(Expr),
}

pub enum Expr {
    Literal(Literal),
}

pub enum Literal {
    U64(u64),
}

pub struct Parser;

impl Parser {
    pub fn parse(path: &Path, source: &str) -> ParseResult<File> {
        let mut errors = Vec::new();
        let mut decls = Vec::new();

        if source.trim() == "1" {
            let decl = Decl::Stmt(Stmt::Expr(Expr::Literal(Literal::U64(1))));
            decls.push(decl);
        } else {
            errors.push(ParseError);
        }

        let file = File {
            name: path.to_string_lossy().into(),
            decls,
        };

        if errors.is_empty() {
            Ok(file)
        } else {
            Err((Some(file), errors))
        }
    }
}
