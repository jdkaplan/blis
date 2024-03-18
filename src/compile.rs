use crate::bytecode::{Chunk, Constant, Op};
use crate::parse::*;

pub struct Compiler;

pub type CompileResult<T> = Result<T, CompileError>;

#[derive(thiserror::Error, Debug)]
#[error("compile error")]
pub struct CompileError;

impl Compiler {
    pub fn compile(file: &File) -> CompileResult<Chunk> {
        let mut constants = Vec::new();
        let mut code = Vec::new();

        for decl in &file.decls {
            let Decl::Stmt(Stmt::Expr(Expr::Literal(Literal::U64(value)))) = decl;

            let idx = constants.len();
            assert!(idx < u8::MAX.into());
            let idx = idx as u8;

            constants.push(Constant::U64(*value));

            code.extend(Op::Constant(idx).to_bytes());
            code.extend(Op::Return.to_bytes());
        }

        Ok(Chunk {
            name: file.name.clone(),
            constants,
            code,
        })
    }
}
