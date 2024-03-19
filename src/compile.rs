use crate::bytecode::{Chunk, Constant, Op};
use crate::parse::*;

pub struct Compiler;

pub type CompileResult<T> = Result<T, CompileError>;

#[derive(thiserror::Error, Debug)]
#[error("compile error")]
pub struct CompileError;

impl Compiler {
    pub fn compile(file: &Program) -> CompileResult<Chunk> {
        let mut constants = Vec::new();
        let mut code = Vec::new();

        for decl in &file.decls {
            let Declaration::Statement(Statement::Expression(Expression::Literal(literal))) = decl;

            let constant = match literal {
                Literal::Integer(int) => Constant::Integer(*int),
                Literal::Float(float) => Constant::Float(*float),
                Literal::String(string) => Constant::String(string.clone()),
            };

            let idx = constants.len();
            assert!(idx < u8::MAX.into());
            let idx = idx as u8;

            constants.push(constant);

            code.extend(Op::Constant(idx).to_bytes());
            code.extend(Op::Return.to_bytes());
        }

        Ok(Chunk { constants, code })
    }
}
