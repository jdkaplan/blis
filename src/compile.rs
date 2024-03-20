use crate::bytecode::{Chunk, Constant, Op};
use crate::parse::ast::*;

pub struct Compiler {
    chunk: Chunk,
    errors: Vec<CompileError>,
}

#[derive(thiserror::Error, Debug)]
pub struct CompileErrors(Vec<CompileError>);

impl std::fmt::Display for CompileErrors {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(err) = self.0.first() {
            write!(f, "{}", err)?;
        } else {
            return write!(f, "");
        }

        for err in &self.0[1..] {
            write!(f, "\n{}", err)?;
        }
        Ok(())
    }
}

#[derive(thiserror::Error, Debug)]
pub enum CompileError {
    #[error("{0}")]
    Other(String),
}

impl Compiler {
    fn new() -> Self {
        Self {
            chunk: Chunk::default(),
            errors: Vec::new(),
        }
    }

    pub fn compile(program: &Program) -> Result<Chunk, CompileErrors> {
        let mut compiler = Self::new();
        compiler.program(program);

        if compiler.errors.is_empty() {
            Ok(compiler.chunk)
        } else {
            Err(CompileErrors(compiler.errors))
        }
    }

    fn program(&mut self, program: &Program) {
        for decl in &program.decls {
            self.declaration(decl);
        }
        self.chunk.push(Op::Return);
    }

    fn declaration(&mut self, decl: &Declaration) {
        let Declaration::Statement(stmt) = decl;
        self.statement(stmt);
    }

    fn statement(&mut self, stmt: &Statement) {
        let Statement::Expression(expr) = stmt;
        self.expression(expr);
        self.chunk.push(Op::Pop);
    }

    fn expression(&mut self, expr: &Expression) {
        let Expression::Literal(lit) = expr;
        self.literal(lit);
    }

    fn literal(&mut self, lit: &Literal) {
        match lit {
            Literal::Nil => {
                self.chunk.push(Op::Nil);
            }
            Literal::Boolean(b) => {
                if *b {
                    self.chunk.push(Op::True);
                } else {
                    self.chunk.push(Op::False);
                }
            }

            Literal::Integer(v) => {
                let id = self.chunk.add_constant(Constant::Integer(*v));
                self.chunk.push(Op::Constant(id));
            }
            Literal::Float(v) => {
                let id = self.chunk.add_constant(Constant::Float(*v));
                self.chunk.push(Op::Constant(id));
            }
            Literal::String(v) => {
                let id = self.chunk.add_constant(Constant::String(v.clone()));
                self.chunk.push(Op::Constant(id));
            }
        }
    }
}
