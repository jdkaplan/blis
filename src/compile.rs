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

type Fallible<T> = Result<T, FailedCodegen>;
struct FailedCodegen;

impl Compiler {
    fn new() -> Self {
        Self {
            chunk: Chunk::default(),
            errors: Vec::new(),
        }
    }

    pub fn compile(program: &Program) -> Result<Chunk, CompileErrors> {
        let mut compiler = Self::new();
        let _ = compiler.program(program); // Errors checked below

        if compiler.errors.is_empty() {
            Ok(compiler.chunk)
        } else {
            Err(CompileErrors(compiler.errors))
        }
    }

    fn program(&mut self, program: &Program) -> Fallible<()> {
        for decl in &program.decls {
            self.declaration(decl)?;
        }
        self.chunk.push(Op::Return);
        Ok(())
    }

    fn block(&mut self, block: &Block) -> Fallible<()> {
        for decl in &block.decls {
            self.declaration(decl)?;
        }
        self.chunk.push(Op::Nil); // TODO: Use trailing expr value instead
        Ok(())
    }

    fn declaration(&mut self, decl: &Declaration) -> Fallible<()> {
        let Declaration::Statement(stmt) = decl;
        self.statement(stmt)
    }

    fn statement(&mut self, stmt: &Statement) -> Fallible<()> {
        let Statement::Expression(expr) = stmt;
        self.expression(expr)?;

        self.chunk.push(Op::Pop);
        Ok(())
    }

    fn expression(&mut self, expr: &Expression) -> Fallible<()> {
        match expr {
            Expression::If(if_) => self.expr_if(if_),
            Expression::Literal(lit) => self.literal(lit),
        }
    }

    fn expr_if(&mut self, if_: &If) -> Fallible<()> {
        // <cond>
        self.expression(&if_.condition)?;

        // jump_false_pop 'skip_conseq [peek cond]
        let skip_conseq = self.chunk.prepare_jump(Op::JumpFalsePop(i16::MAX));

        // <consequent>
        self.block(&if_.consequent)?;

        let Some(alt) = &if_.alternative else {
            // 'skip_conseq:
            self.chunk.set_jump_target(skip_conseq);
            return Ok(());
        };

        // jump 'skip_alt
        let skip_alt = self.chunk.prepare_jump(Op::Jump(i16::MAX));

        // 'skip_conseq:
        self.chunk.set_jump_target(skip_conseq);

        // <alternative>
        self.block(alt)?;

        // 'skip_alt:
        self.chunk.set_jump_target(skip_alt);

        Ok(())
    }

    fn literal(&mut self, lit: &Literal) -> Fallible<()> {
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

        Ok(())
    }
}
