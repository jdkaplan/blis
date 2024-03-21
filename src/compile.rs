use crate::bytecode::{Chunk, Constant, Op};
use crate::parse::ast::*;

pub struct Compiler {
    chunk: Chunk,
    errors: Vec<CompileError>,

    locals: Locals,
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
    #[error(
        "variable redeclared in the same scope: `{}`",
        .0.name
    )]
    DuplicateVariable(Identifier),

    #[error("{0}")]
    Other(String),
}

type CompileResult<T> = Result<T, CompileError>;

type Fallible<T> = Result<T, FailedCodegen>;
struct FailedCodegen;

impl Compiler {
    fn new() -> Self {
        Self {
            chunk: Chunk::default(),
            errors: Vec::new(),
            locals: Locals::default(),
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
        self.locals.begin_scope();

        for decl in &block.decls {
            self.declaration(decl)?;
        }

        if let Some(expr) = &block.expr {
            self.expression(expr)?;
        } else {
            self.chunk.push(Op::Nil);
        }

        self.locals.end_scope();
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
            Expression::Block(block) => self.block(block),
            Expression::If(if_) => self.expr_if(if_),
            Expression::Identifier(ident) => self.identifier(ident),
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

    fn identifier(&mut self, ident: &Identifier) -> Fallible<()> {
        if let Some((slot, _local)) = self.locals.resolve(&ident.name) {
            self.chunk.push(Op::LocalGet(slot));
        } else {
            let global = self.chunk.make_global(ident.name.clone());
            self.chunk.push(Op::GlobalGet(global));
        }
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

#[derive(Debug, Clone)]
struct Local {
    depth: usize,
    initialized: bool,

    ident: Identifier,
}

#[derive(Debug, Clone, Default)]
struct Locals {
    locals: Vec<Local>,
    scope_depth: usize,
}

impl Locals {
    fn begin_scope(&mut self) {
        self.scope_depth += 1;
    }

    fn end_scope(&mut self) -> usize {
        self.scope_depth -= 1;

        let mut count = 0;

        while let Some(local) = self.locals.last() {
            if local.depth > self.scope_depth {
                self.locals.pop();
                count += 1;
            } else {
                break;
            }
        }

        count
    }

    fn iter_slots(&self) -> impl Iterator<Item = (usize, &Local)> {
        self.locals.iter().rev().enumerate()
    }

    fn iter_stack(&self) -> impl Iterator<Item = &Local> {
        self.locals.iter().rev()
    }

    fn resolve<'a>(&'a self, name: &str) -> Option<(u8, &'a Local)> {
        for (slot, var) in self.iter_slots() {
            if var.ident.name == name {
                let slot: u8 = slot.try_into().expect("Too many locals!");
                return Some((slot, var));
            }
        }
        None
    }

    fn reserve(&mut self, ident: Identifier) -> CompileResult<u8> {
        if self.locals.len() >= (u8::MAX as usize) {
            panic!("Too many locals! Time to add Local2 variants");
        }

        let new = Local {
            ident,
            depth: self.scope_depth,
            initialized: false,
        };

        for old in self.iter_stack() {
            if old.ident.name == new.ident.name && old.depth == new.depth {
                return Err(CompileError::DuplicateVariable(new.ident));
            }
        }

        let slot: u8 = self
            .locals
            .len()
            .try_into()
            .expect("Too many locals! Time to add Local2 variants");
        self.locals.push(new);
        Ok(slot)
    }

    fn mark_init(&mut self, slot: u8) {
        self.locals[slot as usize].initialized = true;
    }
}
