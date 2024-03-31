use tracing::{debug, instrument};

use crate::bytecode::{Chunk, Constant, Op};
use crate::parse::ast::*;

#[derive(Debug)]
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

#[derive(Debug)]
struct FailedCodegen;

impl Compiler {
    fn new() -> Self {
        Self {
            chunk: Chunk::default(),
            errors: Vec::new(),
            locals: Locals::default(),
        }
    }

    fn error(&mut self, err: CompileError) -> FailedCodegen {
        debug!({ ?err }, "compile error");
        self.errors.push(err);
        FailedCodegen
    }

    #[instrument(level = "debug", ret)]
    pub fn compile(program: &Program) -> Result<Chunk, CompileErrors> {
        let mut compiler = Self::new();
        let _ = compiler.program(program); // Errors checked below

        if compiler.errors.is_empty() {
            for (idx, val) in compiler.chunk.constants.iter().enumerate() {
                debug!({ ?idx, ?val }, "constant");
            }

            for (idx, name) in compiler.chunk.globals.iter().enumerate() {
                debug!({ ?idx, ?name }, "global");
            }

            for res in compiler.chunk.iter_code() {
                let Ok((pc, op)) = res else {
                    debug!({ ?res }, "chunk error");
                    break;
                };
                debug!({ ?pc, ?op }, "code");
            }

            Ok(compiler.chunk)
        } else {
            Err(CompileErrors(compiler.errors))
        }
    }

    #[instrument(level = "trace")]
    fn program(&mut self, program: &Program) -> Fallible<()> {
        for decl in &program.decls {
            self.declaration(decl)?;
        }
        self.chunk.push(Op::Return);
        Ok(())
    }

    #[instrument(level = "trace")]
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

    #[instrument(level = "trace")]
    fn declaration(&mut self, decl: &Declaration) -> Fallible<()> {
        match decl {
            Declaration::Let(let_) => self.decl_let(let_),
            Declaration::Statement(stmt) => self.statement(stmt),
        }
    }

    #[instrument(level = "trace")]
    fn decl_let(&mut self, let_: &Let) -> Fallible<()> {
        let slot = self
            .locals
            .reserve(let_.ident.clone())
            .map_err(|err| self.error(err))?;

        self.expression(&let_.expr)?;

        self.locals.mark_init(slot);
        Ok(())
    }

    #[instrument(level = "trace")]
    fn statement(&mut self, stmt: &Statement) -> Fallible<()> {
        match stmt {
            Statement::Assignment(assign) => self.stmt_assign(assign),

            Statement::Expression(expr) => {
                self.expression(expr)?;
                self.chunk.push(Op::Pop);
                Ok(())
            }
        }
    }

    #[instrument(level = "trace")]
    fn stmt_assign(&mut self, assign: &Assignment) -> Fallible<()> {
        let Place::Identifier(ident) = &assign.place;

        self.expression(&assign.expr)?;

        if let Some((slot, _local)) = self.locals.resolve(&ident.name) {
            self.chunk.push(Op::LocalSet(slot));
        } else {
            let global = self.chunk.make_global(ident.name.clone());
            self.chunk.push(Op::GlobalSet(global));
        }

        Ok(())
    }

    #[instrument(level = "trace")]
    fn expression(&mut self, expr: &Expression) -> Fallible<()> {
        match expr {
            Expression::Block(block) => self.block(block),
            Expression::If(if_) => self.expr_if(if_),
            Expression::Atom(atom) => self.atom(atom),
        }
    }

    #[instrument(level = "trace")]
    fn atom(&mut self, atom: &Atom) -> Fallible<()> {
        match atom {
            Atom::Identifier(ident) => self.identifier(ident),
            Atom::Literal(lit) => self.literal(lit),
        }
    }

    #[instrument(level = "trace")]
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
            self.chunk.push(Op::Nil);
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

    #[instrument(level = "trace")]
    fn identifier(&mut self, ident: &Identifier) -> Fallible<()> {
        if let Some((slot, _local)) = self.locals.resolve(&ident.name) {
            self.chunk.push(Op::LocalGet(slot));
        } else {
            let global = self.chunk.make_global(ident.name.clone());
            self.chunk.push(Op::GlobalGet(global));
        }
        Ok(())
    }

    #[instrument(level = "trace")]
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
    #[instrument(level = "trace")]
    fn begin_scope(&mut self) {
        self.scope_depth += 1;
    }

    #[instrument(level = "trace")]
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
        self.locals.iter().enumerate().rev()
    }

    fn iter_stack(&self) -> impl Iterator<Item = &Local> {
        self.locals.iter().rev()
    }

    #[instrument(level = "trace")]
    fn resolve<'a>(&'a self, name: &str) -> Option<(u8, &'a Local)> {
        for (slot, var) in self.iter_slots() {
            if var.ident.name == name {
                let slot: u8 = slot.try_into().expect("Too many locals!");
                return Some((slot, var));
            }
        }
        None
    }

    #[instrument(level = "trace")]
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

    #[instrument(level = "trace")]
    fn mark_init(&mut self, slot: u8) {
        self.locals[slot as usize].initialized = true;
    }
}
