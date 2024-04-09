use num_rational::BigRational;
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
            Declaration::Func(func) => self.decl_func(func),
            Declaration::Let(let_) => self.decl_let(let_),
            Declaration::Statement(stmt) => self.statement(stmt),
        }
    }

    #[instrument(level = "trace")]
    fn decl_func(&mut self, func: &Func) -> Fallible<()> {
        // - Declare the identifier in the current scope
        // - Mark it as initialized so it's usable within the func body
        // - Start a new scope containing all the param names
        // - Start a new chunk for the implementation.
        // - Compile the function into the chunk.
        // - Make a constant to hold the func header
        // - Load the constant and store it in the local/global name
        todo!("start here")
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
        let Expression::LogicOr(or) = expr;
        self.logic_or(or)
    }

    #[instrument(level = "trace")]
    fn logic_or(&mut self, or: &LogicOr) -> Fallible<()> {
        // This leaves the last value that was considered on top of the stack.

        // <a>
        self.logic_and(&or.first)?;

        let mut shorts = Vec::new();
        for and in &or.rest {
            // jump_true_peek 'short_circuit
            let short = self.chunk.prepare_jump(Op::JumpTruePeek(i16::MAX));
            shorts.push(short);

            // pop ; <a> was falsey
            self.chunk.push(Op::Pop);

            // <b>
            self.logic_and(and)?;
        }

        // 'short_circuit:
        for jump in shorts {
            self.chunk.set_jump_target(jump);
        }

        Ok(())
    }

    fn logic_and(&mut self, and: &LogicAnd) -> Fallible<()> {
        // This leaves the last value that was considered on top of the stack.

        // <a>
        self.equality(&and.first)?;

        let mut shorts = Vec::new();
        for eq in &and.rest {
            // jump_false_peek 'short_circuit
            let short = self.chunk.prepare_jump(Op::JumpFalsePeek(i16::MAX));
            shorts.push(short);

            // pop ; <a> was truthy
            self.chunk.push(Op::Pop);

            // <b>
            self.equality(eq)?;
        }

        // 'short_circuit:
        for jump in shorts {
            self.chunk.set_jump_target(jump);
        }

        Ok(())
    }

    fn equality(&mut self, eq: &Equality) -> Fallible<()> {
        match eq {
            Equality::Value(comp) => self.comparison(comp),

            Equality::Eq(a, b) => {
                self.equality(a)?;
                self.comparison(b)?;
                self.chunk.push(Op::Eq);
                Ok(())
            }

            Equality::Ne(a, b) => {
                self.equality(a)?;
                self.comparison(b)?;
                self.chunk.push(Op::Ne);
                Ok(())
            }
        }
    }

    fn comparison(&mut self, comp: &Comparison) -> Fallible<()> {
        match comp {
            Comparison::Value(term) => self.term(term),

            Comparison::Gt(a, b) => {
                self.comparison(a)?;
                self.term(b)?;
                self.chunk.push(Op::Gt);
                Ok(())
            }

            Comparison::Ge(a, b) => {
                self.comparison(a)?;
                self.term(b)?;
                self.chunk.push(Op::Ge);
                Ok(())
            }

            Comparison::Lt(a, b) => {
                self.comparison(a)?;
                self.term(b)?;
                self.chunk.push(Op::Lt);
                Ok(())
            }

            Comparison::Le(a, b) => {
                self.comparison(a)?;
                self.term(b)?;
                self.chunk.push(Op::Le);
                Ok(())
            }
        }
    }

    fn term(&mut self, term: &Term) -> Fallible<()> {
        match term {
            Term::Value(factor) => self.factor(factor),

            Term::Add(a, b) => {
                self.term(a)?;
                self.factor(b)?;
                self.chunk.push(Op::Add);
                Ok(())
            }

            Term::Sub(a, b) => {
                self.term(a)?;
                self.factor(b)?;
                self.chunk.push(Op::Sub);
                Ok(())
            }
        }
    }

    fn factor(&mut self, factor: &Factor) -> Fallible<()> {
        match factor {
            Factor::Value(unary) => self.unary(unary),

            Factor::Mul(a, b) => {
                self.factor(a)?;
                self.unary(b)?;
                self.chunk.push(Op::Mul);
                Ok(())
            }

            Factor::Div(a, b) => {
                self.factor(a)?;
                self.unary(b)?;
                self.chunk.push(Op::Div);
                Ok(())
            }

            Factor::Rem(a, b) => {
                self.factor(a)?;
                self.unary(b)?;
                self.chunk.push(Op::Rem);
                Ok(())
            }
        }
    }

    fn unary(&mut self, unary: &Unary) -> Fallible<()> {
        match unary {
            Unary::Value(call) => self.call(call),

            Unary::Not(a) => {
                self.unary(a)?;
                self.chunk.push(Op::Not);
                Ok(())
            }

            Unary::Neg(a) => {
                self.unary(a)?;
                self.chunk.push(Op::Neg);
                Ok(())
            }
        }
    }

    fn call(&mut self, call: &Call) -> Fallible<()> {
        match call {
            Call::Value(primary) => self.primary(primary),

            Call::Call(callee, args) => {
                self.call(callee)?;
                for arg in args {
                    self.expression(arg)?;
                }

                let arity: u8 = args.len().try_into().expect("at most 255 args");
                self.chunk.push(Op::Call(arity));
                Ok(())
            }

            Call::Index(obj, key) => {
                self.call(obj)?;
                self.expression(key)?;
                self.chunk.push(Op::Index);
                Ok(())
            }

            Call::Field(obj, field) => {
                self.call(obj)?;

                let name = Constant::String(field.name.clone());
                let id = self.chunk.add_constant(name);
                self.chunk.push(Op::Constant(id));
                Ok(())
            }
        }
    }

    #[instrument(level = "trace")]
    fn primary(&mut self, primary: &Primary) -> Fallible<()> {
        match primary {
            Primary::Block(block) => self.block(block),
            Primary::If(if_) => self.expr_if(if_),
            Primary::Atom(atom) => self.atom(atom),
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
                let r = BigRational::new(v.clone(), 1.into());
                let id = self.chunk.add_constant(Constant::Rational(r));
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
