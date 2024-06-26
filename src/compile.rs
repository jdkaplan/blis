use std::cell::RefCell;
use std::collections::VecDeque;
use std::rc::Rc;

use num_rational::BigRational;
use serde::Serialize;
use tracing::{debug, instrument, trace};

use crate::bytecode;
use crate::bytecode::chunk::PendingJump;
use crate::bytecode::{Capture, Chunk, Constant, Op};
use crate::parse::ast::*;

#[derive(thiserror::Error, Debug, Serialize)]
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

#[derive(thiserror::Error, Debug, Serialize)]
pub enum CompileError {
    #[error(
        "variable redeclared in the same scope: `{}`",
        .0.name
    )]
    DuplicateVariable(Identifier),

    #[error("`self` used outside of method definition")]
    SelfOutsideMethod,

    #[error("no prior label for `break`: {}", .0.name)]
    NoBreakLabel(Identifier),

    #[error("no prior label for `continue`: {}", .0.name)]
    NoContinueLabel(Identifier),

    #[error("{0}")]
    Other(String), // TODO: Define other compile errors
}

type CompileResult<T> = Result<T, CompileError>;

type Fallible<T> = Result<T, FailedCodegen>;

#[derive(Debug)]
struct FailedCodegen;

pub struct Compiler {
    stack: Vec<Rc<RefCell<FuncBuilder>>>,
    errors: Vec<CompileError>,
}

impl Compiler {
    fn new() -> Self {
        Self {
            stack: Vec::new(),
            errors: Vec::new(),
        }
    }

    fn error(&mut self, err: CompileError) -> FailedCodegen {
        debug!({ ?err }, "compile error");
        self.errors.push(err);
        FailedCodegen
    }

    fn start(&mut self, mode: FuncMode) -> FuncRef {
        let func = FuncBuilder::new(mode);
        let rc = Rc::new(RefCell::new(func));
        self.stack.push(rc.clone());
        FuncRef(rc)
    }

    fn current(&self) -> FuncRef {
        let last = self.stack.last().expect("start called first");
        FuncRef(last.clone())
    }

    fn finish(&mut self, name: &str, handle: FuncRef) -> FuncBuilder {
        // This handle should be the last external reference (created by start). Drop it early so
        // the unwrapping below can succeed.
        drop(handle);

        let last = self.stack.pop().expect("paired with start call");
        let last = Rc::try_unwrap(last).expect("no remaining references from inner funcs");
        let last = last.into_inner();

        debug_chunk(name, &last.chunk);
        last
    }

    #[instrument(level = "debug", skip_all, ret)]
    pub fn compile(program: &Program) -> Result<Chunk, CompileErrors> {
        let mut driver = Self::new();

        let Ok(func) = driver.program(program) else {
            return Err(CompileErrors(driver.errors));
        };

        Ok(func.chunk)
    }

    #[instrument(level = "trace", skip_all)]
    fn program(&mut self, program: &Program) -> Fallible<FuncBuilder> {
        let current = self.start(FuncMode::Script);

        // Reserve stack slot 0 for the currently-executing program.
        current
            .reserve_local(Identifier::empty())
            .map_err(|err| self.error(err))?;

        for decl in &program.decls {
            self.declaration(decl)?;
        }
        current.push(Op::Nil);
        current.push(Op::Return);

        Ok(self.finish("<script>", current))
    }

    #[instrument(level = "trace", skip_all)]
    fn block(&mut self, block: &Block) -> Fallible<()> {
        let func = self.current();
        func.begin_scope();

        for decl in &block.decls {
            self.declaration(decl)?;
        }

        if let Some(expr) = &block.expr {
            self.expression(expr)?;
        } else {
            func.push(Op::Nil);
        }

        let locals = func.end_scope();
        let n: u8 = locals.len().try_into().unwrap();
        func.push(Op::PopUnderN(n));

        Ok(())
    }

    #[instrument(level = "trace", skip_all)]
    fn declaration(&mut self, decl: &Declaration) -> Fallible<()> {
        match decl {
            Declaration::Func(func) => self.decl_func(func),
            Declaration::Let(let_) => self.decl_let(let_),
            Declaration::Type(ty) => self.decl_type(ty),
            Declaration::Statement(stmt) => self.statement(stmt),
        }
    }

    #[instrument(level = "trace", skip_all)]
    fn decl_type(&mut self, ty: &Type) -> Fallible<()> {
        // Make the name immediately available for use so it can be used inside the definition
        // itself.
        let current = self.current();
        let slot = current
            .reserve_local(ty.ident.clone())
            .map_err(|err| self.error(err))?;
        current.init_local(slot);

        let constant = current.add_name_constant(&ty.ident);
        current.push(Op::Type(constant));

        for method in &ty.methods {
            current.begin_scope();
            self.decl_method(method)?;

            let constant = current.add_name_constant(&method.ident);
            current.push(Op::SetMethod(constant));

            // AddMethod already pops the method off the stack, so don't do it twice!
            let locals = current.end_scope();
            assert_eq!(locals.len(), 1, "{:?}", locals);
        }

        if slot == Slot::Global {
            current.define_global(&ty.ident);
        }

        Ok(())
    }

    #[instrument(level = "trace", skip_all)]
    fn decl_method(&mut self, method: &Method) -> Fallible<()> {
        let arity = method.params.len();
        let arity: u8 = arity.try_into().expect("parser enforces limit");

        // Reserve a slot for the method.
        let enclosing = self.current();
        enclosing
            .reserve_local(Identifier::empty())
            .map_err(|err| self.error(err))?;

        let (bfunc, upvalues) = {
            let mode = if method.self_ {
                FuncMode::Method
            } else {
                FuncMode::AssociatedFunc
            };
            let current = self.start(mode);

            current.begin_scope();

            // Reserve a slot for the receiver.
            if method.self_ {
                let slot = current
                    .reserve_local(Identifier::new("self"))
                    .map_err(|err| self.error(err))?;
                current.init_local(slot);
            }

            for param in &method.params {
                let slot = current
                    .reserve_local(param.clone())
                    .map_err(|err| self.error(err))?;
                current.init_local(slot);
            }

            self.block(&method.body)?;
            current.push(Op::Return);

            // There's no end_scope() call here because the Return instruction will pop the whole
            // call frame.

            let builder = self.finish(&method.ident.name, current);

            let bfunc = bytecode::Func {
                name: method.ident.name.clone(),
                arity,
                upvalues: builder.upvalues.len(),
                chunk: builder.chunk,
            };
            (bfunc, builder.upvalues)
        };

        let constant = enclosing.add_constant(Constant::Func(bfunc));
        enclosing.push(Op::Closure(
            constant,
            upvalues.len(),
            upvalues.into_captures(),
        ));

        Ok(())
    }

    #[instrument(level = "trace", skip_all)]
    fn decl_func(&mut self, func: &Func) -> Fallible<()> {
        let arity = func.params.len();
        let arity: u8 = arity.try_into().expect("parser enforces limit");

        // Make the name immediately available so it can be used inside the function itself
        // (recursion!).
        let enclosing = self.current();
        let slot = enclosing
            .reserve_local(func.ident.clone())
            .map_err(|err| self.error(err))?;
        enclosing.init_local(slot);

        let (bfunc, upvalues) = {
            let current = self.start(FuncMode::FreeFunc);

            current.begin_scope();

            // Reserve a slot for the callee.
            current
                .reserve_local(Identifier::empty())
                .map_err(|err| self.error(err))?;

            for param in &func.params {
                let slot = current
                    .reserve_local(param.clone())
                    .map_err(|err| self.error(err))?;
                current.init_local(slot);
            }

            self.block(&func.body)?;
            current.push(Op::Return);

            // There's no end_scope() call here because the Return instruction will pop the whole
            // call frame.

            let builder = self.finish(&func.ident.name, current);

            let bfunc = bytecode::Func {
                name: func.ident.name.clone(),
                arity,
                upvalues: builder.upvalues.len(),
                chunk: builder.chunk,
            };
            (bfunc, builder.upvalues)
        };

        let constant = enclosing.add_constant(Constant::Func(bfunc));

        enclosing.push(Op::Closure(
            constant,
            upvalues.len(),
            upvalues.into_captures(),
        ));

        if slot == Slot::Global {
            enclosing.define_global(&func.ident);
        }

        Ok(())
    }

    #[instrument(level = "trace", skip_all)]
    fn decl_let(&mut self, let_: &Let) -> Fallible<()> {
        let current = self.current();

        let slot = current
            .reserve_local(let_.ident.clone())
            .map_err(|err| self.error(err))?;

        self.expression(&let_.expr)?;

        if slot == Slot::Global {
            current.define_global(&let_.ident);
        }

        current.init_local(slot);
        Ok(())
    }

    #[instrument(level = "trace", skip_all)]
    fn statement(&mut self, stmt: &Statement) -> Fallible<()> {
        match stmt {
            Statement::Break(break_) => self.stmt_break(break_),
            Statement::Continue(continue_) => self.stmt_continue(continue_),
            Statement::Loop(loop_) => self.stmt_loop(loop_),
            Statement::Return(return_) => self.stmt_return(return_),
            Statement::Assignment(assign) => self.stmt_assign(assign),
            Statement::Expression(expr) => {
                self.expression(expr)?;
                self.current().push(Op::Pop);
                Ok(())
            }
        }
    }

    #[instrument(level = "trace", skip_all)]
    fn stmt_break(&mut self, break_: &Break) -> Fallible<()> {
        let current = self.current();

        let locals = current.break_scope();
        let n: u8 = locals.len().try_into().unwrap();
        current.push(Op::PopN(n));

        let jump = current.prepare_jump(Op::Jump(0));
        current
            .add_break(&break_.label, jump)
            .map_err(|err| self.error(err))
    }

    #[instrument(level = "trace", skip_all)]
    fn stmt_continue(&mut self, continue_: &Continue) -> Fallible<()> {
        let current = self.current();

        let locals = current.break_scope();
        let n: u8 = locals.len().try_into().unwrap();
        current.push(Op::PopN(n));

        current
            .add_continue(&continue_.label)
            .map_err(|err| self.error(err))
    }

    #[instrument(level = "trace", skip_all)]
    fn stmt_loop(&mut self, loop_: &Loop) -> Fallible<()> {
        let current = self.current();

        // 'continue:
        current.start_loop(loop_.label.clone());

        // <body>
        self.block(&loop_.body)?;

        // jump 'continue
        current
            .add_continue(&loop_.label)
            .map_err(|err| self.error(err))?;

        // 'break:
        let label = current
            .end_loop(&loop_.label)
            .map_err(|err| self.error(err))?;
        for jump in label.breaks {
            current.set_jump_target(jump);
        }

        Ok(())
    }

    #[instrument(level = "trace", skip_all)]
    fn stmt_return(&mut self, return_: &Return) -> Fallible<()> {
        let current = self.current();

        self.expression(&return_.expr)?;
        current.push(Op::Return);

        Ok(())
    }

    #[instrument(level = "trace", skip_all)]
    fn stmt_assign(&mut self, assign: &Assignment) -> Fallible<()> {
        let current = self.current();

        match &assign.place {
            Place::Field(obj, ident) => {
                // Evaluate left-to-right so that
                //
                //     obj_expr.ident = expr;
                //
                // is the same as
                //
                //     let obj = obj_expr;
                //     let val = expr;
                //     obj.ident = val;
                //
                self.call(obj)?;

                let id = current.add_name_constant(ident);
                self.expression(&assign.expr)?;
                current.push(Op::SetField(id));
                current.push(Op::Pop);
            }
            Place::Index(obj, key) => {
                // Evaluate left-to-right so that
                //
                //     obj_expr[idx_expr] = expr;
                //
                // is the same as
                //
                //     let obj = obj_expr;
                //     let idx = idx_expr;
                //     obj[idx] = val;
                //
                self.call(obj)?;
                self.expression(key)?;

                self.expression(&assign.expr)?;
                current.push(Op::SetIndex);
            }
            Place::Identifier(ident) => {
                // ident = expr
                self.expression(&assign.expr)?;

                if ident.name == "self" {
                    todo!("error: cannot assign to receiver");
                }

                if let Some((slot, _local)) = current.resolve_local(ident) {
                    current.push(Op::SetLocal(slot));
                } else if let Some(upvalue) = self.resolve_upvalue(ident) {
                    current.push(Op::SetUpvalue(upvalue.index()));
                } else {
                    let global = current.make_global(ident);
                    current.push(Op::SetGlobal(global));
                }
            }
        }

        Ok(())
    }

    #[instrument(level = "trace", skip(self))]
    fn resolve_upvalue(&mut self, ident: &Identifier) -> Option<Upvalue> {
        // This may walk the entire stack, so prepare the references. The current compiler is
        // special (we already know it doesn't bind this variable), so pop it off immediately.
        let mut stack: Vec<FuncRef> = self.stack.iter().cloned().map(FuncRef).collect();
        let current = stack.pop().expect("start called before resolving anything");

        // When using deeply-nested functions, it's possible that the referring function (that
        // uses the upvalue) doesn't even exist until some intermediate call frames exist. So this
        // uses "flat closures" that also track upvalues used by their descendants (even the
        // upvalue is not used by that intermediate function itself).
        let mut intermediates = vec![current];

        let mut definition = None;
        while let Some(enclosing) = stack.pop() {
            if let Some(slot) = enclosing.capture_local(ident) {
                definition = Some(slot);
                break;
            } else {
                intermediates.push(enclosing);
            }
        }

        // If there was definition in some enclosing scope, mark it as captured and prepare its
        // immediate upvalue reference.
        let mut upvalue = match definition {
            Some(slot) => Upvalue::Local(slot),
            None => return None, // Must be a global, then!
        };

        // The outermost scope references its parent's local directly. The next scope binds _that_
        // upvalue reference, and so on until we reach the current function.
        //
        // If there are no intermediate scopes, then the current function gets the local reference.
        while let Some(closure) = intermediates.pop() {
            upvalue = closure.add_upvalue(upvalue);
        }

        Some(upvalue)
    }

    #[instrument(level = "trace", skip_all)]
    fn expression(&mut self, expr: &Expression) -> Fallible<()> {
        let Expression::LogicOr(or) = expr;
        self.logic_or(or)
    }

    #[instrument(level = "trace", skip_all)]
    fn logic_or(&mut self, or: &LogicOr) -> Fallible<()> {
        let current = self.current();

        // This leaves the last value that was considered on top of the stack.

        // <a>
        self.logic_and(&or.first)?;

        let mut shorts = Vec::new();
        for and in &or.rest {
            // jump_true_peek 'short_circuit
            let short = current.prepare_jump(Op::JumpTruePeek(0));
            shorts.push(short);

            // pop ; <a> was falsey
            current.push(Op::Pop);

            // <b>
            self.logic_and(and)?;
        }

        // 'short_circuit:
        for jump in shorts {
            current.set_jump_target(jump);
        }

        Ok(())
    }

    fn logic_and(&mut self, and: &LogicAnd) -> Fallible<()> {
        let current = self.current();

        // This leaves the last value that was considered on top of the stack.

        // <a>
        self.equality(&and.first)?;

        let mut shorts = Vec::new();
        for eq in &and.rest {
            // jump_false_peek 'short_circuit
            let short = current.prepare_jump(Op::JumpFalsePeek(0));
            shorts.push(short);

            // pop ; <a> was truthy
            current.push(Op::Pop);

            // <b>
            self.equality(eq)?;
        }

        // 'short_circuit:
        for jump in shorts {
            current.set_jump_target(jump);
        }

        Ok(())
    }

    fn equality(&mut self, eq: &Equality) -> Fallible<()> {
        let current = self.current();

        match eq {
            Equality::Value(comp) => self.comparison(comp),

            Equality::Eq(a, b) => {
                self.equality(a)?;
                self.comparison(b)?;
                current.push(Op::Eq);
                Ok(())
            }

            Equality::Ne(a, b) => {
                self.equality(a)?;
                self.comparison(b)?;
                current.push(Op::Ne);
                Ok(())
            }
        }
    }

    fn comparison(&mut self, comp: &Comparison) -> Fallible<()> {
        let current = self.current();

        match comp {
            Comparison::Value(term) => self.term(term),

            Comparison::Gt(a, b) => {
                self.comparison(a)?;
                self.term(b)?;
                current.push(Op::Gt);
                Ok(())
            }

            Comparison::Ge(a, b) => {
                self.comparison(a)?;
                self.term(b)?;
                current.push(Op::Ge);
                Ok(())
            }

            Comparison::Lt(a, b) => {
                self.comparison(a)?;
                self.term(b)?;
                current.push(Op::Lt);
                Ok(())
            }

            Comparison::Le(a, b) => {
                self.comparison(a)?;
                self.term(b)?;
                current.push(Op::Le);
                Ok(())
            }
        }
    }

    fn term(&mut self, term: &Term) -> Fallible<()> {
        let current = self.current();

        match term {
            Term::Value(factor) => self.factor(factor),

            Term::Add(a, b) => {
                self.term(a)?;
                self.factor(b)?;
                current.push(Op::Add);
                Ok(())
            }

            Term::Sub(a, b) => {
                self.term(a)?;
                self.factor(b)?;
                current.push(Op::Sub);
                Ok(())
            }
        }
    }

    fn factor(&mut self, factor: &Factor) -> Fallible<()> {
        let current = self.current();

        match factor {
            Factor::Value(unary) => self.unary(unary),

            Factor::Mul(a, b) => {
                self.factor(a)?;
                self.unary(b)?;
                current.push(Op::Mul);
                Ok(())
            }

            Factor::Div(a, b) => {
                self.factor(a)?;
                self.unary(b)?;
                current.push(Op::Div);
                Ok(())
            }

            Factor::Rem(a, b) => {
                self.factor(a)?;
                self.unary(b)?;
                current.push(Op::Rem);
                Ok(())
            }
        }
    }

    fn unary(&mut self, unary: &Unary) -> Fallible<()> {
        let current = self.current();

        match unary {
            Unary::Value(call) => self.call(call),

            Unary::Not(a) => {
                self.unary(a)?;
                current.push(Op::Not);
                Ok(())
            }

            Unary::Neg(a) => {
                self.unary(a)?;
                current.push(Op::Neg);
                Ok(())
            }
        }
    }

    fn call(&mut self, call: &Call) -> Fallible<()> {
        let current = self.current();

        match call {
            Call::Value(primary) => self.primary(primary),

            Call::Call(callee, args) => {
                self.call(callee)?;
                for arg in args {
                    self.expression(arg)?;
                }

                let arity: u8 = args.len().try_into().expect("at most 255 args");
                current.push(Op::Call(arity));
                Ok(())
            }

            Call::Index(obj, key) => {
                self.call(obj)?;
                self.expression(key)?;
                current.push(Op::GetIndex);
                Ok(())
            }

            Call::Field(obj, ident) => {
                self.call(obj)?;

                let id = current.add_name_constant(ident);
                current.push(Op::GetField(id));
                Ok(())
            }
        }
    }

    #[instrument(level = "trace", skip_all)]
    fn primary(&mut self, primary: &Primary) -> Fallible<()> {
        match primary {
            Primary::Block(block) => self.block(block),
            Primary::If(if_) => self.expr_if(if_),
            Primary::Atom(atom) => self.atom(atom),
            Primary::Group(expr) => self.expression(expr),
        }
    }

    #[instrument(level = "trace", skip_all)]
    fn atom(&mut self, atom: &Atom) -> Fallible<()> {
        match atom {
            Atom::Identifier(ident) => self.expr_identifier(ident),
            Atom::Literal(lit) => self.expr_literal(lit),
            Atom::Object(obj) => self.expr_object(obj),
            Atom::List(list) => self.expr_list(list),
        }
    }

    #[instrument(level = "trace", skip_all)]
    fn expr_if(&mut self, if_: &If) -> Fallible<()> {
        let current = self.current();

        // <cond>
        self.expression(&if_.condition)?;

        // jump_false_pop 'skip_conseq [peek cond]
        let skip_conseq = current.prepare_jump(Op::JumpFalsePop(0));

        // <consequent>
        self.block(&if_.consequent)?;

        let Some(alt) = &if_.alternative else {
            // 'skip_conseq:
            current.set_jump_target(skip_conseq);
            current.push(Op::Nil);
            return Ok(());
        };

        // jump 'skip_alt
        let skip_alt = current.prepare_jump(Op::Jump(0));

        // 'skip_conseq:
        current.set_jump_target(skip_conseq);

        // <alternative>
        self.block(alt)?;

        // 'skip_alt:
        current.set_jump_target(skip_alt);

        Ok(())
    }

    #[instrument(level = "trace", skip_all)]
    fn expr_object(&mut self, obj: &Object) -> Fallible<()> {
        let current = self.current();

        self.expr_identifier(&obj.ty)?;
        current.push(Op::Object);

        for (ident, expr) in &obj.fields {
            let id = current.add_name_constant(ident);

            self.expression(expr)?;
            current.push(Op::SetField(id));
        }

        Ok(())
    }

    #[instrument(level = "trace", skip_all)]
    fn expr_list(&mut self, list: &List) -> Fallible<()> {
        let len: u8 = list.items.len().try_into().expect("time for BigList");

        let current = self.current();

        for expr in &list.items {
            self.expression(expr)?;
        }

        current.push(Op::List(len));

        Ok(())
    }

    #[instrument(level = "trace", skip_all)]
    fn expr_identifier(&mut self, ident: &Identifier) -> Fallible<()> {
        let current = self.current();

        if ident.name == "self" {
            match current.mode() {
                FuncMode::Script | FuncMode::FreeFunc | FuncMode::AssociatedFunc => {
                    return Err(self.error(CompileError::SelfOutsideMethod));
                }
                FuncMode::Method => {
                    let (slot, _local) =
                        current.resolve_local(ident).expect("method defines `self`");
                    current.push(Op::GetLocal(slot));
                    return Ok(());
                }
            }
        }

        if let Some((slot, _local)) = current.resolve_local(ident) {
            current.push(Op::GetLocal(slot));
        } else if let Some(upvalue) = self.resolve_upvalue(ident) {
            current.push(Op::GetUpvalue(upvalue.index()));
        } else {
            let global = current.make_global(ident);
            current.push(Op::GetGlobal(global));
        }
        Ok(())
    }

    #[instrument(level = "trace", skip_all)]
    fn expr_literal(&mut self, lit: &Literal) -> Fallible<()> {
        let current = self.current();

        match lit {
            Literal::Nil => {
                current.push(Op::Nil);
            }
            Literal::Boolean(b) => {
                if *b {
                    current.push(Op::True);
                } else {
                    current.push(Op::False);
                }
            }

            Literal::Integer(v) => {
                let r = BigRational::new(v.clone(), 1.into());
                let id = current.add_constant(Constant::Rational(r));
                current.push(Op::Constant(id));
            }
            Literal::Float(v) => {
                let id = current.add_constant(Constant::Float(*v));
                current.push(Op::Constant(id));
            }
            Literal::String(v) => {
                let id = current.add_constant(Constant::String(v.clone()));
                current.push(Op::Constant(id));
            }
        }

        Ok(())
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum FuncMode {
    Script,
    FreeFunc,
    AssociatedFunc,
    Method,
}

#[derive(Debug)]
struct FuncBuilder {
    mode: FuncMode,
    chunk: Chunk,
    locals: Locals,
    upvalues: Upvalues,
    labels: Loops,
}

impl FuncBuilder {
    fn new(mode: FuncMode) -> Self {
        Self {
            mode,
            chunk: Chunk::default(),
            locals: Locals::default(),
            upvalues: Upvalues::default(),
            labels: Loops::default(),
        }
    }
}

#[derive(Debug, Clone)]
struct FuncRef(Rc<RefCell<FuncBuilder>>);

impl FuncRef {
    fn mode(&self) -> FuncMode {
        self.0.borrow().mode
    }

    fn begin_scope(&self) {
        let mut func = self.0.borrow_mut();
        func.locals.begin_scope()
    }

    fn break_scope(&self) -> Vec<Local> {
        let mut func = self.0.borrow_mut();
        func.locals.break_scope()
    }

    fn end_scope(&self) -> Vec<Local> {
        let mut func = self.0.borrow_mut();
        func.locals.end_scope()
    }

    fn reserve_local(&self, ident: Identifier) -> CompileResult<Slot> {
        let mut func = self.0.borrow_mut();
        func.locals.reserve(ident)
    }

    fn resolve_local(&self, ident: &Identifier) -> Option<(u8, Local)> {
        let func = self.0.borrow_mut();
        func.locals
            .resolve(&ident.name)
            .map(|(slot, local)| (slot, local.clone()))
    }

    fn capture_local(&self, ident: &Identifier) -> Option<u8> {
        let mut func = self.0.borrow_mut();
        match func.locals.resolve_mut(&ident.name) {
            Some((slot, local)) => {
                local.captured = true;
                Some(slot)
            }
            None => None,
        }
    }

    fn init_local(&self, slot: Slot) {
        let mut func = self.0.borrow_mut();
        func.locals.mark_init(slot)
    }

    fn add_upvalue(&self, upvalue: Upvalue) -> Upvalue {
        let mut func = self.0.borrow_mut();
        func.upvalues.push(upvalue)
    }

    fn push(&self, op: Op) {
        let mut func = self.0.borrow_mut();
        func.chunk.push(op)
    }

    #[allow(unused)]
    fn push_bytes(&self, bytes: &[u8]) {
        let mut func = self.0.borrow_mut();
        func.chunk.push_bytes(bytes)
    }

    fn add_constant(&self, constant: Constant) -> u8 {
        let mut func = self.0.borrow_mut();
        func.chunk.add_constant(constant)
    }

    fn add_name_constant(&self, ident: &Identifier) -> u8 {
        let name = Constant::String(ident.name.clone());

        let mut func = self.0.borrow_mut();
        func.chunk.add_constant(name)
    }

    fn define_global(&self, ident: &Identifier) {
        let mut func = self.0.borrow_mut();
        func.chunk.define_global(ident.name.clone())
    }

    fn make_global(&self, ident: &Identifier) -> u8 {
        let mut func = self.0.borrow_mut();
        func.chunk.make_global(ident.name.clone())
    }

    fn prepare_jump(&self, op: Op) -> PendingJump {
        let mut func = self.0.borrow_mut();
        func.chunk.prepare_jump(op)
    }

    fn set_jump_target(&self, jump: PendingJump) {
        let mut func = self.0.borrow_mut();
        func.chunk.set_jump_target(jump)
    }

    fn start_loop(&self, label: Option<Identifier>) {
        let mut func = self.0.borrow_mut();
        let start = func.chunk.code.len();
        func.labels.push(label, start)
    }

    fn end_loop(&self, label: &Option<Identifier>) -> CompileResult<PendingLoop> {
        let mut func = self.0.borrow_mut();
        func.labels.pop(label)
    }

    fn add_break(&self, label: &Option<Identifier>, jump: PendingJump) -> CompileResult<()> {
        let mut func = self.0.borrow_mut();
        func.labels.add_break(label, jump)
    }

    fn add_continue(&self, label: &Option<Identifier>) -> CompileResult<()> {
        let mut func = self.0.borrow_mut();
        let lp = func.labels.find(label)?;

        let len: isize = func.chunk.code.len().try_into().unwrap();
        let target: isize = lp.start.try_into().unwrap();
        assert!(target < len, "jump must be backwards");

        let delta: u16 = (len - target)
            .try_into()
            .expect("jump offset fits in two bytes");
        func.chunk.push(Op::Loop(delta));
        Ok(())
    }
}

#[derive(Debug, Clone)]
struct Local {
    depth: usize,
    ident: Identifier,
    initialized: bool,
    captured: bool,
}

#[derive(Debug, Clone, Default)]
struct Locals {
    locals: Vec<Local>,
    scope_depth: usize,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Slot {
    Global,
    Local(u8),
}

impl Locals {
    #[instrument(level = "trace")]
    fn begin_scope(&mut self) {
        self.scope_depth += 1;
    }

    #[instrument(level = "trace")]
    fn end_scope(&mut self) -> Vec<Local> {
        self.scope_depth -= 1;

        let mut popped = VecDeque::new();

        while let Some(local) = self.locals.last() {
            if local.depth > self.scope_depth {
                let owned = self.locals.pop().expect("last");
                popped.push_front(owned);
            } else {
                break;
            }
        }

        popped.into()
    }

    #[instrument(level = "trace")]
    fn break_scope(&mut self) -> Vec<Local> {
        let mut popped = VecDeque::new();

        for local in self.iter_stack() {
            if local.depth >= self.scope_depth {
                popped.push_front(local.clone());
            } else {
                break;
            }
        }

        popped.into()
    }

    fn iter_slots(&self) -> impl Iterator<Item = (usize, &Local)> {
        self.locals.iter().enumerate().rev()
    }

    fn iter_slots_mut(&mut self) -> impl Iterator<Item = (usize, &mut Local)> {
        self.locals.iter_mut().enumerate().rev()
    }

    fn iter_stack(&self) -> impl Iterator<Item = &Local> {
        self.locals.iter().rev()
    }

    #[instrument(level = "trace")]
    fn resolve<'a>(&'a self, name: &str) -> Option<(u8, &'a Local)> {
        for (slot, var) in self.iter_slots() {
            if var.ident.name == name && var.initialized {
                let slot: u8 = slot.try_into().expect("Too many locals!");
                return Some((slot, var));
            }
        }
        None
    }

    #[instrument(level = "trace")]
    fn resolve_mut<'a>(&'a mut self, name: &str) -> Option<(u8, &'a mut Local)> {
        for (slot, var) in self.iter_slots_mut() {
            if var.ident.name == name {
                let slot: u8 = slot.try_into().expect("Too many locals!");
                return Some((slot, var));
            }
        }
        None
    }

    #[instrument(level = "trace")]
    fn reserve(&mut self, ident: Identifier) -> CompileResult<Slot> {
        if self.scope_depth == 0 {
            return Ok(Slot::Global);
        }

        if self.locals.len() >= (u8::MAX as usize) {
            panic!("Too many locals! Time to add Local2 variants");
        }

        let new = Local {
            ident,
            depth: self.scope_depth,
            initialized: false,
            captured: false,
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
        Ok(Slot::Local(slot))
    }

    #[instrument(level = "trace")]
    fn mark_init(&mut self, slot: Slot) {
        match slot {
            Slot::Global => {}
            Slot::Local(idx) => {
                self.locals[idx as usize].initialized = true;
            }
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Upvalue {
    Local(u8),
    Nonlocal(u8),
}

impl Upvalue {
    fn index(&self) -> u8 {
        match self {
            Upvalue::Local(idx) | Upvalue::Nonlocal(idx) => *idx,
        }
    }
}

#[derive(Debug, Clone, Default)]
struct Upvalues(Vec<Upvalue>);

impl Upvalues {
    fn len(&self) -> u8 {
        self.0.len().try_into().unwrap()
    }

    fn push(&mut self, upvalue: Upvalue) -> Upvalue {
        // If this upvalue reference already exists, return a ref _to that ref_.
        for (idx, upv) in self.0.iter().enumerate() {
            if upv == &upvalue {
                let idx: u8 = idx.try_into().unwrap();
                return Upvalue::Nonlocal(idx);
            }
        }

        // Otherwise, create a new one.
        let idx = self.0.len();
        self.0.push(upvalue);

        let idx: u8 = idx.try_into().unwrap();
        Upvalue::Nonlocal(idx)
    }

    fn into_captures(self) -> Vec<Capture> {
        self.0
            .into_iter()
            .map(|upvalue| match upvalue {
                Upvalue::Local(idx) => Capture::Local(idx),
                Upvalue::Nonlocal(idx) => Capture::Nonlocal(idx),
            })
            .collect()
    }
}

#[derive(Debug, Clone, Default)]
struct Loops(Vec<PendingLoop>);

#[derive(Debug, Clone)]
struct PendingLoop {
    label: Option<Identifier>,
    start: usize,
    breaks: Vec<PendingJump>,
}

impl Loops {
    fn push(&mut self, label: Option<Identifier>, start: usize) {
        self.0.push(PendingLoop {
            label,
            start,
            breaks: Vec::new(),
        })
    }

    fn pop(&mut self, label: &Option<Identifier>) -> CompileResult<PendingLoop> {
        let lp = self.0.pop().expect("add_label called first");
        assert_eq!(lp.label, *label);
        Ok(lp)
    }

    fn add_break(&mut self, label: &Option<Identifier>, jump: PendingJump) -> CompileResult<()> {
        if let Some(name) = label {
            for lp in self.0.iter_mut().rev() {
                if lp.label.as_ref() == Some(name) {
                    lp.breaks.push(jump);
                    return Ok(());
                }
            }
            Err(CompileError::NoBreakLabel(name.clone()))
        } else {
            let lp = self.0.last_mut().ok_or(CompileError::Other(String::from(
                "break statement outside of loop",
            )))?;

            lp.breaks.push(jump);
            Ok(())
        }
    }

    fn find(&self, label: &Option<Identifier>) -> CompileResult<&PendingLoop> {
        if let Some(name) = label {
            for lp in self.0.iter().rev() {
                if lp.label.as_ref() == Some(name) {
                    return Ok(lp);
                }
            }
            Err(CompileError::NoContinueLabel(name.clone()))
        } else {
            self.0.last().ok_or(CompileError::Other(String::from(
                "continue statement outside of loop",
            )))
        }
    }
}

fn debug_chunk(name: &str, chunk: &Chunk) {
    debug!({ ?name }, "compiled chunk");

    for (idx, val) in chunk.constants.iter().enumerate() {
        trace!({ ?idx, ?val }, "constant");
    }

    for (idx, name) in chunk.globals.iter().enumerate() {
        trace!({ ?idx, ?name }, "global");
    }

    for res in chunk.iter_code() {
        let Ok((pc, op)) = res else {
            trace!({ ?res }, "chunk error");
            break;
        };
        trace!({ ?pc, ?op }, "code");
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use rstest::rstest;

    use crate::bytecode::Chunk;
    use crate::parse::Parser;
    use crate::testing::snapshot_name;

    use super::{CompileErrors, Compiler};

    fn compile(source: &str) -> Result<Chunk, CompileErrors> {
        let ast = Parser::parse(source).unwrap();
        Compiler::compile(&ast)
    }

    #[rstest]
    fn test_programs(
        #[files("test_programs/*.blis")]
        #[files("test_programs/err_runtime/*.blis")]
        path: PathBuf,
    ) {
        let source = std::fs::read_to_string(&path).unwrap();
        let chunk = compile(&source).unwrap();
        let chunk = chunk.disassemble();

        insta::with_settings!({
            input_file => &path,
            description => source,
            omit_expression => true,
        }, {
            insta::assert_ron_snapshot!(snapshot_name(&path, "chunk"), chunk);
        })
    }

    #[rstest]
    fn test_compile_errors(#[files("test_programs/err_compile/*.blis")] path: PathBuf) {
        let source = std::fs::read_to_string(&path).unwrap();
        let errors = compile(&source).unwrap_err();

        insta::with_settings!({
            input_file => &path,
            description => source,
            omit_expression => true,
        }, {
            insta::assert_ron_snapshot!(snapshot_name(&path, "errors"), errors);
        })
    }
}
