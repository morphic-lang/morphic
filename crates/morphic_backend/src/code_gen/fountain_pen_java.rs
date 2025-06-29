use crate::code_gen::java_builder::{self as java, WriteTo};
use crate::code_gen::{fountain_pen, Error};
use id_collections::{id_type, IdVec};
use std::cell::{RefCell, RefMut};
use std::collections::BTreeMap;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::rc::Rc;

#[id_type]
pub struct TailTarget(u32);

#[id_type]
pub struct StructType(u32);

#[id_type]
pub struct VariantsType(u32);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Boolean,
    Byte,
    Int,
    Long,
    Double,
    String,
    Struct(StructType),
    Variants(VariantsType),
}

#[derive(Clone, Copy)]
enum StructOrVariants {
    Struct(StructType),
    Variants(VariantsType),
}

impl StructOrVariants {
    fn as_type(&self) -> Type {
        match self {
            StructOrVariants::Struct(ty) => Type::Struct(ty.clone()),
            StructOrVariants::Variants(ty) => Type::Variants(ty.clone()),
        }
    }
}

#[id_type]
pub struct GlobalValue(u32);

#[id_type]
pub struct FunctionValue(u32);

#[id_type]
pub struct Local(u32);

#[derive(Clone, Copy)]
pub enum Value {
    Local(Local),
    ConstBoolean(bool),
    ConstByte(u8),
    ConstInt(u32),
    ConstLong(u64),
    ConstDouble(f64),
}

#[id_type]
struct TailCase(u32);

#[derive(Clone)]
struct TailCaseData {
    arg_name: java::Ident,
    body: java::Block,
}

// Represented as a while loop and a switch e.g.
//
// function (arg) {
//   let tailCase = 2;
//   let case0Arg = ...;
//   let case1Arg = ...;
//
//   label: while (true) {
//     switch (tailCase) {
//       case 0:
//         do something with case0Arg
//         set tailCase to whatever we're tail calling next
//         continue label;
//       case 1:
//         do something with case1Arg
//         set tailCase to whatever we're tail calling next
//         continue label;
//       case 2:
//         the main body of the tail function
//         set tailCase to whatever we're tail calling next
//         continue label;
//     }
//   }
// }
#[derive(Clone)]
struct TailFunction {
    cases: IdVec<TailCase, TailCaseData>,
    body: java::Block,
    continue_label: java::Label,
    name: java::Ident,
    arg_tys: Vec<Type>,
    args: Vec<Local>,
    ret_ty: Option<Type>,
}

impl TailFunction {
    // fn to_java_method(&self, context: &mut ContextImpl) -> java::Method {
    //     let arg =  java::Arg {
    //             name: java::Ident(format!("arg")),
    //             ty: context.type_to_java_type(self.arg_ty),
    //         };

    //         let body = java::Block::new();

    //     let tail_func = java::Method {
    //         is_static: true,
    //         visibility: java::Visibility::Private,
    //         name: self.name.clone(),
    //         args: vec![arg],
    //         ret_ty: self.ret.map(|ty| context.type_to_java_type(ty)),
    //         body,
    //     };

    //     let func_id = context.functions.push(FunctionValueData::Function(tail_func));

    //     let case_var = context.fresh_ident("tailCase");
    //     let entry_case = self.cases.len();

    //     // Create argument variables for each case
    //     let mut case_arg_vars = Vec::new();
    //     for (case_id, case_data) in &self.cases {
    //         case_arg_vars.push((case_id, case_data.arg_name.clone()));
    //     }

    //     let mut cases = self
    //         .cases
    //         .iter()
    //         .map(|(i, x)| java::StmtCase {
    //             pat: java::Pat::IntLit(i.0 as i64),
    //             block: x.body.clone(),
    //         })
    //         .collect::<Vec<_>>();
    //     cases.push(java::StmtCase {
    //         pat: java::Pat::IntLit(entry_case.try_into().unwrap()),
    //         block: self.body.clone(),
    //     });

    //     let body = java::Block::new();
    //     let scope = MutScope {
    //         context: context,
    //         func: FunctionValue(())
    //         current_block: body,
    //     }

    //     // Declare the case variable (state)
    //     body.push(java::Stmt::DeclVar(java::DeclVar {
    //         name: case_var.clone(),
    //         ty: java::Type::int(),
    //         expr: java::Expr::IntLit(entry_case.try_into().unwrap()),
    //     }));

    //     // Declare argument variables for each case
    //     // For now, assuming each case has one argument of the first arg type
    //     // This should be adjusted based on your specific requirements
    //     for (_, arg_name) in &case_arg_vars {
    //         if !self.arg_ty.is_empty() {
    //             body.push(java::Stmt::DeclVar(java::DeclVar {
    //                 name: arg_name.clone(),
    //                 ty: context.type_to_java_type(self.arg_ty[0]), // Simplified - may need adjustment
    //                 expr: context. // context.type_to_java_type(self.args[0]).default_value(), // You'll need to implement default_value()
    //             }));
    //         }
    //     }

    //     // Create the while loop with switch
    //     body.push(java::Stmt::While(
    //         Some(self.continue_label.clone()),
    //         java::Expr::BooleanLit(true),
    //         java::Block::from_stmt(java::Stmt::Switch(java::Expr::Ident(case_var), cases, None)),
    //     ));

    // }
}

#[derive(Clone)]
struct Function {
    arg_tys: Vec<Type>,
    args: Vec<Local>,
    ret_ty: Option<Type>,
    method: java::Method,
}

#[derive(Clone)]
enum FunctionValueData {
    Function(Function),
    TailFunction(TailFunction),
}

impl FunctionValueData {
    fn arg_tys(&self) -> &[Type] {
        match self {
            FunctionValueData::Function(func) => &func.arg_tys,
            FunctionValueData::TailFunction(tail_func) => &tail_func.arg_tys,
        }
    }

    fn args(&self) -> &[Local] {
        match self {
            FunctionValueData::Function(func) => &func.args,
            FunctionValueData::TailFunction(tail_func) => &tail_func.args,
        }
    }

    fn ret_ty(&self) -> Option<Type> {
        match self {
            FunctionValueData::Function(func) => func.ret_ty,
            FunctionValueData::TailFunction(tail_func) => tail_func.ret_ty,
        }
    }

    fn name(&self) -> java::Ident {
        match self {
            FunctionValueData::Function(func) => func.method.name.clone(),
            FunctionValueData::TailFunction(tail_func) => tail_func.name.clone(),
        }
    }
}

#[derive(Clone)]
pub struct Context {
    inner: Rc<RefCell<ContextImpl>>,
}

struct ContextImpl {
    variants: IdVec<VariantsType, VariantsTypeData>,
    variants_interner: BTreeMap<Vec<Type>, VariantsType>,
    structs: IdVec<StructType, StructTypeData>,
    struct_interner: BTreeMap<Vec<Type>, StructType>,
    globals: IdVec<GlobalValue, java::Data>,
    functions: IdVec<FunctionValue, FunctionValueData>,
    tail_targets: IdVec<TailTarget, (FunctionValue, TailCase)>,
    locals: IdVec<Local, LocalData>,
    next_label_id: u32,
    next_var_id: u32,
}

struct StructTypeData {
    field_tys: Vec<Type>,
    field_sizes: Vec<u32>, // flat sizes of fields (in longs)
    total_size: u32,       // flat size of 'this'
    java_repr: java::Record,
}

impl StructTypeData {
    fn offset_of(&self, field_idx: u32) -> u32 {
        self.field_sizes[..field_idx as usize].iter().sum()
    }
}

struct VariantsTypeData {
    variants_tys: Vec<Type>,
    variant_sizes: Vec<u32>, // flat sizes of variants (in longs)
    total_size: u32,         // flat size of 'this' including the discriminant
    java_repr: java::Record,
}

struct LocalData {
    ty: Type,
    name: java::Ident,
}

#[derive(Clone)]
pub struct Scope {
    context: Context,
    func: FunctionValue,
    current_block: java::Block,
}

struct MutScope<'a> {
    // Use `downgrade` and `context` instead. Touch these fields directly at your own peril.
    #[allow(non_snake_case)]
    DONT_TOUCH_context_rc: Context,
    #[allow(non_snake_case)]
    DONT_TOUCH_context_ref: &'a RefCell<ContextImpl>,
    #[allow(non_snake_case)]
    DONT_TOUCH_context_ref_mut: Option<RefMut<'a, ContextImpl>>,

    func: FunctionValue,
    current_block: java::Block,
}

fn new_field(name: String) -> java::Arg {
    java::Arg {
        name: java::Ident(name),
        ty: java::Type::long(),
    }
}

impl Context {
    pub fn new() -> Self {
        Context {
            inner: Rc::new(RefCell::new(ContextImpl {
                variants: IdVec::new(),
                variants_interner: BTreeMap::new(),
                structs: IdVec::new(),
                struct_interner: BTreeMap::new(),
                globals: IdVec::new(),
                functions: IdVec::new(),
                tail_targets: IdVec::new(),
                locals: IdVec::new(),
                next_label_id: 0,
                next_var_id: 0,
            })),
        }
    }

    pub fn write_to(&self, w: &mut impl Write) -> Result<(), std::io::Error> {
        self.inner
            .borrow()
            .to_java_class()
            .write_to(&mut java::WriteContext::new(2), w)
    }
}

fn get_field_name(idx: u32) -> String {
    format!("field{idx}")
}

impl ContextImpl {
    fn to_java_class(&self) -> java::Class {
        let mut fields = Vec::new();

        fields.extend(
            self.variants
                .values()
                .map(|x| java::Field::Record(x.java_repr.clone())),
        );
        fields.extend(
            self.structs
                .values()
                .map(|x| java::Field::Record(x.java_repr.clone())),
        );
        fields.extend(self.globals.values().map(|x| java::Field::Data(x.clone())));
        fields.extend(self.functions.values().map(|x| match x {
            FunctionValueData::Function(func) => java::Field::Method(func.clone()),
            FunctionValueData::TailFunction(tail_func) => {
                java::Field::Method(tail_func.java_repr.clone())
            }
        }));

        java::Class {
            visibility: java::Visibility::Public,
            is_static: false,
            is_value: false,
            name: java::Ident("Main".to_string()),
            fields,
        }
    }

    fn fresh_ident(&mut self, s: &str) -> java::Ident {
        let id = self.next_var_id;
        self.next_var_id += 1;
        java::Ident(format!("x{id}_{s}"))
    }

    fn fresh_label(&mut self, s: &str) -> java::Label {
        let id = self.next_label_id;
        self.next_label_id += 1;
        java::Label(format!("l{id}_{s}"))
    }

    fn get_struct_type(&mut self, field_tys: &[Type]) -> StructType {
        if let Some(&result) = self.struct_interner.get(field_tys) {
            return result;
        }

        let name = format!("Struct{}", self.structs.len());
        let field_sizes = field_tys
            .iter()
            .map(|&ty| self.type_to_java_longs(ty))
            .collect::<Vec<_>>();
        let total_size = field_sizes.iter().sum();

        let data = (0..total_size)
            .map(|i| new_field(get_field_name(i)))
            .collect::<Vec<_>>();

        let java_repr = java::Record {
            visibility: java::Visibility::Private,
            is_static: true,
            is_value: true,
            name: java::Ident(name),
            data,
        };

        let struct_type = self.structs.push(StructTypeData {
            field_tys: field_tys.to_vec(),
            field_sizes,
            total_size,
            java_repr,
        });

        self.struct_interner.insert(field_tys.to_vec(), struct_type);
        struct_type
    }

    fn get_variants_type(&mut self, variant_tys: &[Type]) -> VariantsType {
        let name = format!("Variants{}", self.variants.len());
        let variant_sizes = variant_tys
            .iter()
            .map(|&ty| self.type_to_java_longs(ty))
            .collect::<Vec<_>>();
        let total_size = variant_sizes.iter().copied().max().unwrap_or(0) + 1;

        let data = (0..total_size)
            .map(|i| new_field(get_field_name(i)))
            .collect::<Vec<_>>();

        let java_repr = java::Record {
            visibility: java::Visibility::Private,
            is_static: true,
            is_value: true,
            name: java::Ident(name),
            data,
        };

        let variants_type = self.variants.push(VariantsTypeData {
            variants_tys: variant_tys.to_vec(),
            variant_sizes,
            total_size,
            java_repr,
        });

        self.variants_interner
            .insert(variant_tys.to_vec(), variants_type);
        variants_type
    }

    fn type_to_java_type(&self, ty: Type) -> java::Type {
        match ty {
            Type::Boolean => java::Type::boolean(),
            Type::Byte => java::Type::byte(),
            Type::Int => java::Type::int(),
            Type::Long => java::Type::long(),
            Type::Double => java::Type::double(),
            Type::Struct(ty) => java::Type::class(self.structs[ty].java_repr.name.clone()),
            Type::Variants(ty) => java::Type::class(self.variants[ty].java_repr.name.clone()),
            Type::String => java::Type::class(java::Ident("String".to_string())),
        }
    }

    fn get_type_of_value(&self, val: Value) -> Type {
        match val {
            Value::Local(local) => self.locals[local].ty,
            Value::ConstBoolean(_) => Type::Boolean,
            Value::ConstByte(_) => Type::Byte,
            Value::ConstInt(_) => Type::Int,
            Value::ConstLong(_) => Type::Long,
            Value::ConstDouble(_) => Type::Double,
        }
    }

    fn type_to_java_longs(&self, ty: Type) -> u32 {
        match ty {
            Type::Boolean | Type::Byte | Type::Int | Type::Long | Type::Double => 1,
            Type::Struct(struct_type) => self.structs[struct_type].total_size,
            Type::Variants(variants_type) => self.variants[variants_type].total_size,
            Type::String => panic!("unsupported type: String"),
        }
    }

    fn value_to_java_expr(&self, val: Value) -> java::Expr {
        match val {
            Value::Local(local) => java::Expr::Ident(self.locals[local].name.clone()),
            Value::ConstBoolean(val) => java::Expr::BooleanLit(val),
            Value::ConstByte(val) => java::Expr::ByteLit(val),
            Value::ConstInt(val) => java::Expr::IntLit(val),
            Value::ConstLong(val) => java::Expr::LongLit(val),
            Value::ConstDouble(val) => java::Expr::DoubleLit(val),
        }
    }
}

impl<'a> MutScope<'a> {
    fn context(&mut self) -> &mut ContextImpl {
        self.DONT_TOUCH_context_ref_mut.as_deref_mut().unwrap()
    }

    fn downgrade<R>(&mut self, f: impl FnOnce(&Scope) -> R) -> R {
        self.DONT_TOUCH_context_ref_mut = None;
        let scope = Scope {
            context: self.DONT_TOUCH_context_rc.clone(),
            func: self.func,
            current_block: self.current_block.clone(),
        };

        let result = f(&scope);

        let new_ref = self.DONT_TOUCH_context_ref.borrow_mut();
        self.DONT_TOUCH_context_ref_mut = Some(new_ref);
        result
    }

    fn downgrade_with<R>(&mut self, block: &mut java::Block, f: impl FnOnce(&Scope) -> R) -> R {
        std::mem::swap(&mut self.current_block, block);
        let result = self.downgrade(f);
        std::mem::swap(&mut self.current_block, block);
        result
    }

    fn new_stmt_unsafe(&mut self, unsafe_fun_name: &str, arg: &[Value], ret_type: Type) -> Value {
        let args_exprs: Vec<java::Expr> = arg
            .iter()
            .map(|&v| self.context().value_to_java_expr(v))
            .collect();

        self.new_stmt_nullary(
            "result",
            java::Expr::MethodCall(
                Box::new(java::Expr::Ident(java::Ident("unsafe".to_string()))),
                java::Ident(unsafe_fun_name.to_string()),
                args_exprs,
            ),
            ret_type,
        )
    }

    fn new_stmt_unsafe_void(&mut self, unsafe_fun_name: &str, arg: &[Value]) {
        let args_exprs: Vec<java::Expr> = arg
            .iter()
            .map(|&v| self.context().value_to_java_expr(v))
            .collect();

        self.current_block
            .push(java::Stmt::Expr(java::Expr::MethodCall(
                Box::new(java::Expr::Ident(java::Ident("unsafe".to_string()))),
                java::Ident(unsafe_fun_name.to_string()),
                args_exprs,
            )));
    }

    fn new_stmt_nullary(&mut self, name: &str, expr: java::Expr, ty_: Type) -> Value {
        let name = self.context().fresh_ident(name);
        let ty = self.context().type_to_java_type(ty_);

        self.current_block.push(java::Stmt::DeclVar(java::DeclVar {
            name: name.clone(),
            ty,
            expr,
        }));

        Value::Local(self.context().locals.push(LocalData { ty: ty_, name }))
    }

    fn new_stmt_unary(
        &mut self,
        name: &str,
        arg: Value,
        expr: impl FnOnce(java::Expr) -> java::Expr,
        ret_ty: Type,
    ) -> Value {
        let name = self.context().fresh_ident(name);
        let ty = self.context().type_to_java_type(ret_ty);
        let arg = self.context().value_to_java_expr(arg);

        self.current_block.push(java::Stmt::DeclVar(java::DeclVar {
            name: name.clone(),
            ty,
            expr: expr(arg),
        }));

        Value::Local(self.context().locals.push(LocalData { ty: ret_ty, name }))
    }

    fn new_stmt_binary(
        &mut self,
        name: &str,
        arg1: Value,
        arg2: Value,
        expr: impl FnOnce(java::Expr, java::Expr) -> java::Expr,
        ret_ty_: Type,
    ) -> Value {
        let name = self.context().fresh_ident(name);
        let ret_ty = self.context().type_to_java_type(ret_ty_);
        let arg1 = self.context().value_to_java_expr(arg1);
        let arg2 = self.context().value_to_java_expr(arg2);

        self.current_block.push(java::Stmt::DeclVar(java::DeclVar {
            name: name.clone(),
            ty: ret_ty,
            expr: expr(arg1, arg2),
        }));

        Value::Local(self.context().locals.push(LocalData { ty: ret_ty_, name }))
    }

    fn new_stmt_nary(
        &mut self,
        name: &str,
        args: &[Value],
        expr: impl FnOnce(Vec<java::Expr>) -> java::Expr,
        ret_ty: Type,
    ) -> Value {
        let name = self.context().fresh_ident(name);
        let ty = self.context().type_to_java_type(ret_ty);
        let args = args
            .iter()
            .map(|&arg| self.context().value_to_java_expr(arg))
            .collect::<Vec<_>>();

        self.current_block.push(java::Stmt::DeclVar(java::DeclVar {
            name: name.clone(),
            ty,
            expr: expr(args),
        }));

        Value::Local(self.context().locals.push(LocalData { ty: ret_ty, name }))
    }

    fn make_record_from_longs(&mut self, ty: StructOrVariants, fields: &[Value]) -> Value {
        let (record_name, total_size) = match ty {
            StructOrVariants::Struct(ty) => {
                let data = &self.context().structs[ty];
                (data.java_repr.name.clone(), data.total_size)
            }
            StructOrVariants::Variants(ty) => {
                let data = &self.context().variants[ty];
                (data.java_repr.name.clone(), data.total_size)
            }
        };
        assert_eq!(total_size as usize, fields.len());
        let binding_name = self.context().fresh_ident("longs");
        let fields = fields
            .iter()
            .map(|&v| self.context().value_to_java_expr(v))
            .collect::<Vec<_>>();
        let expr = java::DeclVar {
            name: binding_name.clone(),
            ty: java::Type::class(record_name.clone()),
            expr: java::Expr::New(java::Type::class(record_name), fields),
        };
        self.current_block.push(java::Stmt::DeclVar(expr));
        Value::Local(self.context().locals.push(LocalData {
            ty: ty.as_type(),
            name: binding_name,
        }))
    }

    fn make_undef(&mut self, ty: Type) -> Value {
        match ty {
            Type::Boolean => Value::ConstBoolean(false),
            Type::Byte => Value::ConstByte(0),
            Type::Int => Value::ConstInt(0),
            Type::Long => Value::ConstLong(0),
            Type::Double => Value::ConstDouble(0.0),
            Type::String => panic!("unsupported type: String"),
            Type::Struct(struct_type) => {
                let struct_type_data = &self.context().structs[struct_type];
                let fields = (0..struct_type_data.total_size)
                    .map(|_| Value::ConstLong(0))
                    .collect::<Vec<_>>();
                self.make_record_from_longs(StructOrVariants::Struct(struct_type), &fields)
            }
            Type::Variants(variants_type) => {
                let variants_type_data = &self.context().variants[variants_type];
                let variants = (0..variants_type_data.total_size)
                    .map(|_| Value::ConstLong(0))
                    .collect::<Vec<_>>();
                self.make_record_from_longs(StructOrVariants::Variants(variants_type), &variants)
            }
        }
    }

    fn get_struct_field(
        &mut self,
        struct_ty: StructType,
        idx: u32,
        mut get_long: impl FnMut(&mut Self, u32) -> java::Expr,
    ) -> Value {
        let struct_ty_data = &self.context().structs[struct_ty];
        let field_ty = struct_ty_data.field_tys[idx as usize];
        let start_offset = struct_ty_data.offset_of(idx);
        let expr = match field_ty {
            Type::Boolean => java::Expr::Cast(
                java::Type::boolean(),
                Box::new(get_long(self, start_offset)),
            ),
            Type::Byte => {
                java::Expr::Cast(java::Type::byte(), Box::new(get_long(self, start_offset)))
            }
            Type::Int => {
                java::Expr::Cast(java::Type::int(), Box::new(get_long(self, start_offset)))
            }
            Type::Long => get_long(self, start_offset),
            Type::Double => {
                java::Expr::Cast(java::Type::double(), Box::new(get_long(self, start_offset)))
            }
            Type::String => panic!("unsupported type: String"),
            Type::Struct(nested_struct_ty) => {
                let nested_struct_data = &self.context().structs[nested_struct_ty];
                let field_size = nested_struct_data.total_size;
                let args = (0..field_size)
                    .map(|i| get_long(self, start_offset + i))
                    .collect();
                java::Expr::New(
                    self.context()
                        .type_to_java_type(Type::Struct(nested_struct_ty)),
                    args,
                )
            }
            Type::Variants(variants_ty) => {
                let variants_data = &self.context().variants[variants_ty];
                let field_size = variants_data.total_size;
                let args = (0..field_size)
                    .map(|i| get_long(self, start_offset + i))
                    .collect();
                java::Expr::New(
                    self.context()
                        .type_to_java_type(Type::Variants(variants_ty)),
                    args,
                )
            }
        };

        self.new_stmt_nullary("get_struct_field", expr, field_ty)
    }

    fn get_struct_field_stack(
        &mut self,
        struct_ty: StructType,
        idx: u32,
        struct_val: Value,
    ) -> Value {
        let struct_val_expr = Box::new(self.context().value_to_java_expr(struct_val));
        self.get_struct_field(struct_ty, idx, |i, _| {
            java::Expr::Field(struct_val_expr.clone(), java::Ident(get_field_name(i)))
        })
    }

    fn get_struct_field_heap(
        &mut self,
        struct_ty: StructType,
        idx: u32,
        base_pointer: Value,
    ) -> Value {
        self.get_struct_field(struct_ty, idx, |scope, i| {
            let offset = i64(8 * i as u64);
            let ptr_plus_offset = scope.add(base_pointer, offset);
            let expr = scope.new_stmt_unsafe("getLong", &[ptr_plus_offset], Type::Long);
            scope.context().value_to_java_expr(expr)
        })
    }

    fn undef(&mut self, ty: Type) -> Value {
        match ty {
            Type::Boolean => Value::ConstBoolean(false),
            Type::Byte => Value::ConstByte(0),
            Type::Int => Value::ConstInt(0),
            Type::Long => Value::ConstLong(0),
            Type::Double => Value::ConstDouble(0.0),
            Type::String => panic!("unsupported type: String"),
            Type::Struct(struct_type) => {
                let field_tys = &self.context().structs[struct_type].field_tys;
                let field_vals = field_tys
                    .iter()
                    .map(|ty| self.undef(*ty))
                    .collect::<Vec<_>>();
                let name = self.context().structs[struct_type].java_repr.name.clone();
                self.make_record_from_longs(name, &field_vals)
            }
            Type::Variants(_) => todo!(),
        }
    }

    fn str(&mut self, s: &str) -> Value {
        self.new_stmt_nullary("str", java::Expr::StringLit(s.to_string()), Type::String)
    }

    fn arg(&mut self, idx: u32) -> Value {
        let func_id = self.func;
        let func = &self.context().functions[func_id];
        Value::Local(func.args()[idx as usize])
    }

    fn tail_arg(&mut self) -> Value {
        // TODO: implement tail arguments
        unimplemented!("tail_arg not yet implemented")
    }

    fn call(&mut self, fn_value: FunctionValue, args: &[Value]) -> Value {
        let name = self.context().functions[fn_value].name();
        let ret_ty = self.context().functions[fn_value].ret_ty();
        self.new_stmt_nary(
            "call_result",
            args,
            |args| java::Expr::Call(name, args),
            ret_ty.unwrap(),
        )
    }

    fn call_void(&mut self, fn_value: FunctionValue, args: &[Value]) {
        let name = self.context().functions[fn_value].name();
        let ret_ty = self.context().functions[fn_value].ret_ty();
        if ret_ty.is_some() {
            panic!()
        }

        let name = self.context().fresh_ident("call_void");
        let args = args
            .iter()
            .map(|&arg| self.context().value_to_java_expr(arg))
            .collect::<Vec<_>>();

        self.current_block
            .push(java::Stmt::Expr(java::Expr::Call(name, args)));
    }

    fn tail_call(&mut self, _called: TailTarget, _arg: Value) -> Value {
        // TODO: implement tail calls
        unimplemented!("tail_call not yet implemented")
    }

    fn gep(&mut self, _struct_ty: Type, _struct_ptr: Value, _idx: u32) -> Value {
        // TODO: implement struct field access
        let temp_name = self.context_handle.next_temp_name();
        let value_id = self
            .context_handle
            .inner
            .borrow_mut()
            .locals
            .push(java::Ident(temp_name));
        Value(value_id.0)
    }

    fn arrow(&mut self, _struct_ty: Type, _field_ty: Type, _struct_ptr: Value, _idx: u32) -> Value {
        // TODO: implement field access
        let temp_name = self.context_handle.next_temp_name();
        let value_id = self
            .context_handle
            .inner
            .borrow_mut()
            .locals
            .push(java::Ident(temp_name));
        Value(value_id.0)
    }

    fn field(&mut self, _struct_val: Value, _idx: u32) -> Value {
        // TODO: implement field extraction
        let temp_name = self.context_handle.next_temp_name();
        let value_id = self
            .context_handle
            .inner
            .borrow_mut()
            .locals
            .push(java::Ident(temp_name));
        Value(value_id.0)
    }

    fn arrow_set(&mut self, _struct_ty: Type, _struct_ptr: Value, _idx: u32, _new_data: Value) {
        // TODO: implement field assignment
    }

    fn if_(&mut self, _cond: Value, _body: impl FnOnce(&mut self)) {
        // TODO: implement if statements
    }

    fn if_else(&mut self, _cond: Value, mut _body: impl FnMut(&mut self, bool)) {
        // TODO: implement if-else statements
    }

    fn if_expr(&mut self, _cond: Value, mut _body: impl FnMut(&mut self, bool) -> Value) -> Value {
        // TODO: implement if expressions
        let temp_name = self.context_handle.next_temp_name();
        let value_id = self
            .context_handle
            .inner
            .borrow_mut()
            .locals
            .push(java::Ident(temp_name));
        Value(value_id.0)
    }

    fn ternary(&mut self, _cond: Value, _then_value: Value, _else_value: Value) -> Value {
        // TODO: implement ternary operator
        let temp_name = self.context_handle.next_temp_name();
        let value_id = self
            .context_handle
            .inner
            .borrow_mut()
            .locals
            .push(java::Ident(temp_name));
        Value(value_id.0)
    }

    fn int_cast(&mut self, _result_type: Type, int: Value) -> Value {
        // only ever used to cast from i64 to usize
        int
    }

    fn make_struct(&mut self, _fields: &[Value]) -> Value {
        // TODO: implement tuple creation
        let temp_name = self.context_handle.next_temp_name();
        let value_id = self
            .context_handle
            .inner
            .borrow_mut()
            .locals
            .push(java::Ident(temp_name));
        Value(value_id.0)
    }

    fn buf_addr(&mut self, _pointee_ty: Type, _arr: Value, _idx: Value) -> Value {
        // TODO: implement buffer address calculation
        let temp_name = self.context_handle.next_temp_name();
        let value_id = self
            .context_handle
            .inner
            .borrow_mut()
            .locals
            .push(java::Ident(temp_name));
        Value(value_id.0)
    }

    fn buf_addr_oob(&mut self, _pointee_ty: Type, _arr: Value, _idx: Value) -> Value {
        // TODO: implement buffer address calculation (out of bounds)
        let temp_name = self.context_handle.next_temp_name();
        let value_id = self
            .context_handle
            .inner
            .borrow_mut()
            .locals
            .push(java::Ident(temp_name));
        Value(value_id.0)
    }

    fn buf_set(&mut self, _pointee_ty: Type, _arr: Value, _idx: Value, _val: Value) {
        // TODO: implement buffer element assignment
    }

    fn buf_get(&mut self, _pointee_ty: Type, _arr: Value, _idx: Value) -> Value {
        // TODO: implement buffer element access
        let temp_name = self.context_handle.next_temp_name();
        let value_id = self
            .context_handle
            .inner
            .borrow_mut()
            .locals
            .push(java::Ident(temp_name));
        Value(value_id.0)
    }

    fn for_(&mut self, bound: Value, body: impl FnOnce(&Scope, Value)) {
        let (count, stmt, mut block) = {
            let count_name = inner.fresh_ident("i");
            let bound_expr = inner.value_to_java_expr(bound);

            let init = java::DeclVar {
                name: count_name.clone(),
                ty: java::Type::long(),
                expr: java::Expr::LongLit(0),
            };

            let count = inner.locals.push(LocalData {
                ty: Type::Long,
                name: count_name.clone(),
            });

            let cond = java::Expr::BinOp(
                java::BinOp::Lt,
                Box::new(java::Expr::Ident(count_name.clone())),
                Box::new(bound_expr),
            );

            let incr = java::Expr::Assign(
                Box::new(java::Expr::Ident(count_name.clone())),
                Box::new(java::Expr::BinOp(
                    java::BinOp::Add,
                    Box::new(java::Expr::Ident(count_name)),
                    Box::new(java::Expr::LongLit(1)),
                )),
            );

            let block = java::Block::new();
            (
                count,
                java::Stmt::For(None, init, cond, incr, block.clone()),
                block,
            )
        };

        self.downgrade_with(&mut block, |scope| body(scope, Value::Local(count)));
        self.current_block.push(stmt);
    }

    // fn get_struct_field(
    //     &mut self,
    //     struct_ty: StructType,
    //     idx: u32,
    //     mut get_long: impl FnMut(&mut Self, u32) -> java::Expr,
    // ) -> Value {

    fn ptr_set(&mut self, ptr: Value, val: Value) {
        let pointee_ty = self.context().get_type_of_value(val);
        match pointee_ty {
            Type::Boolean => self.new_stmt_unsafe_void("putBoolean", &[ptr, val]),
            Type::Byte => self.new_stmt_unsafe_void("putByte", &[ptr, val]),
            Type::Int => self.new_stmt_unsafe_void("putInt", &[ptr, val]),
            Type::Long => self.new_stmt_unsafe_void("putLong", &[ptr, val]),
            Type::Double => self.new_stmt_unsafe_void("putDouble", &[ptr, val]),
            Type::String => panic!("unsupported type: String"),
            Type::Struct(struct_type) => todo!(),
            Type::Variants(variants_type) => todo!(),
        };
    }

    fn ptr_get(&mut self, pointee_ty: Type, ptr: Value) -> Value {
        match pointee_ty {
            Type::Boolean => self.new_stmt_unsafe("getBoolean", &[ptr], Type::Boolean),
            Type::Byte => self.new_stmt_unsafe("getByte", &[ptr], Type::Byte),
            Type::Int => self.new_stmt_unsafe("getInt", &[ptr], Type::Int),
            Type::Long => self.new_stmt_unsafe("getLong", &[ptr], Type::Long),
            Type::Double => self.new_stmt_unsafe("getDouble", &[ptr], Type::Double),
            Type::String => panic!("unsupported type: String"),
            Type::Struct(struct_type) => {
                let num_fields = self.context().structs[struct_type].field_tys.len();
                let fields = (0..num_fields)
                    .map(|i| self.get_struct_field_heap(struct_type, i as u32, ptr))
                    .collect::<Vec<_>>();
                self.make_struct(&fields)
            }

            Type::Variants(variants_type) => {}
        }
    }

    fn global_set(&mut self, ptr: GlobalValue, val: Value) {
        let name = self.context().globals[ptr].name.clone();
        let val_expr = self.context().value_to_java_expr(val);
        self.current_block.push(java::Stmt::Expr(java::Expr::Assign(
            Box::new(java::Expr::Ident(name)),
            Box::new(val_expr),
        )));
    }

    fn global_get(&mut self, pointee_ty: Type, ptr: GlobalValue) -> Value {
        let name = self.context().globals[ptr].name.clone();
        self.new_stmt_nullary("global_get", java::Expr::Ident(name), pointee_ty)
    }

    fn panic(&mut self, panic_string: &str, panic_args: &[Value]) {
        let panic_str = java::Expr::StringLit(panic_string.to_string());
        let panic_fn_name = "panic";
        let panic_fn_call = java::Expr::Call(panic_fn_name, vec![panic_str]);
        self.current_block.push(java::Stmt::Expr(panic_fn_call));
    }

    fn print(&mut self, _message: &str, _message_args: &[Value]) {
        // TODO: implement print
    }

    fn debug(&mut self, _message: &str, _message_args: &[Value]) {
        // TODO: implement debug print
    }

    fn malloc(&mut self, num: Value, ty: Type) -> Value {
        let sizeof_expr = self.mul(self.size(ty), num);

        self.new_stmt_unsafe("allocateMemory", &[sizeof_expr], i64_t())
    }

    fn calloc(&mut self, num: Value, ty: Type) -> Value {
        let sizeof_expr = self.mul(self.size(ty), num);

        let allocate_call = self.new_stmt_unsafe("allocateMemory", &[sizeof_expr], i64_t());

        self.new_stmt_unsafe(
            "setMemory",
            &[allocate_call, sizeof_expr, self.i8(0)],
            Type::Boolean,
        );

        allocate_call
    }

    fn free(&mut self, _ptr: Value) {
        self.new_stmt_unsafe("freeMemory", &[_ptr], Type::Boolean);
    }

    fn is_null(&mut self, ptr: Value) -> Value {
        let zero = self.i64(0);
        self.eq(ptr, zero)
    }

    fn variants_new_discrim(&mut self, _ty: Type, _idx: u32) -> Value {
        // TODO: implement variant discriminant creation
        let temp_name = self.context_handle.next_temp_name();
        let value_id = self
            .context_handle
            .inner
            .borrow_mut()
            .locals
            .push(java::Ident(temp_name));
        Value(value_id.0)
    }

    fn variants_get_discrim(&mut self, _val: Value) -> Value {
        // TODO: implement variant discriminant extraction
        let temp_name = self.context_handle.next_temp_name();
        let value_id = self
            .context_handle
            .inner
            .borrow_mut()
            .locals
            .push(java::Ident(temp_name));
        Value(value_id.0)
    }

    fn variants_new(&mut self, _ty: &VariantsType, _val: Value, _idx: u32) -> Value {
        // TODO: implement variant creation
        let temp_name = self.context_handle.next_temp_name();
        let value_id = self
            .context_handle
            .inner
            .borrow_mut()
            .locals
            .push(java::Ident(temp_name));
        Value(value_id.0)
    }

    fn variants_get(&mut self, _ty: &VariantsType, _val: Value, _idx: u32) -> Value {
        // TODO: implement variant extraction
        let temp_name = self.context_handle.next_temp_name();
        let value_id = self
            .context_handle
            .inner
            .borrow_mut()
            .locals
            .push(java::Ident(temp_name));
        Value(value_id.0)
    }

    fn variants_switch(
        &mut self,
        _ty: &VariantsType,
        _val: Value,
        mut _cases: impl FnMut(&mut self, u32, Value),
    ) {
        // TODO: implement variant switch
    }

    fn ret_void(&mut self) {
        self.current_block.push(java::Stmt::Return(None));
    }

    fn ret(&mut self, ret_val: Value) {
        let expr = self.context().value_to_java_expr(ret_val);
        self.current_block.push(java::Stmt::Return(Some(expr)));
    }

    fn size(&mut self, ty: Type) -> Value {
        let result: u32 = match ty {
            // everything is a long
            Type::Boolean => 1,
            Type::Byte => 1,
            Type::Int => 4,
            Type::Long => 8,
            Type::Double => 8,
            Type::String => panic!("don't put a string into an array"),
            Type::Struct(struct_type) => {
                let struct_data = &self.context().structs[struct_type];
                struct_data.total_size * 8
            }
            Type::Variants(variants_type) => {
                let variants_data = &self.context().variants[variants_type];
                variants_data.total_size * 8
            }
        };

        i32(result)
    }

    fn unreachable(&mut self) {
        self.current_block.push(java::Stmt::Expr(java::Expr::call(
            "System",
            "exit",
            vec![java::Expr::IntLit(1)],
        )));
    }

    fn alloca(&mut self, ty: Type) -> Value {
        let undef = self.undef(ty);
        let undef_expr = self.context().value_to_java_expr(undef);
        self.new_stmt_nullary("alloca", undef_expr, ty)
    }

    fn while_(&mut self, cond: impl FnOnce(&Scope) -> Value, body: impl FnOnce(&Scope)) {
        let while_label = self.context().fresh_label("while");
        let mut while_block = java::Block::new();

        let cond_value = self.downgrade_with(&mut while_block, cond);
        let cond_expr = self.context().value_to_java_expr(cond_value);

        let if_block = java::Block::new();
        if_block.push(java::Stmt::Break(Some(while_label.clone())));
        while_block.push(java::Stmt::If(cond_expr, if_block, None));

        self.downgrade_with(&mut while_block, body);
        self.current_block.push(java::Stmt::While(
            Some(while_label),
            java::Expr::BooleanLit(true),
            while_block,
        ));
    }

    // Integer operations

    fn eq(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "eq",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Eq, Box::new(a), Box::new(b)),
            Type::Boolean,
        )
    }

    fn ne(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "ne",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Ne, Box::new(a), Box::new(b)),
            Type::Boolean,
        )
    }

    fn slt(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "slt",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Lt, Box::new(a), Box::new(b)),
            Type::Boolean,
        )
    }

    fn sle(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "sle",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Le, Box::new(a), Box::new(b)),
            Type::Boolean,
        )
    }

    fn sgt(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "sgt",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Gt, Box::new(a), Box::new(b)),
            Type::Boolean,
        )
    }

    fn sge(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "sge",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Ge, Box::new(a), Box::new(b)),
            Type::Boolean,
        )
    }

    fn ult(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "ult",
            arg1,
            arg2,
            |a, b| {
                java::Expr::BinOp(
                    java::BinOp::Lt,
                    Box::new(java::Expr::call("Integer", "compareUnsigned", vec![a, b])),
                    Box::new(java::Expr::IntLit(0)),
                )
            },
            Type::Boolean,
        )
    }

    fn ule(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "ule",
            arg1,
            arg2,
            |a, b| {
                java::Expr::BinOp(
                    java::BinOp::Le,
                    Box::new(java::Expr::call("Integer", "compareUnsigned", vec![a, b])),
                    Box::new(java::Expr::IntLit(0)),
                )
            },
            Type::Boolean,
        )
    }

    fn ugt(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "ugt",
            arg1,
            arg2,
            |a, b| {
                java::Expr::BinOp(
                    java::BinOp::Gt,
                    Box::new(java::Expr::call("Integer", "compareUnsigned", vec![a, b])),
                    Box::new(java::Expr::IntLit(0)),
                )
            },
            Type::Boolean,
        )
    }

    fn uge(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "uge",
            arg1,
            arg2,
            |a, b| {
                java::Expr::BinOp(
                    java::BinOp::Ge,
                    Box::new(java::Expr::call("Integer", "compareUnsigned", vec![a, b])),
                    Box::new(java::Expr::IntLit(0)),
                )
            },
            Type::Boolean,
        )
    }

    fn sdiv(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "sdiv",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Div, Box::new(a), Box::new(b)),
            Type::Long,
        )
    }

    fn srem(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "srem",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Rem, Box::new(a), Box::new(b)),
            Type::Long,
        )
    }

    fn udiv(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "udiv",
            arg1,
            arg2,
            |a, b| java::Expr::call("Integer", "divideUnsigned", vec![a, b]),
            Type::Long,
        )
    }

    fn urem(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "urem",
            arg1,
            arg2,
            |a, b| java::Expr::call("Integer", "remainderUnsigned", vec![a, b]),
            Type::Long,
        )
    }

    fn neg(&mut self, arg: Value) -> Value {
        self.new_stmt_unary(
            "neg",
            arg,
            |a| java::Expr::UnOp(java::UnOp::Neg, Box::new(a)),
            Type::Long,
        )
    }

    fn add(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "add",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Add, Box::new(a), Box::new(b)),
            Type::Long,
        )
    }

    fn sub(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "sub",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Sub, Box::new(a), Box::new(b)),
            Type::Long,
        )
    }

    fn mul(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "mul",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Mul, Box::new(a), Box::new(b)),
            Type::Long,
        )
    }

    // Floating point operations

    fn oeq(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "oeq",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Eq, Box::new(a), Box::new(b)),
            Type::Boolean,
        )
    }

    fn one(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "one",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Ne, Box::new(a), Box::new(b)),
            Type::Boolean,
        )
    }

    fn olt(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "olt",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Lt, Box::new(a), Box::new(b)),
            Type::Boolean,
        )
    }

    fn ole(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "ole",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Le, Box::new(a), Box::new(b)),
            Type::Boolean,
        )
    }

    fn ogt(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "ogt",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Gt, Box::new(a), Box::new(b)),
            Type::Boolean,
        )
    }

    fn oge(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "oge",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Ge, Box::new(a), Box::new(b)),
            Type::Boolean,
        )
    }

    fn fneg(&mut self, arg: Value) -> Value {
        self.new_stmt_unary(
            "fneg",
            arg,
            |a| java::Expr::UnOp(java::UnOp::Neg, Box::new(a)),
            Type::Double,
        )
    }

    fn fadd(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "fadd",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Add, Box::new(a), Box::new(b)),
            Type::Double,
        )
    }

    fn fsub(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "fsub",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Sub, Box::new(a), Box::new(b)),
            Type::Double,
        )
    }

    fn fmul(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "fmul",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Mul, Box::new(a), Box::new(b)),
            Type::Double,
        )
    }

    fn fdiv(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "fdiv",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Div, Box::new(a), Box::new(b)),
            Type::Double,
        )
    }

    // Bitwise operations

    fn sll(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "sll",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Sll, Box::new(a), Box::new(b)),
            Type::Long,
        )
    }

    fn srl(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "srl",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::Srl, Box::new(a), Box::new(b)),
            Type::Long,
        )
    }

    fn and(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "and",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::BitAnd, Box::new(a), Box::new(b)),
            Type::Long,
        )
    }

    fn or(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "or",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::BitOr, Box::new(a), Box::new(b)),
            Type::Long,
        )
    }

    fn not(&mut self, arg: Value) -> Value {
        self.new_stmt_unary(
            "not",
            arg,
            |a| java::Expr::UnOp(java::UnOp::BitNot, Box::new(a)),
            Type::Long,
        )
    }

    fn xor(&mut self, arg1: Value, arg2: Value) -> Value {
        self.new_stmt_binary(
            "xor",
            arg1,
            arg2,
            |a, b| java::Expr::BinOp(java::BinOp::BitXor, Box::new(a), Box::new(b)),
            Type::Long,
        )
    }

    fn z_extend(&mut self, value: Value) -> Value {
        self.new_stmt_unary(
            "z_extend",
            value,
            |a| {
                // casting does sign extension, so we have to mask the top bits
                java::Expr::BinOp(
                    java::BinOp::BitAnd,
                    Box::new(java::Expr::Cast(
                        java::Type::Val(java::ValType::Long),
                        Box::new(a),
                    )),
                    Box::new(java::Expr::LongLit(0xffff_ffff_ffff_fff0)),
                )
            },
            Type::Long,
        )
    }

    fn s_extend(&mut self, value: Value) -> Value {
        self.new_stmt_unary(
            "s_extend",
            value,
            |a| java::Expr::Cast(java::Type::Val(java::ValType::Long), Box::new(a)),
            Type::Long,
        )
    }

    fn truncate(&mut self, value: Value) -> Value {
        self.new_stmt_unary(
            "truncate",
            value,
            |a| java::Expr::Cast(java::Type::Val(java::ValType::Byte), Box::new(a)),
            Type::Byte,
        )
    }

    fn ctpop(&mut self, arg: Value) -> Value {
        self.new_stmt_unary(
            "ctpop",
            arg,
            |a| java::Expr::call("Integer", "bitCount", vec![a]),
            Type::Long,
        )
    }

    fn ctlz(&mut self, arg: Value) -> Value {
        self.new_stmt_unary(
            "ctlz",
            arg,
            |a| java::Expr::call("Integer", "numberOfLeadingZeros", vec![a]),
            Type::Long,
        )
    }

    fn cttz(&mut self, arg: Value) -> Value {
        self.new_stmt_unary(
            "cttz",
            arg,
            |a| java::Expr::call("Integer", "numberOfTrailingZeros", vec![a]),
            Type::Long,
        )
    }
}

impl Scope {
    fn upgrade<'a>(&'a self) -> MutScope<'a> {
        MutScope {
            context_rc: self.context.clone(),
            context_ref: &self.context.inner,
            context_ref_mut: Some(self.context.inner.borrow_mut()),
            func: self.func,
            current_block: self.current_block.clone(),
        }
    }
}

fn i1_t() -> Type {
    Type::Boolean
}

fn i8_t() -> Type {
    Type::Byte
}

fn i32_t() -> Type {
    Type::Int
}

fn i64_t() -> Type {
    Type::Long
}

fn usize_t() -> Type {
    Type::Long
}

fn f64_t() -> Type {
    Type::Double
}

fn ptr_t() -> Type {
    Type::Long
}

fn i1(val: bool) -> Value {
    Value::ConstBoolean(val)
}

fn i8(val: u8) -> Value {
    Value::ConstByte(val)
}

fn i32(val: u32) -> Value {
    Value::ConstInt(val)
}

fn i64(val: u64) -> Value {
    Value::ConstLong(val)
}

fn usize(val: u64) -> Value {
    Value::ConstLong(val)
}

fn f64(val: f64) -> Value {
    Value::ConstDouble(val)
}

fn null() -> Value {
    Value::ConstLong(0)
}

impl fountain_pen::Context for Context {
    type Scope = Scope;
    type TailTarget = TailTarget;
    type VariantsType = VariantsType;
    type Type = Type;
    type GlobalValue = GlobalValue;
    type FunctionValue = FunctionValue;
    type Value = Value;
    type ProfileRc = ProfileRc;
    type Tal = Tal;

    fn tal(&self) -> &Self::Tal {
        todo!()
    }

    fn declare_main_func(&self) -> Self::FunctionValue {
        let mut inner = self.inner.borrow_mut();

        let method = java::Method {
            is_static: true,
            visibility: java::Visibility::Public,
            name: java::Ident("main".to_string()),
            args: vec![java::Arg {
                name: java::Ident("args".to_string()),
                ty: java::Type::class(java::Ident("String".to_string())).array(),
            }],
            ret_ty: None,
            body: java::Block::new(),
        };

        inner.functions.push(FunctionValueData::Function(method))
    }

    fn declare_func(
        &self,
        name: &str,
        arg_tys: &[Self::Type],
        ret_ty: Option<Self::Type>,
    ) -> Self::FunctionValue {
        let mut inner = self.inner.borrow_mut();

        let arg_tys = arg_tys
            .iter()
            .enumerate()
            .map(|(i, &arg_ty)| java::Arg {
                name: java::Ident(format!("arg{i}")),
                ty: inner.type_to_java_type(arg_ty),
            })
            .collect();

        let method = java::Method {
            is_static: true,
            visibility: java::Visibility::Private,
            name: inner.fresh_ident(name),
            args: arg_tys,
            ret_ty: ret_ty.map(|ty| inner.type_to_java_type(ty)),
            body: java::Block::new(),
        };

        inner.functions.push(FunctionValueData::Function(method))
    }

    fn declare_tail_func(
        &self,
        name: &str,
        arg_tys: &[Self::Type],
        ret_ty: Option<Self::Type>,
        tail_arg_tys: &[Self::Type],
    ) -> (Self::FunctionValue, Vec<Self::TailTarget>) {
        // For now, treat tail functions the same as regular functions
        // TODO: Implement proper tail call optimization
        let func = self.declare_func(name, arg_tys, ret_ty);
        let tail_targets = Vec::new(); // TODO: implement tail targets
        (func, tail_targets)
    }

    fn declare_global(
        &self,
        name: &str,
        ty: Self::Type,
        init: Option<Self::Value>,
    ) -> Self::GlobalValue {
        // let ident = java::Ident(name.to_string());
        // let global_id = self.inner.borrow_mut().global_values.push(ident);
        // GlobalValue(global_id.0)

        let mut inner = self.inner.borrow_mut();

        let args = arg_tys
            .iter()
            .enumerate()
            .map(|(i, &arg_ty)| java::Arg {
                name: java::Ident(format!("arg{i}")),
                ty: inner.type_to_java_type(arg_ty),
            })
            .collect();

        let method = java::Method {
            is_static: true,
            visibility: java::Visibility::Private,
            name: inner.fresh_ident(name),
            args,
            ret_ty: ret_ty.map(|ty| inner.type_to_java_type(ty)),
            body: java::Block::new(),
        };

        inner.globals.push(
            java::Data {
                visibility: java::Visibility::PackagePrivate,
                is_static: true,
                name: inner.fresh_ident(name),
                ty: ty,
                init: init,
            }, // {
               //     pub visibility: Visibility,
               //     pub is_static: bool,
               //     pub name: Ident,
               //     pub ty: Type,
               //     pub init: Expr,
               // }
        );
        // inner.functions.push(FunctionValueData::Function(method))
    }

    fn scope(&self, func: Self::FunctionValue) -> Self::Scope {
        let inner = self.inner.borrow();
        let func_data = &inner.functions[func];
        let block = match func_data {
            FunctionValueData::Function(method) => method.body.clone(),
            FunctionValueData::TailFunction(tail_func) => tail_func.body.clone(),
        };
        Scope {
            context: self.clone(),
            func,
            current_block: block,
        }
    }

    fn tail_scope(&self, tail_target: Self::TailTarget) -> Self::Scope {
        let inner = self.inner.borrow();
        let (func, case) = inner.tail_targets[tail_target];
        let func_data = &inner.functions[func];
        let FunctionValueData::TailFunction(tail_func) = func_data else {
            unreachable!()
        };
        let block = tail_func.cases[case].body.clone();
        Scope {
            context: self.clone(),
            func,
            current_block: block,
        }
    }

    fn global_value_as_pointer(&self, global_value: Self::GlobalValue) -> Self::Value {
        todo!()
    }

    fn variants_type_as_type(&self, variants_type: &Self::VariantsType) -> Self::Type {
        todo!()
    }

    fn get_type(&self, val: Self::Value) -> Self::Type {
        match val {
            Value::Local(local) => self.inner.borrow().locals[local].ty,
            Value::ConstBoolean(_) => Type::Boolean,
            Value::ConstByte(_) => Type::Byte,
            Value::ConstInt(_) => Type::Int,
            Value::ConstLong(_) => Type::Long,
            Value::ConstDouble(_) => Type::Double,
        }
    }

    // We only use this for optimizations, so we don't need to support it properly
    fn is_iso_to_unit(&self, _ty: Self::Type) -> bool {
        false
    }

    fn i1_t(&self) -> Self::Type {
        i1_t()
    }

    fn i8_t(&self) -> Self::Type {
        i8_t()
    }

    fn i32_t(&self) -> Self::Type {
        i32_t()
    }

    fn i64_t(&self) -> Self::Type {
        i64_t()
    }

    fn usize_t(&self) -> Self::Type {
        usize_t()
    }

    fn f64_t(&self) -> Self::Type {
        f64_t()
    }

    fn ptr_t(&self) -> Self::Type {
        ptr_t()
    }

    fn struct_t(&self, fields: &[Self::Type]) -> Self::Type {
        let mut inner = self.inner.borrow_mut();
        Type::Struct(inner.get_struct_type(fields))
    }

    fn variants_t(&self, variants: &[Self::Type]) -> Self::VariantsType {
        let mut inner = self.inner.borrow_mut();
        inner.get_variants_type(variants)
    }

    fn i1(&self, val: bool) -> Self::Value {
        i1(val)
    }

    fn i8(&self, val: u8) -> Self::Value {
        i8(val)
    }

    fn i32(&self, val: u32) -> Self::Value {
        i32(val)
    }

    fn i64(&self, val: u64) -> Self::Value {
        i64(val)
    }

    fn usize(&self, val: u64) -> Self::Value {
        usize(val)
    }

    fn f64(&self, val: f64) -> Self::Value {
        f64(val)
    }

    fn null(&self) -> Self::Value {
        null()
    }
}

impl fountain_pen::Scope for Scope {
    type Context = Context;
    type TailTarget = TailTarget;
    type VariantsType = VariantsType;
    type Type = Type;
    type GlobalValue = GlobalValue;
    type FunctionValue = FunctionValue;
    type Value = Value;

    fn context(&self) -> &Self::Context {
        &self.context
    }

    fn func(&self) -> Self::FunctionValue {
        self.func
    }

    fn undef(&self, ty: Self::Type) -> Self::Value {
        self.upgrade().undef(ty)
    }

    fn str(&self, s: &str) -> Self::Value {
        self.upgrade().str(s)
    }

    fn arg(&self, idx: u32) -> Self::Value {
        self.upgrade().arg(idx)
    }

    fn tail_arg(&self) -> Self::Value {
        self.upgrade().tail_arg()
    }

    fn call(&self, called: Self::FunctionValue, args: &[Self::Value]) -> Self::Value {
        self.upgrade().call(called, args)
    }

    fn call_void(&self, called: Self::FunctionValue, args: &[Self::Value]) {
        self.upgrade().call_void(called, args)
    }

    fn tail_call(&self, called: Self::TailTarget, arg: Self::Value) -> Self::Value {
        self.upgrade().tail_call(called, arg)
    }

    fn gep(&self, struct_ty: Self::Type, struct_ptr: Self::Value, idx: u32) -> Self::Value {
        self.upgrade().gep(struct_ty, struct_ptr, idx)
    }

    fn arrow(
        &self,
        struct_ty: Self::Type,
        field_ty: Self::Type,
        struct_ptr: Self::Value,
        idx: u32,
    ) -> Self::Value {
        self.upgrade().arrow(struct_ty, field_ty, struct_ptr, idx)
    }

    fn field(&self, struct_val: Self::Value, idx: u32) -> Self::Value {
        self.upgrade().field(struct_val, idx)
    }

    fn arrow_set(
        &self,
        struct_ty: Self::Type,
        struct_ptr: Self::Value,
        idx: u32,
        new_data: Self::Value,
    ) {
        self.upgrade()
            .arrow_set(struct_ty, struct_ptr, idx, new_data)
    }

    fn if_(&self, cond: Self::Value, body: impl FnOnce(&Self)) {
        self.upgrade().if_(cond, body)
    }

    fn if_else(&self, cond: Self::Value, mut body: impl FnMut(&Self, bool)) {
        self.upgrade().if_else(cond, body)
    }

    fn if_expr(
        &self,
        cond: Self::Value,
        mut body: impl FnMut(&Self, bool) -> Self::Value,
    ) -> Self::Value {
        self.upgrade().if_expr(cond, body)
    }

    fn ternary(
        &self,
        cond: Self::Value,
        then_value: Self::Value,
        else_value: Self::Value,
    ) -> Self::Value {
        self.upgrade().ternary(cond, then_value, else_value)
    }

    fn int_cast(&self, result_type: Self::Type, int: Self::Value) -> Self::Value {
        self.upgrade().int_cast(result_type, int)
    }

    fn make_struct(&self, fields: &[Self::Value]) -> Self::Value {
        self.upgrade().make_struct(fields)
    }

    fn buf_addr(&self, pointee_ty: Self::Type, arr: Self::Value, idx: Self::Value) -> Self::Value {
        self.upgrade().buf_addr(pointee_ty, arr, idx)
    }

    fn buf_addr_oob(
        &self,
        pointee_ty: Self::Type,
        arr: Self::Value,
        idx: Self::Value,
    ) -> Self::Value {
        self.upgrade().buf_addr_oob(pointee_ty, arr, idx)
    }

    fn buf_set(
        &self,
        pointee_ty: Self::Type,
        arr: Self::Value,
        idx: Self::Value,
        val: Self::Value,
    ) {
        self.upgrade().buf_set(pointee_ty, arr, idx, val)
    }

    fn buf_get(&self, pointee_ty: Self::Type, arr: Self::Value, idx: Self::Value) -> Self::Value {
        self.upgrade().buf_get(pointee_ty, arr, idx)
    }

    fn for_(&self, bound: Self::Value, body: impl FnOnce(&Self, Self::Value)) {
        self.upgrade().for_(bound, body)
    }

    fn ptr_set(&self, ptr: Self::Value, val: Self::Value) {
        self.upgrade().ptr_set(ptr, val)
    }

    fn ptr_get(&self, pointee_ty: Self::Type, ptr: Self::Value) -> Self::Value {
        self.upgrade().ptr_get(pointee_ty, ptr)
    }

    fn global_set(&self, ptr: Self::GlobalValue, val: Self::Value) {
        self.upgrade().global_set(ptr, val)
    }

    fn global_get(&self, pointee_ty: Self::Type, ptr: Self::GlobalValue) -> Self::Value {
        self.upgrade().global_get(pointee_ty, ptr)
    }

    fn panic(&self, panic_string: &str, panic_args: &[Self::Value]) {
        self.upgrade().panic(panic_string, panic_args)
    }

    fn print(&self, message: &str, message_args: &[Self::Value]) {
        self.upgrade().print(message, message_args)
    }

    fn debug(&self, message: &str, message_args: &[Self::Value]) {
        self.upgrade().debug(message, message_args)
    }

    fn malloc(&self, num: Self::Value, ty: Self::Type) -> Self::Value {
        self.upgrade().malloc(num, ty)
    }

    fn calloc(&self, num: Self::Value, ty: Self::Type) -> Self::Value {
        self.upgrade().calloc(num, ty)
    }

    fn free(&self, _ptr: Self::Value) {
        self.upgrade().free(_ptr)
    }

    fn is_null(&self, ptr: Self::Value) -> Self::Value {
        self.upgrade().is_null(ptr)
    }

    fn variants_new_discrim(&self, ty: Self::Type, idx: u32) -> Self::Value {
        self.upgrade().variants_new_discrim(ty, idx)
    }

    fn variants_get_discrim(&self, val: Self::Value) -> Self::Value {
        self.upgrade().variants_get_discrim(val)
    }

    fn variants_new(&self, ty: &Self::VariantsType, val: Self::Value, idx: u32) -> Self::Value {
        self.upgrade().variants_new(ty, val, idx)
    }

    fn variants_get(&self, ty: &Self::VariantsType, val: Self::Value, idx: u32) -> Self::Value {
        self.upgrade().variants_get(ty, val, idx)
    }

    fn variants_switch(
        &self,
        ty: &Self::VariantsType,
        val: Self::Value,
        mut cases: impl FnMut(&Self, u32, Self::Value),
    ) {
        self.upgrade().variants_switch(ty, val, cases)
    }

    fn ret_void(&self) {
        self.upgrade().ret_void()
    }

    fn ret(&self, ret_val: Self::Value) {
        self.upgrade().ret(ret_val)
    }

    fn size(&self, ty: Self::Type) -> Self::Value {
        self.upgrade().size(ty)
    }

    fn unreachable(&self) {
        self.upgrade().unreachable()
    }

    fn alloca(&self, ty: Self::Type) -> Self::Value {
        self.upgrade().alloca(ty)
    }

    fn while_(&self, cond: impl FnOnce(&Self) -> Self::Value, body: impl FnOnce(&Self)) {
        self.upgrade().while_(cond, body);
    }

    // Integer operations

    fn eq(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().eq(arg1, arg2)
    }

    fn ne(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().ne(arg1, arg2)
    }

    fn slt(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().slt(arg1, arg2)
    }

    fn sle(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().sle(arg1, arg2)
    }

    fn sgt(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().sgt(arg1, arg2)
    }

    fn sge(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().sge(arg1, arg2)
    }

    fn ult(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().ult(arg1, arg2)
    }

    fn ule(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().ule(arg1, arg2)
    }

    fn ugt(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().ugt(arg1, arg2)
    }

    fn uge(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().uge(arg1, arg2)
    }

    fn sdiv(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().sdiv(arg1, arg2)
    }

    fn srem(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().srem(arg1, arg2)
    }

    fn udiv(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().udiv(arg1, arg2)
    }

    fn urem(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().urem(arg1, arg2)
    }

    fn neg(&self, arg: Self::Value) -> Self::Value {
        self.upgrade().neg(arg)
    }

    fn add(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().add(arg1, arg2)
    }

    fn sub(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().sub(arg1, arg2)
    }

    fn mul(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().mul(arg1, arg2)
    }

    // Floating point operations

    fn oeq(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().oeq(arg1, arg2)
    }

    fn one(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().one(arg1, arg2)
    }

    fn olt(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().olt(arg1, arg2)
    }

    fn ole(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().ole(arg1, arg2)
    }

    fn ogt(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().ogt(arg1, arg2)
    }

    fn oge(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().oge(arg1, arg2)
    }

    fn fneg(&self, arg: Self::Value) -> Self::Value {
        self.upgrade().fneg(arg)
    }

    fn fadd(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().fadd(arg1, arg2)
    }

    fn fsub(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().fsub(arg1, arg2)
    }

    fn fmul(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().fmul(arg1, arg2)
    }

    fn fdiv(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().fdiv(arg1, arg2)
    }

    // Bitwise operations

    fn sll(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().sll(arg1, arg2)
    }

    fn srl(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().srl(arg1, arg2)
    }

    fn and(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().and(arg1, arg2)
    }

    fn or(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().or(arg1, arg2)
    }

    fn not(&self, arg: Self::Value) -> Self::Value {
        self.upgrade().not(arg)
    }

    fn xor(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value {
        self.upgrade().xor(arg1, arg2)
    }

    fn z_extend(&self, value: Self::Value) -> Self::Value {
        self.upgrade().z_extend(value)
    }

    fn s_extend(&self, value: Self::Value) -> Self::Value {
        self.upgrade().s_extend(value)
    }

    fn truncate(&self, value: Self::Value) -> Self::Value {
        self.upgrade().truncate(value)
    }

    fn ctpop(&self, arg: Self::Value) -> Self::Value {
        self.upgrade().ctpop(arg)
    }

    fn ctlz(&self, arg: Self::Value) -> Self::Value {
        self.upgrade().ctlz(arg)
    }

    fn cttz(&self, arg: Self::Value) -> Self::Value {
        self.upgrade().cttz(arg)
    }
}

#[derive(Clone)]
pub struct ProfileRc {
    // Dummy implementation for Java backend
}

#[derive(Clone)]
pub struct Tal {
    // Dummy implementation for Java backend
}

impl fountain_pen::ProfileRc for ProfileRc {
    type FunctionValue = FunctionValue;

    fn record_retain(&self) -> Self::FunctionValue {
        todo!()
    }

    fn record_release(&self) -> Self::FunctionValue {
        todo!()
    }

    fn record_rc1(&self) -> Self::FunctionValue {
        todo!()
    }

    fn get_retain_count(&self) -> Self::FunctionValue {
        todo!()
    }

    fn get_release_count(&self) -> Self::FunctionValue {
        todo!()
    }

    fn get_rc1_count(&self) -> Self::FunctionValue {
        todo!()
    }
}

impl fountain_pen::Tal for Tal {
    type FunctionValue = FunctionValue;
    type ProfileRc = ProfileRc;

    fn memcpy(&self) -> Self::FunctionValue {
        todo!()
    }

    fn exit(&self) -> Self::FunctionValue {
        todo!()
    }

    fn getchar(&self) -> Self::FunctionValue {
        todo!()
    }

    fn malloc(&self) -> Self::FunctionValue {
        todo!()
    }

    fn calloc(&self) -> Self::FunctionValue {
        todo!()
    }

    fn realloc(&self) -> Self::FunctionValue {
        todo!()
    }

    fn free(&self) -> Self::FunctionValue {
        todo!()
    }

    fn print(&self) -> Self::FunctionValue {
        todo!()
    }

    fn print_error(&self) -> Self::FunctionValue {
        todo!()
    }

    fn write(&self) -> Self::FunctionValue {
        todo!()
    }

    fn write_error(&self) -> Self::FunctionValue {
        todo!()
    }

    fn flush(&self) -> Self::FunctionValue {
        todo!()
    }

    fn prof_clock_res_nanos(&self) -> Self::FunctionValue {
        todo!()
    }

    fn prof_clock_nanos(&self) -> Self::FunctionValue {
        todo!()
    }

    fn prof_report_init(&self) -> Self::FunctionValue {
        todo!()
    }

    fn prof_report_write_string(&self) -> Self::FunctionValue {
        todo!()
    }

    fn prof_report_write_u64(&self) -> Self::FunctionValue {
        todo!()
    }

    fn prof_report_done(&self) -> Self::FunctionValue {
        todo!()
    }

    fn prof_rc(&self) -> Option<&Self::ProfileRc> {
        todo!()
    }

    fn expect_i1(&self) -> Self::FunctionValue {
        todo!()
    }

    fn umul_with_overflow_i64(&self) -> Self::FunctionValue {
        todo!()
    }
}

fn compile_to_jar(
    context: &Context,
    version: &str,
    jar_path: &Path,
    path: &Path,
) -> Result<(), Error> {
    struct Guard {
        old: PathBuf,
    }

    impl Guard {
        #[must_use]
        fn set_cwd(new: &Path) -> Self {
            let old = std::env::current_dir().unwrap();
            std::env::set_current_dir(new).unwrap();
            Self { old }
        }
    }

    impl Drop for Guard {
        fn drop(&mut self) {
            std::env::set_current_dir(&self.old).unwrap();
        }
    }

    let mut temp_dir = tempfile::tempdir_in("").unwrap();

    let _ = Guard::set_cwd(temp_dir.path());
    let main_file_path = Path::new("Main.java");

    let mut main_file = File::create(&main_file_path).unwrap();
    context.write_to(&mut main_file).unwrap();

    let output = std::process::Command::new("javac")
        .arg("--enable-preview")
        .arg("--source")
        .arg(version)
        .arg("Main.java")
        .output()
        .map_err(Error::CouldNotSpawnChild)?;
    if !output.status.success() {
        return Err(Error::CouldNotCompileJava(
            String::from_utf8_lossy(&output.stderr).to_string(),
        ));
    }

    let output = std::process::Command::new("jar")
        .arg("cfe")
        .arg(jar_path)
        .arg("Main")
        .arg("*.class")
        .output()
        .map_err(Error::CouldNotSpawnChild)?;
    if !output.status.success() {
        return Err(Error::CouldNotCreateJar(
            String::from_utf8_lossy(&output.stderr).to_string(),
        ));
    }

    Ok(())
}
