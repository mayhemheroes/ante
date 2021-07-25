//! This module acts as a thin wrapper around z3-sys,
//! providing helper functions without changing any
//! actual behavior.
use z3_sys::*;
use std::ffi::{ CStr, CString };
use crate::util::fmap;

#[derive(Copy, Clone)]
pub struct Context(Z3_context);

#[derive(Copy, Clone)]
pub struct Solver {
    context: Z3_context,
    solver: Z3_solver,
}

pub enum SatResult {
    Sat(Model),
    Unsat,
    Unknown(/*reason:*/String),
}

pub type Model = Z3_model;

/// This needs to be a type alias instead of a wrapper
/// struct to avoid extra iterations when passing arrays
/// of Z3_asts to z3.
pub type Ast = Z3_ast;

pub type FuncDecl = Z3_func_decl;
pub type Sort = Z3_sort;
pub type Constructor = Z3_constructor;
pub type Symbol = Z3_symbol;

impl Context {
    pub fn new() -> Context {
        unsafe {
            let config = Z3_mk_config();
            Context(Z3_mk_context(config))
        }
    }

    pub fn bool_value(self, value: bool) -> Ast {
        unsafe {
            if value {
                Z3_mk_true(self.0)
            } else {
                Z3_mk_false(self.0)
            }
        }
    }

    pub fn fresh_bool(self) -> Ast {
        unsafe {
            let no_name = std::ptr::null();
            // inc rc here?
            let sort = Z3_mk_bool_sort(self.0);
            Z3_mk_fresh_const(self.0, no_name, sort)
        }
    }

    pub fn int_value(self, value: u64, signed: bool) -> Ast {
        unsafe {
            let sort = Z3_mk_int_sort(self.0);
            if signed {
                Z3_mk_int64(self.0, value as i64, sort)
            } else {
                Z3_mk_unsigned_int64(self.0, value, sort)
            }
        }
    }

    pub fn double_value(self, value: f64) -> Ast {
        unsafe {
            let sort = Z3_mk_fpa_sort_64(self.0);
            Z3_mk_fpa_numeral_double(self.0, value, sort)
        }
    }

    pub fn string_value(self, value: &str) -> Ast {
        let string = CString::new(value).unwrap();
        unsafe {
            Z3_mk_string(self.0, string.as_c_str().as_ptr())
        }
    }

    pub fn mk_const(self, name: &str, sort: Sort) -> Ast {
        let name = CString::new(name).unwrap();
        unsafe {
            let symbol = Z3_mk_string_symbol(self.0, name.as_c_str().as_ptr());
            Z3_mk_const(self.0, symbol, sort)
        }
    }

    pub fn mk_fresh(self, sort: Sort) -> Ast {
        unsafe {
            let prefix = std::ptr::null();
            Z3_mk_fresh_const(self.0, prefix, sort)
        }
    }

    pub fn int_sort(self) -> Sort {
        unsafe { Z3_mk_int_sort(self.0) }
    }

    pub fn double_sort(self) -> Sort {
        unsafe { Z3_mk_fpa_sort_double(self.0) }
    }

    pub fn bool_sort(self) -> Sort {
        unsafe { Z3_mk_bool_sort(self.0) }
    }

    pub fn uninterpreted_sort(self, name: &str) -> Sort {
        unsafe { Z3_mk_uninterpreted_sort(self.0, self.symbol(name)) }
    }

    pub fn get_sort(self, ast: Ast) -> Sort {
        unsafe { Z3_get_sort(self.0, ast) }
    }

    pub fn symbol(self, name: &str) -> Symbol {
        let name = CString::new(name).unwrap();
        unsafe {
            Z3_mk_string_symbol(self.0, name.as_c_str().as_ptr())
        }
    }

    pub fn mk_constructor(self, name: &str, fields: &[Sort], field_names: &[Symbol]) -> Constructor {
        assert_eq!(fields.len(), field_names.len());
        let recognizer_name = CString::new(format!("is_{}", name)).unwrap();
        let recognizer_name = recognizer_name.as_c_str().as_ptr();

        unsafe {
            // the main constructor name is after the "is_" prefix of the recognizer
            let name = recognizer_name.offset(3);

            let recognizer_name = Z3_mk_string_symbol(self.0, recognizer_name);
            let name = Z3_mk_string_symbol(self.0, name);

            // TODO: These are all "Sort" datatype accessors, these probably don't
            // work for recursive datatypes.
            let mut sort_refs: Vec<std::os::raw::c_uint> = vec![0; fields.len()];

            Z3_mk_constructor(self.0,
                name,
                recognizer_name,
                fields.len() as u32,
                field_names.as_ptr(),
                fields.as_ptr(),
                sort_refs.as_mut_ptr()
            )
        }
    }

    pub fn mk_datatype(self, name: &str, constructors: &mut [Constructor]) -> Sort {
        unsafe {
            let name = self.symbol(name);
            Z3_mk_datatype(self.0, name, constructors.len() as u32, constructors.as_mut_ptr())
        }
    }

    pub fn get_nth_constructor(self, sort: Sort, n: usize) -> FuncDecl {
        unsafe {
            Z3_get_datatype_sort_constructor(self.0, sort, n as u32)
        }
    }

    pub fn ast_to_string(self, ast: Ast) -> String {
        unsafe {
            let cstr = Z3_ast_to_string(self.0, ast);
            CStr::from_ptr(cstr).to_string_lossy().to_string()
        }
    }

    pub fn func_decl_to_string(self, func: FuncDecl) -> String {
        unsafe {
            let cstring = Z3_func_decl_to_string(self.0, func);
            let cstring = CStr::from_ptr(cstring);
            cstring.to_string_lossy().to_string()
        }
    }

    pub fn apply(self, func_decl: FuncDecl, args: &[Ast]) -> Ast {
        unsafe {
            Z3_mk_app(self.0, func_decl, args.len() as u32, args.as_ptr())
        }
    }

    pub fn and(self, args: &[Ast]) -> Ast {
        unsafe {
            Z3_mk_and(self.0, args.len() as u32, args.as_ptr())
        }
    }

    pub fn eq(self, arg1: Ast, arg2: Ast) -> Ast {
        unsafe {
            Z3_mk_eq(self.0, arg1, arg2)
        }
    }

    pub fn neq(self, arg1: Ast, arg2: Ast) -> Ast {
        unsafe {
            let args = [arg1, arg2];
            Z3_mk_distinct(self.0, 2, args.as_ptr())
        }
    }

    pub fn implies(self, arg1: Ast, arg2: Ast) -> Ast {
        unsafe {
            Z3_mk_implies(self.0, arg1, arg2)
        }
    }

    pub fn add(self, arg1: Ast, arg2: Ast) -> Ast {
        unsafe {
            let args = [arg1, arg2];
            Z3_mk_add(self.0, 2, args.as_ptr())
        }
    }

    pub fn sub(self, arg1: Ast, arg2: Ast) -> Ast {
        unsafe {
            let args = [arg1, arg2];
            Z3_mk_sub(self.0, 2, args.as_ptr())
        }
    }

    pub fn mul(self, arg1: Ast, arg2: Ast) -> Ast {
        unsafe {
            let args = [arg1, arg2];
            Z3_mk_mul(self.0, 2, args.as_ptr())
        }
    }

    pub fn div(self, arg1: Ast, arg2: Ast) -> Ast {
        unsafe {
            Z3_mk_div(self.0, arg1, arg2)
        }
    }

    pub fn lt(self, arg1: Ast, arg2: Ast) -> Ast {
        unsafe {
            Z3_mk_lt(self.0, arg1, arg2)
        }
    }

    pub fn le(self, arg1: Ast, arg2: Ast) -> Ast {
        unsafe {
            Z3_mk_le(self.0, arg1, arg2)
        }
    }

    pub fn gt(self, arg1: Ast, arg2: Ast) -> Ast {
        unsafe {
            Z3_mk_gt(self.0, arg1, arg2)
        }
    }

    pub fn ge(self, arg1: Ast, arg2: Ast) -> Ast {
        unsafe {
            Z3_mk_ge(self.0, arg1, arg2)
        }
    }

    pub fn not(self, arg: Ast) -> Ast {
        unsafe {
            Z3_mk_not(self.0, arg)
        }
    }

    pub fn eval(self, model: Model, ast: Ast) -> Option<Ast> {
        unsafe {
            let mut buffer = std::mem::zeroed();
            if Z3_model_eval(self.0, model, ast, true, &mut buffer) {
                Some(buffer)
            } else {
                None
            }
        }
    }

    pub fn substitute(self, ast: Ast, from: &[Ast], to: &[Ast]) -> Ast {
        assert_eq!(from.len(), to.len());
        unsafe {
            Z3_substitute(self.0, ast, from.len() as u32, from.as_ptr(), to.as_ptr())
        }
    }

    pub fn define_function(self, name: &str, args: &mut [Ast], body: Ast) -> FuncDecl {
        let arg_sorts = fmap(args, |&arg| self.get_sort(arg));
        let body_sort = self.get_sort(body);
        let name = self.symbol(name);

        unsafe {
            let decl = Z3_mk_rec_func_decl(self.0, name, arg_sorts.len() as u32,
                arg_sorts.as_ptr(), body_sort);

            Z3_add_rec_def(self.0, decl, args.len() as u32, args.as_mut_ptr(), body);
            decl
        }
    }
}

impl Solver {
    pub fn new(context: Context) -> Solver {
        unsafe { 
            let context = context.0;
            let solver = Z3_mk_solver(context);
            // Z3_solver_inc_ref(self.0, solver);
            Solver { solver, context }
        }
    }

    pub fn check(self) -> SatResult {
        unsafe {
            match Z3_solver_check(self.context, self.solver) {
                Z3_L_TRUE => {
                    let model = Z3_solver_get_model(self.context, self.solver);
                    SatResult::Sat(model)
                },
                Z3_L_FALSE => SatResult::Unsat,
                Z3_L_UNDEF => {
                    let reason = Z3_solver_get_reason_unknown(self.context, self.solver);
                    let reason = CStr::from_ptr(reason).to_string_lossy();
                    SatResult::Unknown(reason.to_string())
                },
                _ => unreachable!(),
            }
        }
    }

    pub fn push(self) {
        unsafe {
            Z3_solver_push(self.context, self.solver)
        }
    }

    pub fn pop(self) {
        unsafe {
            Z3_solver_pop(self.context, self.solver, 1)
        }
    }

    pub fn assert(self, assertion: Ast) {
        unsafe {
            Z3_solver_assert(self.context, self.solver, assertion)
        }
    }
}
