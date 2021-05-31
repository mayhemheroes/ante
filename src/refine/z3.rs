//! This module acts as a thin wrapper around z3-sys,
//! providing helper functions without changing any
//! actual behavior.
use z3_sys::*;
use std::ffi::CString;

#[derive(Copy, Clone)]
pub struct Context(Z3_context);

#[derive(Copy, Clone)]
pub struct Solver(Z3_solver);

pub enum SatResult {
    Sat(Model),
    Unsat,
    Unknown,
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
            let sort_refs: Vec<std::os::raw::c_uint> = vec![0; fields.len()];

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

    pub fn mk_datatype(self, name: &str, constructors: &[Constructor]) -> Sort {
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

    pub fn apply(self, func_decl: FuncDecl, args: &[Ast]) -> Ast {
        unsafe {
            Z3_mk_app(self.0, func_decl, args.len() as u32, args.as_ptr())
        }
    }
}

impl Solver {
    pub fn new(context: Context) -> Solver {
        unsafe { 
            let solver = Z3_mk_solver(context.0);
            // Z3_solver_inc_ref(self.0, solver);
            Solver(solver)
        }
    }

    pub fn check(self, context: Context) -> SatResult {
        unsafe {
            match Z3_solver_check(context.0, self.0) {
                Z3_L_TRUE => {
                    let model = Z3_solver_get_model(context.0, self.0);
                    SatResult::Sat(model)
                },
                Z3_L_FALSE => SatResult::Unsat,
                Z3_L_UNDEF => SatResult::Unknown,
                _ => unreachable!(),
            }
        }
    }

    pub fn push(self) {
    }

    pub fn pop(self) {
    }

    pub fn assert(self) {
    }
}
