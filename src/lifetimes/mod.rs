//! This module implements the Lifetime Analysis Pass whose purpose
//! is to find the lowest stack frame a lifetime variable is found at.
//! The lifetime variables should already be unified via the type inference
//! pass beforehand so this pass need only traverse the Ast in a
//! breadth-first manor starting in main to find the first occurance of
//! each type variable.
use crate::parser::ast::{ self, Ast };
use crate::types::{ TypeVariableId, Type, TypeBinding };
use crate::cache::{ ModuleCache, DefinitionInfoId, DefinitionKind };
use crate::util::trustme;

use std::collections::HashMap;

mod refusageinfo;
mod allocationcount;

use refusageinfo::RefUsageInfo;

/// A lifetime variable is represented simply as a type variable for ease
/// of unification during the type inference pass.
pub type LifetimeVariableId = TypeVariableId;

#[derive(Copy, Clone)]
pub struct StackFrameIndex(usize);

/// The visitor struct passed around for the lifetime analysis pass in the
/// InferableLifetime trait below. This lets us keep track of the lowest
/// StackFrameIndex we find a given lifetime variable in as well as how
/// many times allocation is performed in that reference. If it is a known
/// number of times, then codegen can use this information to allocate that
/// memory on the stack.
struct LifetimeAnalyzer {
    pub level: StackFrameIndex,

    /// Contains the stack frame index each region should be allocated in
    pub lifetimes: HashMap<LifetimeVariableId, RefUsageInfo>,

    /// Queue of definitions to visit and what stack frame index they should be at.
    /// This is used so that we can traverse the ast breadth-first by stackframe
    /// rather than depth-first visiting each function as we find it.
    pub definition_queue: Vec<(DefinitionInfoId, StackFrameIndex)>,

    pub visited_definitions: HashMap<DefinitionInfoId, Vec<RefUsageInfo>>,
}

/// TODO: need to store analysis data on functions, e.g:
/// foo a b - allocates 1 ref in a, allocates n refs in b

pub fn infer<'c>(ast: &mut Ast<'c>, cache: &mut ModuleCache<'c>) {
    let mut analyzer = LifetimeAnalyzer::new();
    // First visit main
    ast.infer_lifetime(&mut analyzer, cache);

    // Then visit every new callstack frame after main.
    // We don't need to visit the same function twice (even for different
    // generic arguments) since we are only trying to find the lowest
    // StackFrameIndex a given `ref` appears in so that the codegen
    // pass can allocate space on that stack frame later.
    while let Some((id, stackframe)) = analyzer.definition_queue.pop() {
        analyzer.level = stackframe;
        analyzer.visit_definition(id, cache);
    }
}

impl LifetimeAnalyzer {
    fn new() -> LifetimeAnalyzer {
        LifetimeAnalyzer {
            level: StackFrameIndex(0),
            lifetimes: HashMap::new(),
            definition_queue: vec![],
            visited_definitions: HashMap::new(),
        }
    }

    /// Scan a type for any references that contain lifetime variables.
    /// If any lifetime variables are found, register this instance
    /// of them at the current stack frame index.
    fn scan_type_for_refs<'c>(&mut self, typ: &Type, cache: &ModuleCache<'c>) {
        match typ {
            Type::Ref(lifetime) => {
                self.lifetimes.entry(*lifetime)
                    .or_insert(RefUsageInfo::new(*lifetime, self.level));
            },
            Type::Primitive(_) => (),
            Type::TypeVariable(id) => {
                match &cache.type_bindings[id.0] {
                    TypeBinding::Bound(typ) => self.scan_type_for_refs(typ, cache),

                    // If the type is still unbound at this point then it is a generic type
                    // which may only be bound at the site where the function/variable is used.
                    // In this case, we don't care about keeping track of type bindings
                    // since we know the ref could only originate from this use site which will
                    // always have a lower StackFrameIndex and thus we don't need to actually
                    // keep track of monomorphisation bindings when recurring into functions.
                    TypeBinding::Unbound(..) => (),
                }
            },
            Type::UserDefinedType(_id) => {
                // TODO: recurse into user-defined type to find refs hidden
                // in struct or union fields.
            },
            Type::Function(args, ret, _) => {
                for arg in args {
                    self.scan_type_for_refs(arg, cache);
                }
                self.scan_type_for_refs(ret, cache);
            },
            Type::TypeApplication(constructor, args) => {
                self.scan_type_for_refs(constructor, cache);
                for arg in args {
                    self.scan_type_for_refs(arg, cache);
                }
            },
            Type::ForAll(_, typ) => self.scan_type_for_refs(typ, cache),
        }
    }

    fn queue_definition(&mut self, id: DefinitionInfoId) {
        let next_stackframe = StackFrameIndex(self.level.0 + 1);
        self.definition_queue.push((id, next_stackframe));
    }

    fn visit_definition<'c>(&mut self, id: DefinitionInfoId, cache: &mut ModuleCache<'c>) {
        if self.visited_definitions.contains_key(&id) {
            return;
        }

        self.visited_definitions.insert(id, vec![]);

        let definition = cache.definition_infos[id.0].definition.as_mut().unwrap();

        match trustme::extend_lifetime(definition) {
            DefinitionKind::Definition(definition) => {
                definition.infer_lifetime(self, cache);
            },
            DefinitionKind::Extern(declaration) => {
                declaration.infer_lifetime(self, cache);
            },
            DefinitionKind::TraitDefinition(_) => {
                // Until default methods are implemented, there is nothing
                // in a trait definition that can allocate lifetimes
            },
            // Do nothing for the remaining cases - they can't contain any lifetimes in their bodies
            DefinitionKind::TypeConstructor { .. } => {},
            DefinitionKind::Parameter => {},
            DefinitionKind::MatchPattern => {},
        }
    }
}

trait InferableLifetime {
    fn infer_lifetime<'c>(&mut self, analyzer: &mut LifetimeAnalyzer, cache: &mut ModuleCache<'c>);
}

impl<'ast> InferableLifetime for Ast<'ast> {
    fn infer_lifetime<'c>(&mut self, analyzer: &mut LifetimeAnalyzer, cache: &mut ModuleCache<'c>) {
        dispatch_on_expr!(self, InferableLifetime::infer_lifetime, analyzer, cache)
    }
}

impl<'ast> InferableLifetime for ast::Literal<'ast> {
    fn infer_lifetime<'c>(&mut self, _analyzer: &mut LifetimeAnalyzer, _cache: &mut ModuleCache<'c>) {}
}

impl<'ast> InferableLifetime for ast::Variable<'ast> {
    fn infer_lifetime<'c>(&mut self, analyzer: &mut LifetimeAnalyzer, cache: &mut ModuleCache<'c>) {
        analyzer.scan_type_for_refs(self.typ.as_ref().unwrap(), cache);

        analyzer.queue_definition(self.definition.unwrap());
    }
}

impl<'ast> InferableLifetime for ast::Lambda<'ast> {
    fn infer_lifetime<'c>(&mut self, analyzer: &mut LifetimeAnalyzer, cache: &mut ModuleCache<'c>) {
        analyzer.scan_type_for_refs(self.typ.as_ref().unwrap(), cache);

        self.body.infer_lifetime(analyzer, cache);
    }
}

impl<'ast> InferableLifetime for ast::FunctionCall<'ast> {
    fn infer_lifetime<'c>(&mut self, analyzer: &mut LifetimeAnalyzer, cache: &mut ModuleCache<'c>) {
        analyzer.scan_type_for_refs(self.typ.as_ref().unwrap(), cache);

        self.function.infer_lifetime(analyzer, cache);
        for arg in self.args.iter_mut() {
            arg.infer_lifetime(analyzer, cache);
        }
    }
}

impl<'ast> InferableLifetime for ast::Definition<'ast> {
    fn infer_lifetime<'c>(&mut self, analyzer: &mut LifetimeAnalyzer, cache: &mut ModuleCache<'c>) {
        self.pattern.infer_lifetime(analyzer, cache);
        self.expression.infer_lifetime(analyzer, cache);
    }
}

impl<'ast> InferableLifetime for ast::If<'ast> {
    fn infer_lifetime<'c>(&mut self, analyzer: &mut LifetimeAnalyzer, cache: &mut ModuleCache<'c>) {
        self.condition.infer_lifetime(analyzer, cache);
        self.then.infer_lifetime(analyzer, cache);

        if let Some(otherwise) = &mut self.otherwise {
            otherwise.infer_lifetime(analyzer, cache);
        }
    }
}

impl<'ast> InferableLifetime for ast::Match<'ast> {
    fn infer_lifetime<'c>(&mut self, analyzer: &mut LifetimeAnalyzer, cache: &mut ModuleCache<'c>) {
        self.expression.infer_lifetime(analyzer, cache);

        for (pattern, branch) in self.branches.iter_mut() {
            pattern.infer_lifetime(analyzer, cache);
            branch.infer_lifetime(analyzer, cache);
        }
    }
}

impl<'ast> InferableLifetime for ast::TypeDefinition<'ast> {
    fn infer_lifetime<'c>(&mut self, _analyzer: &mut LifetimeAnalyzer, _cache: &mut ModuleCache<'c>) {}
}

impl<'ast> InferableLifetime for ast::TypeAnnotation<'ast> {
    fn infer_lifetime<'c>(&mut self, analyzer: &mut LifetimeAnalyzer, cache: &mut ModuleCache<'c>) {
        self.lhs.infer_lifetime(analyzer, cache);
    }
}

impl<'ast> InferableLifetime for ast::Import<'ast> {
    fn infer_lifetime<'c>(&mut self, _analyzer: &mut LifetimeAnalyzer, _cache: &mut ModuleCache<'c>) {}
}

impl<'ast> InferableLifetime for ast::TraitDefinition<'ast> {
    fn infer_lifetime<'c>(&mut self, _analyzer: &mut LifetimeAnalyzer, _cache: &mut ModuleCache<'c>) {}
}

impl<'ast> InferableLifetime for ast::TraitImpl<'ast> {
    fn infer_lifetime<'c>(&mut self, analyzer: &mut LifetimeAnalyzer, cache: &mut ModuleCache<'c>) {
        for definition in self.definitions.iter_mut() {
            definition.infer_lifetime(analyzer, cache);
        }
    }
}

impl<'ast> InferableLifetime for ast::Return<'ast> {
    fn infer_lifetime<'c>(&mut self, analyzer: &mut LifetimeAnalyzer, cache: &mut ModuleCache<'c>) {
        self.expression.infer_lifetime(analyzer, cache);
    }
}

impl<'ast> InferableLifetime for ast::Sequence<'ast> {
    fn infer_lifetime<'c>(&mut self, analyzer: &mut LifetimeAnalyzer, cache: &mut ModuleCache<'c>) {
        for statement in self.statements.iter_mut() {
            statement.infer_lifetime(analyzer, cache);
        }
    }
}

impl<'ast> InferableLifetime for ast::Extern<'ast> {
    fn infer_lifetime<'c>(&mut self, analyzer: &mut LifetimeAnalyzer, cache: &mut ModuleCache<'c>) {
        for declaration in self.declarations.iter_mut() {
            declaration.infer_lifetime(analyzer, cache);
        }
    }
}

impl<'ast> InferableLifetime for ast::MemberAccess<'ast> {
    fn infer_lifetime<'c>(&mut self, analyzer: &mut LifetimeAnalyzer, cache: &mut ModuleCache<'c>) {
        self.lhs.infer_lifetime(analyzer, cache);
    }
}

impl<'ast> InferableLifetime for ast::Assignment<'ast> {
    fn infer_lifetime<'c>(&mut self, analyzer: &mut LifetimeAnalyzer, cache: &mut ModuleCache<'c>) {
        self.lhs.infer_lifetime(analyzer, cache);
        self.rhs.infer_lifetime(analyzer, cache);
    }
}
