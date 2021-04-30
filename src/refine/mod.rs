use crate::parser::ast::{ self, Ast };
use crate::cache::{ ModuleCache, DefinitionInfoId };
use crate::util::{ reinterpret_from_bits, timing };

mod context;

use crate::refine::context::{ RefinementContext, Refinements, DefinitionRefinementInfo };

pub fn refine<'c>(ast: &mut Ast<'c>, cache: &mut ModuleCache<'c>) {
    timing::start_time("Refinement type inference");
    let z3_context = z3::Context::new(&z3::Config::new());
    let mut context = RefinementContext::new(&z3_context);
    ast.refine(&mut context, cache);
}

trait Refineable {
    fn refine<'z3, 'c>(&mut self, context: &mut RefinementContext<'z3>, cache: &mut ModuleCache<'c>) -> Option<Refinements<'z3>>;
}

impl<'ast> Refineable for Ast<'ast> {
    fn refine<'z3, 'c>(&mut self, context: &mut RefinementContext<'z3>, cache: &mut ModuleCache<'c>) -> Option<Refinements<'z3>> {
        dispatch_on_expr!(self, Refineable::refine, context, cache)
    }
}

impl<'ast> Refineable for ast::Literal<'ast> {
    fn refine<'z3, 'c>(&mut self, context: &mut RefinementContext<'z3>, cache: &mut ModuleCache<'c>) -> Option<Refinements<'z3>> {
        use crate::parser::ast::LiteralKind;
        match &self.kind {
            LiteralKind::Char(c) => None,
            LiteralKind::Bool(b) => context.bool_value(*b),
            LiteralKind::Float(f) => context.float_value(reinterpret_from_bits(*f)),
            LiteralKind::Integer(i, kind) => context.integer_value(*i, kind.is_signed(cache)),
            LiteralKind::String(s) => context.string_value(s),
            LiteralKind::Unit => context.integer_value(0, false),
        }
    }
}

impl<'ast> Refineable for ast::Variable<'ast> {
    fn refine<'z3, 'c>(&mut self, context: &mut RefinementContext<'z3>, cache: &mut ModuleCache<'c>) -> Option<Refinements<'z3>> {

    }
}

impl<'ast> Refineable for ast::Lambda<'ast> {
    fn refine<'z3, 'c>(&mut self, context: &mut RefinementContext<'z3>, cache: &mut ModuleCache<'c>) -> Option<Refinements<'z3>> {
        self.body.refine(context, cache)
            .map(|refinements| DefinitionRefinementInfo::new(refinements, self.args));

        None
    }
}

impl<'ast> Refineable for ast::FunctionCall<'ast> {
    fn refine<'z3, 'c>(&mut self, context: &mut RefinementContext<'z3>, cache: &mut ModuleCache<'c>) -> Option<Refinements<'z3>> {

    }
}

impl<'ast> Refineable for ast::Definition<'ast> {
    fn refine<'z3, 'c>(&mut self, context: &mut RefinementContext<'z3>, cache: &mut ModuleCache<'c>) -> Option<Refinements<'z3>> {

    }
}

impl<'ast> Refineable for ast::If<'ast> {
    fn refine<'z3, 'c>(&mut self, context: &mut RefinementContext<'z3>, cache: &mut ModuleCache<'c>) -> Option<Refinements<'z3>> {

    }
}

impl<'ast> Refineable for ast::Match<'ast> {
    fn refine<'z3, 'c>(&mut self, context: &mut RefinementContext<'z3>, cache: &mut ModuleCache<'c>) -> Option<Refinements<'z3>> {

    }
}

impl<'ast> Refineable for ast::TypeDefinition<'ast> {
    fn refine<'z3, 'c>(&mut self, context: &mut RefinementContext<'z3>, cache: &mut ModuleCache<'c>) -> Option<Refinements<'z3>> {

    }
}

impl<'ast> Refineable for ast::TypeAnnotation<'ast> {
    fn refine<'z3, 'c>(&mut self, context: &mut RefinementContext<'z3>, cache: &mut ModuleCache<'c>) -> Option<Refinements<'z3>> {

    }
}

impl<'ast> Refineable for ast::Import<'ast> {
    fn refine<'z3, 'c>(&mut self, context: &mut RefinementContext<'z3>, cache: &mut ModuleCache<'c>) -> Option<Refinements<'z3>> {

    }
}

impl<'ast> Refineable for ast::TraitDefinition<'ast> {
    fn refine<'z3, 'c>(&mut self, context: &mut RefinementContext<'z3>, cache: &mut ModuleCache<'c>) -> Option<Refinements<'z3>> {

    }
}

impl<'ast> Refineable for ast::TraitImpl<'ast> {
    fn refine<'z3, 'c>(&mut self, context: &mut RefinementContext<'z3>, cache: &mut ModuleCache<'c>) -> Option<Refinements<'z3>> {

    }
}

impl<'ast> Refineable for ast::Return<'ast> {
    fn refine<'z3, 'c>(&mut self, context: &mut RefinementContext<'z3>, cache: &mut ModuleCache<'c>) -> Option<Refinements<'z3>> {

    }
}

impl<'ast> Refineable for ast::Sequence<'ast> {
    fn refine<'z3, 'c>(&mut self, context: &mut RefinementContext<'z3>, cache: &mut ModuleCache<'c>) -> Option<Refinements<'z3>> {

    }
}

impl<'ast> Refineable for ast::Extern<'ast> {
    fn refine<'z3, 'c>(&mut self, context: &mut RefinementContext<'z3>, cache: &mut ModuleCache<'c>) -> Option<Refinements<'z3>> {

    }
}

impl<'ast> Refineable for ast::MemberAccess<'ast> {
    fn refine<'z3, 'c>(&mut self, context: &mut RefinementContext<'z3>, cache: &mut ModuleCache<'c>) -> Option<Refinements<'z3>> {

    }
}

impl<'ast> Refineable for ast::Assignment<'ast> {
    fn refine<'z3, 'c>(&mut self, context: &mut RefinementContext<'z3>, cache: &mut ModuleCache<'c>) -> Option<Refinements<'z3>> {

    }
}
