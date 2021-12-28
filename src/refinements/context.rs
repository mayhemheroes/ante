use std::collections::HashMap;

use crate::{
    cache::{DefinitionInfoId, ModuleCache},
    error::location::Locatable,
    parser::ast::Ast,
    refinements::types::{Refinement, RefinementType},
    types::Type,
};

pub struct RefinementContext {
    definitions: HashMap<DefinitionInfoId, RefinementType>,
}

impl RefinementContext {
    pub fn new() -> RefinementContext {
        RefinementContext {
            definitions: HashMap::new(),
        }
    }

    /// Lookup the given id and return the associated refinement type.
    /// If no definition is found, assume the variable is defined and
    /// create one using the Type from the ModuleCache.
    pub fn lookup_or_create<'c>(&mut self, id: DefinitionInfoId, cache: &ModuleCache<'c>) -> RefinementType {
        if let Some(typ) = self.definitions.get(&id) {
            return typ.clone();
        }

        let typ = cache.definition_infos[id.0].typ.as_ref().unwrap();
        let typ = self.convert_type(typ);
        self.definitions.insert(id, typ.clone());
        typ
    }

    pub fn insert_refinement(&mut self, id: DefinitionInfoId, typ: RefinementType) {
        self.definitions.insert(id, typ);
    }

    pub fn remove_refinement(&mut self, id: DefinitionInfoId) {
        self.definitions.remove(&id);
    }

    pub fn with_refinement<'c, F, T>(&mut self, id: DefinitionInfoId, r: Refinement, cache: &mut ModuleCache<'c>, f: F) -> T
        where F: FnOnce(&mut Self) -> T
    {
        let t = RefinementType::bool_refined(r, cache);
        self.definitions.insert(id, t);
        let ret = f(self);
        self.definitions.remove(&id);
        ret
    }

    /// Convert a term into a term that can be immediately
    /// substituted into a Refinement (i.e. it is a Variable or Literal)
    pub fn named<'c>(ast: &Ast<'c>, cache: &mut ModuleCache<'c>) -> (Ast<'c>, Refinement, DefinitionInfoId) {
        let location = ast.locate();
        let name = "[internal]".to_string();
        let id = cache.push_definition(&name, false, location);
        let var = Ast::variable_with_definition(name, id, location);

        // TODO: this can be made more efficient
        let def = Ast::definition(var.clone(), ast.clone(), location);
        (Ast::sequence(vec![def, var], location), Refinement::Variable(id), id)
    }

    /// Converts a types::Type to a RefinementType. Any refinement
    /// holes not specified in the Type will be translated as None
    /// in the corresponding Option<Refinement> field of the RefinementType
    pub fn convert_type(&mut self, _typ: &Type) -> RefinementType {
        todo!()
    }

    // pub fn convert<'c>(&self, ast: &Ast<'c>) -> Refinement {
    //     match ast {
    //         Ast::Variable(variable) => Refinement::Variable(variable.definition.unwrap()),
    //         Ast::Literal(literal) => {
    //             match &literal.kind {
    //                 LiteralKind::Unit => Refinement::Unit,
    //                 LiteralKind::Char(c) => Refinement::Integer(*c as i64),
    //                 LiteralKind::Bool(b) => Refinement::Boolean(*b),
    //                 LiteralKind::Float(f) => Refinement::Float(*f),
    //                 LiteralKind::Integer(x, _) => Refinement::Integer(*x as i64),
    //                 LiteralKind::String(s) => (),
    //             }
    //         }
    //         other => {

    //         }
    //     }
    // }

    pub fn refine_definition<'c>(&mut self, id: DefinitionInfoId, cache: &ModuleCache<'c>) -> Refinement {
        let info = &cache.definition_infos[id.0];

        use crate::cache::DefinitionKind;
        match &info.definition {
            Some(DefinitionKind::Definition(definition)) => {

            },
            Some(DefinitionKind::TypeConstructor { name, tag }) => {

            },
            Some(DefinitionKind::TraitDefinition(definition)) => {

            },
            Some(DefinitionKind::Extern(definition)) => {

            },
            Some(DefinitionKind::MatchPattern) => {

            },
            Some(DefinitionKind::Parameter) => {

            },
            None => todo!(),
        }

        todo!()
    }

    pub fn bind_pattern<'c>(&mut self, _pattern: &Ast<'c>, _typ: RefinementType) {
        todo!()
    }

    pub fn iter<'a>(&'a self) -> impl Iterator<Item = (DefinitionInfoId, &'a RefinementType)> {
        self.definitions.iter().map(|(id, typ)| (*id, typ))
    }

    pub fn fold<T, F>(&self, mut initial: T, mut f: F) -> T
        where F: FnMut(DefinitionInfoId, &Refinement, T) -> T
    {
        for (_, typ) in self.iter() {
            if let RefinementType::Base(_, Some((id, refinement))) = typ {
                initial = f(*id, refinement, initial);
            }
        }
        initial
    }
}
