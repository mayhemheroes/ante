use std::collections::HashMap;

use crate::{
    cache::{DefinitionInfoId, ModuleCache},
    types::refinement::{Refinement, RefinementType}
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

    pub fn lookup(&self, id: DefinitionInfoId) -> Option<&RefinementType> {
        self.definitions.get(&id)
    }

    pub fn refine_definition<'c>(&mut self, id: DefinitionInfoId, cache: &ModuleCache<'c>) -> Refinement {
        let info = &cache.definition_infos[id.0];

        use crate::cache::DefinitionKind;
        match info.definition {
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
}
