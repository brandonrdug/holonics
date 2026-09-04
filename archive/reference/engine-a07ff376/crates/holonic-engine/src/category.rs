//! A small exact presentation of boundary objects and composable arrows.
//!
//! This is not a claim that category theory replaces computation. It makes
//! the compositional boundary explicit so implementations can be checked
//! against the abstract path they purport to realize.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use thiserror::Error;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct BoundaryId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ArrowId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoundaryObject {
    pub id: BoundaryId,
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoundaryArrow {
    pub id: ArrowId,
    pub name: String,
    pub domain: BoundaryId,
    pub codomain: BoundaryId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CategoryPresentation {
    pub schema: String,
    pub objects: BTreeMap<BoundaryId, BoundaryObject>,
    pub arrows: BTreeMap<ArrowId, BoundaryArrow>,
    next_object: u64,
    next_arrow: u64,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum CategoryError {
    #[error("boundary object {0:?} is absent")]
    MissingObject(BoundaryId),
    #[error("boundary arrow {0:?} is absent")]
    MissingArrow(ArrowId),
    #[error(
        "arrow {right:?} begins at {right_domain:?}, but the preceding arrow ends at {left_codomain:?}"
    )]
    NonComposable {
        right: ArrowId,
        right_domain: BoundaryId,
        left_codomain: BoundaryId,
    },
    #[error("an empty path requires an explicitly supplied boundary object")]
    EmptyPath,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComposablePath {
    pub domain: BoundaryId,
    pub codomain: BoundaryId,
    pub arrows: Vec<ArrowId>,
}

impl Default for CategoryPresentation {
    fn default() -> Self {
        Self {
            schema: "holonic-engine.category-presentation.v1".to_owned(),
            objects: BTreeMap::new(),
            arrows: BTreeMap::new(),
            next_object: 1,
            next_arrow: 1,
        }
    }
}

impl CategoryPresentation {
    pub fn add_object(&mut self, name: impl Into<String>) -> BoundaryId {
        let id = BoundaryId(self.next_object);
        self.next_object += 1;
        self.objects.insert(
            id,
            BoundaryObject {
                id,
                name: name.into(),
            },
        );
        id
    }

    pub fn add_arrow(
        &mut self,
        name: impl Into<String>,
        domain: BoundaryId,
        codomain: BoundaryId,
    ) -> Result<ArrowId, CategoryError> {
        if !self.objects.contains_key(&domain) {
            return Err(CategoryError::MissingObject(domain));
        }
        if !self.objects.contains_key(&codomain) {
            return Err(CategoryError::MissingObject(codomain));
        }
        let id = ArrowId(self.next_arrow);
        self.next_arrow += 1;
        self.arrows.insert(
            id,
            BoundaryArrow {
                id,
                name: name.into(),
                domain,
                codomain,
            },
        );
        Ok(id)
    }

    pub fn identity(&self, object: BoundaryId) -> Result<ComposablePath, CategoryError> {
        if !self.objects.contains_key(&object) {
            return Err(CategoryError::MissingObject(object));
        }
        Ok(ComposablePath {
            domain: object,
            codomain: object,
            arrows: Vec::new(),
        })
    }

    pub fn path(&self, arrows: &[ArrowId]) -> Result<ComposablePath, CategoryError> {
        let first = self
            .arrows
            .get(arrows.first().ok_or(CategoryError::EmptyPath)?)
            .ok_or_else(|| CategoryError::MissingArrow(arrows[0]))?;
        let mut codomain = first.codomain;
        for id in &arrows[1..] {
            let arrow = self
                .arrows
                .get(id)
                .ok_or(CategoryError::MissingArrow(*id))?;
            if arrow.domain != codomain {
                return Err(CategoryError::NonComposable {
                    right: *id,
                    right_domain: arrow.domain,
                    left_codomain: codomain,
                });
            }
            codomain = arrow.codomain;
        }
        Ok(ComposablePath {
            domain: first.domain,
            codomain,
            arrows: arrows.to_vec(),
        })
    }
}

/// One situated programming-object interface.
///
/// `carrier` is the local body exposed at this boundary. A property is an
/// observation arrow out of that body. A method is an afforded process whose
/// parameter boundary and result boundary stay explicit. Neither name nor
/// address is treated as the body's complete identity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObjectInterface {
    pub carrier: BoundaryId,
    pub properties: BTreeMap<String, ArrowId>,
    pub methods: BTreeMap<String, ParameterizedMethod>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParameterizedMethod {
    pub parameter: BoundaryId,
    pub transition: ArrowId,
    pub result: BoundaryId,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_composable_algorithm_path_respects_boundaries() {
        let mut category = CategoryPresentation::default();
        let text = category.add_object("text");
        let tokens = category.add_object("token sequence");
        let incidence = category.add_object("causal incidence");
        let tokenize = category.add_arrow("tokenize", text, tokens).unwrap();
        let relate = category.add_arrow("relate", tokens, incidence).unwrap();
        let path = category.path(&[tokenize, relate]).unwrap();
        assert_eq!(path.domain, text);
        assert_eq!(path.codomain, incidence);
    }

    #[test]
    fn names_do_not_make_noncomposable_arrows_compose() {
        let mut category = CategoryPresentation::default();
        let a = category.add_object("a");
        let b = category.add_object("b");
        let c = category.add_object("c");
        let left = category.add_arrow("same semantic label", a, b).unwrap();
        let right = category.add_arrow("same semantic label", c, a).unwrap();
        assert!(matches!(
            category.path(&[left, right]),
            Err(CategoryError::NonComposable { .. })
        ));
    }
}
