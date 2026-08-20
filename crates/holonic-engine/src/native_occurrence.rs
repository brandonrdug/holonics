//! **The native occurrence: a native rest authenticated by content, witnessing its own laws.**
//!
//! The foreign arm binds its laws through [`crate::source_occurrence::SourceOccurrence`] — an
//! implementation text, a configuration, a container — and refuses any law the source's own
//! testimony does not entail. The native arm has no foreign implementation to authenticate; what it
//! has is **its own rest**: a container it emitted, carrying its atlas as integer populations and,
//! in the container's own metadata slot, the statements of the laws that read them. This module is
//! the witness for that rest, held to the same standard as the foreign one — a law binds only when
//! the rest *declares* it and the populations it reads are *identified* in the rest's header with
//! their shapes and integer carriers — so a native law can no more be authenticated by an unrelated
//! statement than a foreign law by an unrelated slice.
//!
//! **Composition first.** Nothing here re-reads a container: `foreign_map::manifest_safetensors`
//! already parses the header, the metadata and every region, and
//! `source_occurrence::AuthenticatedContainer` already carries the header digest, the whole-content
//! digest, the region identities and `verify_still`. This module is the *witness seam* over them —
//! it decides what testimony a rest may carry — and it owns no reading of its own.
//!
//! Admissible testimony on a native occurrence: [`SourceTestimony::DeclaredShape`] (the population
//! must be a region of the rest with that shape and an integer carrier — the rest's populations
//! cross as integers and nothing else), [`SourceTestimony::AuthoritativeDescription`] (the statement
//! must be one the rest itself carries in its metadata), and the caller's
//! [`SourceTestimony::Intervention`]. An `Implementation` or `Configuration` testimony is foreign to
//! a native rest and refuses at validation: the native arm is independent by construction, not by
//! declaration.

use std::collections::BTreeMap;

use crate::foreign_map::{manifest_safetensors, FileIdentity};
use crate::ported_operation::{OperationSpecies, PortedOperationComplex, SourceTestimony};
use crate::source_occurrence::{AuthenticatedContainer, BindingValidation, OccurrenceWitness, RegionIdentity, SourceRefusal};

/// The native rest as an occurrence: its container, content-addressed, and its own declarations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeOccurrence {
    pub container: AuthenticatedContainer,
    /// The rest's own metadata, verbatim: `key → statement`. A law's description must be one of
    /// these statements.
    pub declarations: BTreeMap<String, String>,
}

impl NativeOccurrence {
    /// Read and authenticate the native rest at `locator`: the header (every region with its shape
    /// and carrier), the container's own metadata, the whole-content digest, and the file identity.
    ///
    /// The digest is always taken here and that is not an identity claim. A path plus its lineage
    /// is the rest's identity; the digest is the apparatus frame — it detects a rest that moved
    /// under the deed, which is exactly what `verify_still` asks after the deed.
    pub fn read(locator: &str) -> Result<Self, SourceRefusal> {
        let (_, manifest) = manifest_safetensors(locator).map_err(|error| SourceRefusal::ContainerMalformed { locator: locator.to_owned(), reason: error.to_string() })?;
        let (octets, header_octets, header_sha256) = AuthenticatedContainer::read_header(locator)?;
        let content_sha256 = AuthenticatedContainer::digest_whole(locator)?;
        let mut regions = BTreeMap::new();
        for (name, tensor) in &manifest.tensors {
            regions.insert(
                name.clone(),
                RegionIdentity { population: name.clone(), dtype: tensor.dtype.declared().to_owned(), shape: tensor.shape.clone(), start: tensor.start, end: tensor.end, sha256: None },
            );
        }
        Ok(Self {
            container: AuthenticatedContainer {
                locator: locator.to_owned(),
                octets,
                header_octets,
                header_sha256,
                content_sha256: Some(content_sha256),
                regions,
                identity: FileIdentity::at(locator).ok(),
            },
            declarations: manifest.container_metadata,
        })
    }

    /// Does the rest itself carry this statement?
    pub fn declares(&self, statement: &str) -> bool {
        self.declarations.values().any(|carried| carried == statement)
    }

    /// Does the rest identify this population as a region of its own header?
    pub fn identifies(&self, population: &str) -> bool {
        self.container.regions.contains_key(population)
    }

    /// The rest's declared shape for one population, as its header states it.
    pub fn shape_of(&self, population: &str) -> Option<&[usize]> {
        self.container.regions.get(population).map(|region| region.shape.as_slice())
    }
}

/// Which carriers a native rest's populations may cross as. Integers, and nothing else: the atlas
/// is class indices, germ indices, standings and offsets, and a float carrier for any of them
/// would put a deleted tail into an address.
fn integer_carrier(dtype: &str) -> bool {
    matches!(dtype, "U8" | "U16" | "U32" | "U64" | "I8" | "I16" | "I32" | "I64")
}

impl OccurrenceWitness for NativeOccurrence {
    fn witness(&self) -> &'static str {
        "native rest"
    }

    fn validate(&self, complex: &PortedOperationComplex) -> Result<Vec<BindingValidation>, SourceRefusal> {
        self.container.verify_still()?;
        let mut validated = Vec::with_capacity(complex.operations.len());
        for operation in complex.operations.values() {
            let name = complex.shape.laws.get(&operation.law).map(|law| law.name.clone()).unwrap_or_default();
            let mut validation = BindingValidation {
                operation: name.clone(),
                species: operation.species,
                symbols: Vec::new(),
                fields: Vec::new(),
                shapes: Vec::new(),
                interventions: Vec::new(),
                descriptions: Vec::new(),
            };
            let mut exterior = false;
            for testimony in &operation.testimony {
                match testimony {
                    SourceTestimony::DeclaredShape { population, shape } => {
                        let region = self.container.regions.get(population).ok_or_else(|| SourceRefusal::PopulationNotIdentified { operation: name.clone(), population: population.clone() })?;
                        if region.shape != *shape {
                            return Err(SourceRefusal::ShapeDiffers { operation: name, population: population.clone(), declared: shape.clone(), measured: region.shape.clone() });
                        }
                        if !integer_carrier(&region.dtype) {
                            return Err(SourceRefusal::DtypeDiffers { operation: name.clone(), population: population.clone(), declared: "an integer carrier".to_owned(), measured: region.dtype.clone() });
                        }
                        validation.shapes.push((population.clone(), shape.clone()));
                        exterior = true;
                    }
                    SourceTestimony::AuthoritativeDescription { statement } => {
                        if !self.declares(statement) {
                            return Err(SourceRefusal::DeclarationNotInRest { operation: name, statement: statement.clone() });
                        }
                        validation.descriptions.push(statement.clone());
                        exterior = true;
                    }
                    SourceTestimony::Intervention { statement } => validation.interventions.push(statement.clone()),
                    SourceTestimony::Implementation { .. } | SourceTestimony::Configuration { .. } => {
                        return Err(SourceRefusal::TestimonyForeignToNativeRest { operation: name, testimony: format!("{testimony:?}") });
                    }
                    SourceTestimony::Undecided { .. } => {}
                }
            }
            if !validation.interventions.is_empty() && exterior && operation.species != OperationSpecies::Quotient {
                return Err(SourceRefusal::InterventionOnSourceLaw { operation: name, species: operation.species });
            }
            if !exterior && validation.interventions.is_empty() {
                return Err(SourceRefusal::TestimonyNotExterior { operation: name, testimony: operation.testimony.iter().map(|t| format!("{t:?}")).collect() });
            }
            if let Some(carrier) = &operation.carrier {
                if !self.identifies(carrier) {
                    return Err(SourceRefusal::PopulationNotIdentified { operation: name, population: carrier.clone() });
                }
            }
            validated.push(validation);
        }
        Ok(validated)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ported_operation::OperationSpecies;

    /// A one-population rest with its own metadata, written to a temporary path. The container is
    /// the format itself — a length, a JSON header, a flat payload — so nothing is mocked.
    fn write_rest(path: &std::path::Path, statement: &str, dtype: &str, rows: usize) {
        let payload: Vec<u8> = vec![1, 0, 0, 0, 2, 0, 0, 0];
        let header = format!(
            "{{\"__metadata__\":{{\"law.walk\":\"{statement}\"}},\"athena.class.suffix\":{{\"dtype\":\"{dtype}\",\"shape\":[{rows},1],\"data_offsets\":[0,8]}}}}"
        );
        let mut header = header.into_bytes();
        while header.len() % 8 != 0 {
            header.push(b' ');
        }
        let mut octets = Vec::new();
        octets.extend_from_slice(&(header.len() as u64).to_le_bytes());
        octets.extend_from_slice(&header);
        octets.extend_from_slice(&payload);
        std::fs::write(path, octets).expect("write the rest");
    }

    fn complex(testimony: Vec<SourceTestimony>) -> PortedOperationComplex {
        let mut complex = PortedOperationComplex::new("a native rest witnessing one law");
        let out = complex.port("landed class");
        complex.bind_operation("athena walk", OperationSpecies::Construction, vec![], vec![out], None, testimony).expect("bound");
        complex
    }

    #[test]
    fn a_native_rest_witnesses_its_own_declaration_and_refuses_an_unrelated_one() {
        let path = std::env::temp_dir().join("holonic-native-occurrence-declares.safetensors");
        write_rest(&path, "the walk falls along the suffix link", "U32", 2);
        let rest = NativeOccurrence::read(path.to_str().expect("path")).expect("read");
        assert_eq!(rest.witness(), "native rest");
        assert!(rest.declares("the walk falls along the suffix link"));
        assert!(!rest.declares("some other statement"));
        assert!(rest.identifies("athena.class.suffix"));
        assert_eq!(rest.shape_of("athena.class.suffix"), Some(&[2usize, 1][..]));

        let declared = complex(vec![
            SourceTestimony::AuthoritativeDescription { statement: "the walk falls along the suffix link".to_owned() },
            SourceTestimony::DeclaredShape { population: "athena.class.suffix".to_owned(), shape: vec![2, 1] },
        ]);
        let validated = rest.validate(&declared).expect("the rest declares it");
        assert_eq!(validated.len(), 1);
        assert_eq!(validated[0].descriptions, vec!["the walk falls along the suffix link".to_owned()]);
        assert_eq!(validated[0].shapes.len(), 1);

        // a statement the rest does not carry refuses, by name
        let undeclared = complex(vec![
            SourceTestimony::AuthoritativeDescription { statement: "a law the rest never declared".to_owned() },
            SourceTestimony::DeclaredShape { population: "athena.class.suffix".to_owned(), shape: vec![2, 1] },
        ]);
        assert!(matches!(rest.validate(&undeclared), Err(SourceRefusal::DeclarationNotInRest { .. })));

        // a population the rest does not identify, and a shape that disagrees, both refuse
        let absent = complex(vec![SourceTestimony::DeclaredShape { population: "athena.class.standing".to_owned(), shape: vec![2, 1] }]);
        assert!(matches!(rest.validate(&absent), Err(SourceRefusal::PopulationNotIdentified { .. })));
        let drifted = complex(vec![SourceTestimony::DeclaredShape { population: "athena.class.suffix".to_owned(), shape: vec![3, 1] }]);
        assert!(matches!(rest.validate(&drifted), Err(SourceRefusal::ShapeDiffers { .. })));

        // **and foreign testimony refuses by TYPE**: a native rest has no implementation text and
        // no configuration, so offering either is not a missing file but a category error.
        let foreign = complex(vec![SourceTestimony::Implementation { locator: "modeling.py".to_owned(), symbol: "Attention.forward".to_owned() }]);
        assert!(matches!(rest.validate(&foreign), Err(SourceRefusal::TestimonyForeignToNativeRest { .. })));
        let configured = complex(vec![SourceTestimony::Configuration { field: "hidden_size".to_owned(), value: "2560".to_owned() }]);
        assert!(matches!(rest.validate(&configured), Err(SourceRefusal::TestimonyForeignToNativeRest { .. })));
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn a_native_rest_refuses_a_population_that_does_not_cross_as_an_integer() {
        let path = std::env::temp_dir().join("holonic-native-occurrence-carrier.safetensors");
        write_rest(&path, "the walk falls along the suffix link", "BF16", 4);
        let rest = NativeOccurrence::read(path.to_str().expect("path")).expect("read");
        let declared = complex(vec![SourceTestimony::DeclaredShape { population: "athena.class.suffix".to_owned(), shape: vec![4, 1] }]);
        assert!(matches!(rest.validate(&declared), Err(SourceRefusal::DtypeDiffers { .. })));
        let _ = std::fs::remove_file(&path);
    }
}
