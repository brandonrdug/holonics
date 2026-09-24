//! **Library intake for an environment-indexed physical occurrence.**
//!
//! [definition] This is item **B2** of
//! `docs/plans/THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md`. Every mmCIF, NumPy and
//! uncertainty adapter in this repository once lived under an example driver
//! (`crates/holonic-life/examples/m5/{cif,npy}.rs`) or inside a test module
//! (`crates/holonic-engine/src/grain_tower/tests.rs::read_all_atoms`), so the exact contact
//! complex, the grain tower and the apertured graded complex had no library path from an exterior
//! file to a founded face. This module is that path, and the M5 deed now reads through it: its
//! `cif.rs` and `npy.rs` retain only the receiver's own two choices — the alpha-carbon
//! representative and the binding of a component by its ordered sequence — and carry no reader of
//! their own. That migration is also the equivalence evidence: the deed returns the same
//! `contacts=70632, shared=40` and the same shortest separator through the library that it
//! returned through its own readers.
//!
//! # What it founds, and what it refuses
//!
//! 1. **All-atom mmCIF.** [`mmcif::StructurePresentation`] retains *every* `_atom_site` row —
//!    there is no alpha-carbon filter and no element filter — as exact rational coordinates. The
//!    coordinate discipline is stated in [`mmcif`]'s header: a token's enclosure is its own last
//!    decimal place, and the scaled integer wire is a separately declared, always-outward
//!    projection. No float parses, stores or decides a coordinate.
//! 2. **Uncertainty.** [`numpy`] admits `<f2`, `<f4` and `<f8` through the exact decoders at
//!    `exact_value::ieee754::decode_binary{16,32,64}_bits`. An IEEE word is an exterior codeword decoded to an exact
//!    dyadic immediately; that is the one lawful place a float bit pattern appears in this path.
//!    A non-finite word is refused by name with its index and its bit pattern.
//! 3. **The environment index.** [`EnvironmentIndex`] carries the [`TargetEcology`], the
//!    [`DesignLineage`] and the [`TokenAddress`] population the array is addressed by.
//!    [`AddressedUncertainty::found`] is the **only** constructor, it takes the index by value,
//!    and it checks that the token population matches the array's extent. There is no `Default`,
//!    no `Option` and no inference: an external predictor that emits only `pae` — Boltz-2 does
//!    exactly this — is refused with [`IntakeRefusal::EnvironmentArraysAbsent`] naming every key
//!    that is missing, until a caller declares the index that run was produced under.
//! 4. **Nothing an exterior file declares ever sizes an allocation.** A ZIP directory's
//!    `uncompressed` extent, a `.npy` `shape` and a `<U*` width are all declarations read before
//!    anything has been decompressed, checksummed or measured. Each is checked against the payload
//!    actually present — `deflate::declared_extent_bound` for the container, `data.len()` for a
//!    member — and each product over them is `checked_mul`. A declaration that cannot be honoured
//!    is [`IntakeRefusal::DeclaredExtentUnbounded`] or [`IntakeRefusal::DeclaredExtentOverflows`],
//!    naming the declaration and the bound. Sized directly, such a field is not a refusal and not
//!    even a panic: it is `handle_alloc_error`, which aborts the process.
//!
//! # What it reaches
//!
//! * [`crate::physical_constraint_complex`] — [`found_constraint_complex`] founds the presented
//!   components, enacts every cross-pair classification on the exact interval arithmetic, and
//!   hands the complex its own audit population together with the directional uncertainty of
//!   every addressed pair.
//! * [`crate::physical_constraint_grading`] — the founded complex is an ordinary argument to
//!   `graded_constraint_family`, so the open class reaches the `2^n` family with no further
//!   adapter.
//! * [`crate::grain_tower`] — [`scaled_component_wire`] emits the atom-grain
//!   [`ScaledOccurrence`] population and [`enact_grain_family`] founds the face, the census, the
//!   inflation witness and the reopen receipt, returning a [`GrainTower`] whose
//!   [`ApertureRelation`] is the measured inflation rather than a default.
//!
//! # The measured receipt
//!
//! [established-bounded; implemented-exact; measured] Over the four M5 cross families —
//! 70,632 residue pairs at an equal 8 Å aperture — the library path returns fine-inside 1,397,
//! coarse-inside 301, fine-only 1,096, coarse-only 0, with the per-family fine-only counts
//! 239 / 307 / 215 / 335. This is the same table `grain_tower/tests.rs` measured through its own
//! test-local reader; that test is retained deliberately, so the number now has two independent
//! readers agreeing rather than one reader asserted twice.
//!
//! # The paired Lean owner
//!
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/ExteriorIntake.lean`, namespace
//! `Soma.Holonics.Foundation.ExteriorIntake`, which names this file and every item below. The
//! citation is bidirectional on purpose.
//!
//! | Lean declaration | Rust owner |
//! |---|---|
//! | `FloatFormat`, `FloatFormat.significandBits`, `binary16 ≤ binary32 ≤ binary64` | [`numpy::UncertaintyWordFormat`], [`numpy::UncertaintyWordFormat::stored_significand_bits`] |
//! | `Codeword`, `Codeword.Finite`, `Codeword.value` | [`numpy::ExactWord`], `exact_value::ieee754::BinaryFloatDatum` |
//! | `decode`, `decode_total_on_finite` | [`numpy::ExactWord::decode`] returning `Ok` for every finite word |
//! | `decode_exact_on_finite` | [`numpy::ExactWord::value`] is the codeword's exact value, never a rounding |
//! | `decode_refuses_nonfinite` | [`IntakeRefusal::NonFiniteUncertaintyWord`] |
//! | `wider_format_carries_every_value`, `binary32_strictly_refines_binary16` | admitting `<f4` beside `<f2` |
//! | `DecimalToken`, `DecimalToken.enclosure` | [`mmcif::DecimalToken`], [`mmcif::DecimalToken::source_enclosure`] |
//! | `projectOutward`, `projection_contains_source` | [`mmcif::DecimalToken::projected_wire`] |
//! | `widening_never_flips_a_decision` | the coordinate discipline of [`mmcif`] |
//! | `EnvironmentIndex`, `TargetEcology`, `DesignLineage` | [`EnvironmentIndex`], [`TargetEcology`], [`DesignLineage`] |
//! | `Occurrence`, `Occurrence.environment` | [`AddressedUncertainty`], [`AddressedUncertainty::environment`] |
//! | `foundWith`, `found`, `found_none_of_environment_absent`, `found_environment`, `no_occurrence_without_environment` | [`AddressedUncertainty::found`], [`EnvironmentIndex::from_numpy_source`] |
//! | `addressedPairs`, `addressed_pair_population`, `reading_total_on_addressed_pairs` | [`AddressedUncertainty::pair_uncertainty`] |
//! | `reading_is_directional` | `PairUncertainty::{row_given_column, column_given_row}` retained separately |
//!
//! Every one of those elaborates with no `sorryAx`.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use num_bigint::{BigInt, BigUint};
use num_traits::One;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::EventId;
use holonics::exact_value::ExactInterval;
use crate::grain_tower::{
    ApertureRelation, Grain, GrainAddress, GrainCell, GrainCensus, GrainFace,
    GrainPair, GrainRefusal, GrainReopenReceipt, GrainSelection, GrainTower, InflationWitness,
    ScaledAperture, ScaledOccurrence, check_grain_reopen, coarse_readings, found_atom_face,
    rational_root_upper_bound,
};
use crate::physical_constraint_complex::{
    ComponentMaterial, ConstraintComponentId, ConstraintError, ConstraintVertexId, ContactClass,
    DistanceAperture, PairUncertainty, PhysicalConstraintComplex, ResidueMaterial,
};
use crate::physical_constraint_grading::{
    ConstraintComplexFamily, ConstraintGradingError, graded_constraint_family,
};

mod deflate;
pub mod mmcif;
pub mod numpy;

use holonics::restriction::tower::Transition;
use mmcif::{ChainOccurrence, StructurePresentation};
use numpy::{ExactWord, NumpySource, UncertaintyWordFormat};

/// The eleven arrays the M5 uncertainty wire carries. `pae` alone is the array; the other ten are
/// the environment and lineage the array was produced under.
///
/// [definition] This is not a convention this module invented. It is the `TargetEcology` /
/// `DesignLineage` contract already sitting in the released wire format, named so that a reader
/// that carries only `pae` can be told exactly what it is missing.
pub const ENVIRONMENT_ARRAYS: [&str; 11] = [
    "pae.npy",
    "token_chain_ids.npy",
    "token_res_ids.npy",
    "token_entity.npy",
    "design_uuid.npy",
    "design_name.npy",
    "target.npy",
    "cofolding_model.npy",
    "stoichiometry.npy",
    "target_form.npy",
    "seed.npy",
];

/// The array carrying the uncertainty itself, as distinct from its environment.
pub const UNCERTAINTY_ARRAY: &str = "pae.npy";

// ---------------------------------------------------------------------------------------------
// The environment index and the lineage
// ---------------------------------------------------------------------------------------------

/// The environment `eta` one prediction was produced under.
///
/// [definition] These are the coordinates the released wire actually names. An empty value is
/// *presented testimony that the coordinate was left blank*, which is different from an absent
/// array, and [`Self::blank_coordinates`] names the blanks without refusing them.
///
/// Lean counterpart: `Foundation/ExteriorIntake.lean::TargetEcology`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct TargetEcology {
    /// The addressed target.
    pub target: String,
    /// Which conformational or assembly form of that target was presented.
    pub target_form: String,
    /// The presented stoichiometry.
    pub stoichiometry: String,
    /// The cofolding model that produced the prediction.
    pub cofolding_model: String,
}

impl TargetEcology {
    /// Which declared coordinates are present but blank. A blank is retained, not defaulted.
    pub fn blank_coordinates(&self) -> Vec<&'static str> {
        let mut blank = Vec::new();
        for (name, value) in [
            ("target", &self.target),
            ("target_form", &self.target_form),
            ("stoichiometry", &self.stoichiometry),
            ("cofolding_model", &self.cofolding_model),
        ] {
            if value.is_empty() {
                blank.push(name);
            }
        }
        blank
    }
}

/// The causal lineage of the design the prediction was made about.
///
/// Lean counterpart: `Foundation/ExteriorIntake.lean::DesignLineage`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct DesignLineage {
    /// The design's stable identifier.
    pub design_uuid: String,
    /// The design's presented name.
    pub design_name: String,
    /// The sampling seed of this particular prediction occurrence.
    pub seed: String,
}

/// One row and column address of the uncertainty array.
///
/// Lean counterpart: `Foundation/ExteriorIntake.lean::TokenAddress`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct TokenAddress {
    /// The chain this token belongs to, as the predictor labelled it.
    pub chain: String,
    /// The residue ordinal within that chain.
    pub residue: i32,
    /// The entity class the predictor assigned, when it presented one.
    pub entity: Option<String>,
}

/// Where an environment index came from.
///
/// [definition] There are exactly two lawful provenances and no third. Either the wire carried
/// the environment arrays, or a caller declared the index for a predictor that emits only the
/// uncertainty array. A declaration is retained *as a declaration* so a consumer can see that the
/// index is exterior testimony rather than something the run itself recorded.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum EnvironmentProvenance {
    /// Read out of the source's own arrays, with the member names that supplied it.
    CarriedByArrays {
        /// The source the arrays were read from.
        source: String,
    },
    /// Declared by a caller for a predictor that emits only the uncertainty array.
    DeclaredByCaller {
        /// Who declared it and on what ground, retained as testimony.
        declaration: String,
    },
}

/// The complete environment index one uncertainty array was produced under.
///
/// Lean counterpart: `Foundation/ExteriorIntake.lean::EnvironmentIndex`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EnvironmentIndex {
    /// The schema this index serializes under.
    pub schema: String,
    /// How this index came to exist.
    pub provenance: EnvironmentProvenance,
    /// The environment.
    pub ecology: TargetEcology,
    /// The design lineage.
    pub lineage: DesignLineage,
    /// The addressed token population, in array order.
    pub tokens: Vec<TokenAddress>,
}

impl EnvironmentIndex {
    /// Read the index out of a source that carries the environment arrays.
    ///
    /// Every absent array is named in one refusal, so a caller learns the whole gap at once rather
    /// than one key per attempt.
    pub fn from_numpy_source(source: &NumpySource) -> Result<Self, IntakeRefusal> {
        let absent = ENVIRONMENT_ARRAYS
            .iter()
            .filter(|name| !source.members.contains_key(**name))
            .map(|name| (*name).to_owned())
            .collect::<Vec<_>>();
        if !absent.is_empty() {
            return Err(IntakeRefusal::EnvironmentArraysAbsent {
                origin: source.lineage.clone(),
                absent,
                present: source.member_names(),
            });
        }
        let scalar = |name: &str| -> Result<String, IntakeRefusal> {
            source.member(name)?.unicode_scalar()
        };
        let chains = source.member("token_chain_ids.npy")?.unicode_words()?;
        let residues = source.member("token_res_ids.npy")?.i32_words()?;
        let entities = source.member("token_entity.npy")?.unicode_words()?;
        if chains.len() != residues.len() || chains.len() != entities.len() {
            return Err(IntakeRefusal::TokenFacesDisagree {
                origin: source.lineage.clone(),
                chains: chains.len(),
                residues: residues.len(),
                entities: entities.len(),
            });
        }
        let tokens = chains
            .into_iter()
            .zip(residues)
            .zip(entities)
            .map(|((chain, residue), entity)| TokenAddress {
                chain,
                residue,
                entity: Some(entity),
            })
            .collect();
        Ok(Self {
            schema: "holonic-engine.environment-index.v1".to_owned(),
            provenance: EnvironmentProvenance::CarriedByArrays {
                source: source.lineage.clone(),
            },
            ecology: TargetEcology {
                target: scalar("target.npy")?,
                target_form: scalar("target_form.npy")?,
                stoichiometry: scalar("stoichiometry.npy")?,
                cofolding_model: scalar("cofolding_model.npy")?,
            },
            lineage: DesignLineage {
                design_uuid: scalar("design_uuid.npy")?,
                design_name: scalar("design_name.npy")?,
                seed: scalar("seed.npy")?,
            },
            tokens,
        })
    }

    /// Declare an index for a predictor that emits only the uncertainty array.
    ///
    /// The declaration text is required and is retained: an index with no stated ground is not a
    /// declaration, it is a default, and this intake founds no defaults.
    pub fn declared(
        declaration: impl Into<String>,
        ecology: TargetEcology,
        lineage: DesignLineage,
        tokens: Vec<TokenAddress>,
    ) -> Result<Self, IntakeRefusal> {
        let declaration = declaration.into();
        if declaration.trim().is_empty() {
            return Err(IntakeRefusal::EnvironmentDeclarationEmpty);
        }
        if tokens.is_empty() {
            return Err(IntakeRefusal::EnvironmentDeclarationEmpty);
        }
        Ok(Self {
            schema: "holonic-engine.environment-index.v1".to_owned(),
            provenance: EnvironmentProvenance::DeclaredByCaller { declaration },
            ecology,
            lineage,
            tokens,
        })
    }

    /// The array index of one addressed token.
    pub fn token_index(&self, chain: &str, residue: i32) -> Result<usize, IntakeRefusal> {
        self.tokens
            .iter()
            .position(|token| token.chain == chain && token.residue == residue)
            .ok_or_else(|| IntakeRefusal::TokenAbsent {
                chain: chain.to_owned(),
                residue,
            })
    }

    /// Whether every token address occurs exactly once. A repeated address makes the array's
    /// addressing ambiguous and is refused by [`AddressedUncertainty::found`].
    pub fn addresses_are_distinct(&self) -> bool {
        let distinct = self
            .tokens
            .iter()
            .map(|token| (token.chain.as_str(), token.residue))
            .collect::<BTreeSet<_>>();
        distinct.len() == self.tokens.len()
    }
}

// ---------------------------------------------------------------------------------------------
// The uncertainty array
// ---------------------------------------------------------------------------------------------

/// A square directional uncertainty array, retained as exterior codewords with its format.
///
/// [definition] The codewords are retained rather than the decoded rationals because decoding is
/// exact and total on finite words: the decoded value is recoverable at any time and materializing
/// `extent²` rationals up front would carry nothing the word does not already determine. The
/// non-finite scan happens **once, at founding**, so an array that reaches a consumer carries only
/// words that decode.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UncertaintyArray {
    /// The schema this array serializes under.
    pub schema: String,
    /// Exterior lineage of the source, retained as testimony.
    pub source_lineage: String,
    /// The format every word is stored in.
    pub format: UncertaintyWordFormat,
    /// The square extent.
    pub extent: usize,
    /// How many words decoded to a finite exact dyadic. Equals `extent²` for an admitted array.
    pub finite_words: usize,
    /// The declared reading law, retained in the artifact so a consumer reads it.
    pub reading_law: String,
    words: Vec<u64>,
}

impl UncertaintyArray {
    /// Found an array from its codewords, refusing the first non-finite word by name.
    pub fn found(
        source_lineage: impl Into<String>,
        format: UncertaintyWordFormat,
        shape: &[usize],
        words: Vec<u64>,
    ) -> Result<Self, IntakeRefusal> {
        let source_lineage = source_lineage.into();
        if shape.len() != 2 || shape[0] != shape[1] {
            return Err(IntakeRefusal::UncertaintyNotSquare {
                origin: source_lineage,
                shape: shape.to_vec(),
            });
        }
        let extent = shape[0];
        // `extent` is a declared header field, so `extent²` is taken with `checked_mul`: a wrapped
        // square could make this very check pass for a payload that does not carry the array.
        let declared = extent.checked_mul(extent).ok_or_else(|| {
            IntakeRefusal::DeclaredExtentOverflows {
                member: source_lineage.clone(),
                detail: format!("the square extent {extent}, whose cell count"),
            }
        })?;
        if words.len() != declared {
            return Err(IntakeRefusal::UncertaintyExtentDisagrees {
                origin: source_lineage,
                extent,
                words: words.len(),
            });
        }
        for (index, word) in words.iter().enumerate() {
            ExactWord::decode(format, index, *word)?;
        }
        let finite_words = words.len();
        Ok(Self {
            schema: "holonic-engine.uncertainty-array.v1".to_owned(),
            source_lineage,
            format,
            extent,
            finite_words,
            reading_law: format!(
                "every {} word is decoded as its exact IEEE dyadic and retained as a point, with \
                 the format's unit in the last place carried separately; a predictor's stored \
                 uncertainty is testimony about a prediction and is neither a coordinate \
                 enclosure nor a physical measurement",
                format.descr()
            ),
            words,
        })
    }

    /// Read the uncertainty array out of a NumPy source.
    pub fn from_numpy_source(source: &NumpySource) -> Result<Self, IntakeRefusal> {
        let member = source.member(UNCERTAINTY_ARRAY)?;
        let (format, words) = member.float_words()?;
        Self::found(source.lineage.clone(), format, &member.shape, words)
    }

    /// The exact decoding of one cell. Row and column are **not** symmetrized.
    pub fn word(&self, row: usize, column: usize) -> Result<ExactWord, IntakeRefusal> {
        if row >= self.extent || column >= self.extent {
            return Err(IntakeRefusal::UncertaintyCellOutOfRange {
                origin: self.source_lineage.clone(),
                extent: self.extent,
                row,
                column,
            });
        }
        let index = row * self.extent + column;
        ExactWord::decode(self.format, index, self.words[index])
    }
}

/// An uncertainty array **together with the environment index it was produced under**.
///
/// [definition] There is exactly one constructor, [`Self::found`], and it takes the index by
/// value. No path in this module produces an [`AddressedUncertainty`] whose environment is absent,
/// defaulted or inferred. That is the whole content of `B2`'s third clause, stated as a type.
///
/// Lean counterpart: `Foundation/ExteriorIntake.lean::Occurrence`, whose `environment` field is
/// likewise a field of the structure and not an option.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AddressedUncertainty {
    /// The schema this occurrence serializes under.
    pub schema: String,
    environment: EnvironmentIndex,
    array: UncertaintyArray,
}

impl AddressedUncertainty {
    /// Found the occurrence. The token population must address the array exactly: one distinct
    /// address per row, and as many addresses as the array has rows.
    pub fn found(
        environment: EnvironmentIndex,
        array: UncertaintyArray,
    ) -> Result<Self, IntakeRefusal> {
        if environment.tokens.len() != array.extent {
            return Err(IntakeRefusal::TokenPopulationDisagrees {
                origin: array.source_lineage.clone(),
                extent: array.extent,
                tokens: environment.tokens.len(),
            });
        }
        if !environment.addresses_are_distinct() {
            return Err(IntakeRefusal::TokenAddressRepeated {
                origin: array.source_lineage.clone(),
            });
        }
        Ok(Self {
            schema: "holonic-engine.addressed-uncertainty-occurrence.v1".to_owned(),
            environment,
            array,
        })
    }

    /// Read a complete source that carries its own environment arrays.
    pub fn read_self_indexed(path: &Path) -> Result<Self, IntakeRefusal> {
        let source = NumpySource::read(path)?;
        let environment = EnvironmentIndex::from_numpy_source(&source)?;
        let array = UncertaintyArray::from_numpy_source(&source)?;
        Self::found(environment, array)
    }

    /// Read a source that carries only the uncertainty array, under a declared environment index.
    ///
    /// This is the Boltz-shaped path. Without the declaration there is no constructor to call.
    pub fn read_with_declared_environment(
        path: &Path,
        environment: EnvironmentIndex,
    ) -> Result<Self, IntakeRefusal> {
        let source = NumpySource::read(path)?;
        let array = UncertaintyArray::from_numpy_source(&source)?;
        Self::found(environment, array)
    }

    /// The environment index. Total, because the occurrence cannot exist without it.
    pub fn environment(&self) -> &EnvironmentIndex {
        &self.environment
    }

    /// The array.
    pub fn array(&self) -> &UncertaintyArray {
        &self.array
    }

    /// The directional codewords of one addressed pair, both retained whole.
    pub fn directional_words(
        &self,
        left_chain: &str,
        left_residue: i32,
        right_chain: &str,
        right_residue: i32,
    ) -> Result<(ExactWord, ExactWord), IntakeRefusal> {
        let row = self.environment.token_index(left_chain, left_residue)?;
        let column = self.environment.token_index(right_chain, right_residue)?;
        Ok((self.array.word(row, column)?, self.array.word(column, row)?))
    }

    /// The directional uncertainty of every pair in one declared cross population, keyed by the
    /// one-based ordinals `physical_constraint_complex::found_contact_family` addresses.
    ///
    /// [proved-derived; formal-checked] The return is total on the addressed population and
    /// invents nothing outside it: its cardinality is exactly `|left| · |right|`, which is
    /// `Foundation/ExteriorIntake.lean::{addressed_pair_population,
    /// reading_total_on_addressed_pairs}`.
    ///
    /// The `*_bits` fields of [`PairUncertainty`] are a sixteen-bit testimony face of the existing
    /// wire type. For a `<f4` or `<f8` source they carry the low sixteen bits of the codeword; the
    /// **exact** value never passes through them — it is carried whole in `row_given_column` and
    /// `column_given_row`, and the complete codeword is available from [`Self::directional_words`].
    pub fn pair_uncertainty(
        &self,
        left_chain: &str,
        left_residues: &[i32],
        right_chain: &str,
        right_residues: &[i32],
    ) -> Result<BTreeMap<(u32, u32), PairUncertainty>, IntakeRefusal> {
        let mut result = BTreeMap::new();
        for (left_at, left_residue) in left_residues.iter().enumerate() {
            for (right_at, right_residue) in right_residues.iter().enumerate() {
                let (row, column) = self.directional_words(
                    left_chain,
                    *left_residue,
                    right_chain,
                    *right_residue,
                )?;
                result.insert(
                    (left_at as u32 + 1, right_at as u32 + 1),
                    PairUncertainty {
                        source_lineage: format!(
                            "{} / directional uncertainty {left_chain}:{left_residue}<->\
                             {right_chain}:{right_residue} / environment {} seed {}",
                            self.array.source_lineage,
                            self.environment.ecology.target_form,
                            self.environment.lineage.seed
                        ),
                        row_given_column_bits: row.low_sixteen_bits(),
                        column_given_row_bits: column.low_sixteen_bits(),
                        row_given_column: ExactInterval::point(row.value.clone()),
                        column_given_row: ExactInterval::point(column.value.clone()),
                        row_given_column_ulp: row.unit_in_last_place.clone(),
                        column_given_row_ulp: column.unit_in_last_place.clone(),
                    },
                );
            }
        }
        Ok(result)
    }
}

// ---------------------------------------------------------------------------------------------
// The path into `physical_constraint_complex` and `physical_constraint_grading`
// ---------------------------------------------------------------------------------------------

/// At what grain a chain is presented to the constraint complex.
///
/// [definition] `Atom` presents every atom as its own vertex; the polygonal chain is then the
/// presentation's own atom order. `Representative` presents one declared atom per residue, which
/// is the receiver `crates/holonic-life/examples/m5/cif.rs::REPRESENTATIVE` enacts. Naming it a *selection*
/// rather than a restriction is deliberate: `grain_tower.rs::GrainSelection` proves it is not the
/// restriction, and this enum keeps the two distinguishable at intake.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ComponentGrain {
    /// Every atom becomes a vertex.
    Atom,
    /// One declared atom per residue becomes a vertex.
    Representative {
        /// The `_atom_site.label_atom_id` of the representative, for example `"CA"`.
        atom_label: String,
    },
}

impl ComponentGrain {
    /// A short name for receipts.
    pub fn name(&self) -> String {
        match self {
            Self::Atom => "atom".to_owned(),
            Self::Representative { atom_label } => format!("representative({atom_label})"),
        }
    }
}

/// The [`ComponentMaterial`] of one chain at a declared grain, on a declared resident denominator.
pub fn component_material(
    chain: &ChainOccurrence,
    presentation_lineage: &str,
    grain: &ComponentGrain,
    resident_decimal_places: u32,
) -> Result<ComponentMaterial, IntakeRefusal> {
    let mut residues = Vec::new();
    for residue in &chain.residues {
        match grain {
            ComponentGrain::Atom => {
                for atom in &residue.atoms {
                    residues.push(ResidueMaterial {
                        source_ordinal: residue.source_ordinal,
                        monomer: format!("{}:{}", residue.monomer, atom.label),
                        position: atom.projected_box(resident_decimal_places)?,
                    });
                }
            }
            ComponentGrain::Representative { atom_label } => {
                let at = residue.labelled_atom(atom_label)?.ok_or_else(|| {
                    IntakeRefusal::RepresentativeAtomAbsent {
                        chain: chain.label_asym_id.clone(),
                        residue: residue.source_ordinal,
                        label: atom_label.clone(),
                    }
                })?;
                residues.push(ResidueMaterial {
                    source_ordinal: residue.source_ordinal,
                    monomer: residue.monomer.clone(),
                    position: residue.atoms[at].projected_box(resident_decimal_places)?,
                });
            }
        }
    }
    Ok(ComponentMaterial {
        lineage: format!(
            "{presentation_lineage} / source chain {} / grain {} / outward resident decimal \
             projection 10^-{resident_decimal_places}",
            chain.label_asym_id,
            grain.name()
        ),
        residues,
    })
}

/// The residue source ordinal addressing each vertex of [`component_material`], in vertex order.
///
/// An atom-grain presentation repeats its residue's ordinal once per atom, which is exactly how an
/// atom pair inherits the uncertainty of the residue pair the predictor addressed.
pub fn component_vertex_tokens(
    chain: &ChainOccurrence,
    grain: &ComponentGrain,
) -> Result<Vec<i32>, IntakeRefusal> {
    let mut tokens = Vec::new();
    for residue in &chain.residues {
        match grain {
            ComponentGrain::Atom => {
                for _ in &residue.atoms {
                    tokens.push(residue.source_ordinal);
                }
            }
            ComponentGrain::Representative { atom_label } => {
                if residue.labelled_atom(atom_label)?.is_none() {
                    return Err(IntakeRefusal::RepresentativeAtomAbsent {
                        chain: chain.label_asym_id.clone(),
                        residue: residue.source_ordinal,
                        label: atom_label.clone(),
                    });
                }
                tokens.push(residue.source_ordinal);
            }
        }
    }
    Ok(tokens)
}

/// How one cross family is presented to the exact constraint complex: at what grain, on what
/// resident denominator, and against what aperture.
///
/// These three travel together because they are one declaration: a grain without a denominator has
/// no coordinates, and a denominator without an aperture decides nothing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContactPresentation {
    /// At what grain each chain becomes a component.
    pub grain: ComponentGrain,
    /// The resident denominator `10^resident_decimal_places` every coordinate is projected onto.
    pub resident_decimal_places: u32,
    /// The aperture the cross family is classified against.
    pub aperture: DistanceAperture,
}

/// One declared cross family for [`found_constraint_complex`].
#[derive(Clone, Debug)]
pub struct PresentedFamily {
    /// The left component.
    pub left: ConstraintComponentId,
    /// The right component.
    pub right: ConstraintComponentId,
    /// The aperture this family is classified against.
    pub aperture: DistanceAperture,
    /// The directional uncertainty of every addressed pair.
    pub uncertainty: BTreeMap<(u32, u32), PairUncertainty>,
}

/// Found the exact constraint complex of a declared component population and its cross families.
///
/// [definition] The classification handed to
/// `PhysicalConstraintComplex::found_contact_family` is enacted here on the same exact interval
/// arithmetic the complex audits with, so on this CPU path the audit is a redundancy check rather
/// than an independent one. That is stated rather than hidden: the audit exists for a *resident*
/// carrier, and when one enacts the family the intake's classification is the thing being checked.
pub fn found_constraint_complex(
    presentation_lineage: &str,
    source_event: EventId,
    materials: Vec<ComponentMaterial>,
    families: Vec<PresentedFamily>,
) -> Result<PhysicalConstraintComplex, IntakeRefusal> {
    let mut complex =
        PhysicalConstraintComplex::found(presentation_lineage, source_event, materials)?;
    for family in families {
        let enacted = enacted_classes(&complex, family.left, family.right, &family.aperture)?;
        complex.found_contact_family(
            family.left,
            family.right,
            family.aperture,
            &enacted,
            &family.uncertainty,
        )?;
    }
    Ok(complex)
}

/// The exact class of every pair of one declared cross population, in the row-major order
/// `found_contact_family` reads.
pub fn enacted_classes(
    complex: &PhysicalConstraintComplex,
    left: ConstraintComponentId,
    right: ConstraintComponentId,
    aperture: &DistanceAperture,
) -> Result<Vec<ContactClass>, IntakeRefusal> {
    let left_vertices = complex.component(left)?.vertices.clone();
    let right_vertices = complex.component(right)?.vertices.clone();
    let mut enacted = Vec::with_capacity(left_vertices.len() * right_vertices.len());
    for left_vertex in &left_vertices {
        for right_vertex in &right_vertices {
            let distance = complex.vertices[left_vertex]
                .position
                .squared_distance(&complex.vertices[right_vertex].position);
            enacted.push(aperture.classify(&distance));
        }
    }
    Ok(enacted)
}

/// The exact class of every pair of one component's **within-component** population, in the
/// canonical order `found_within_component_contact_family` reads: ascending `i`, then ascending
/// `j`, over the unordered pairs whose chain positions differ by at least `minimum_separation`.
///
/// The same admission audit applies as for [`enacted_classes`]: on this CPU path the classification
/// and the check share one interval arithmetic, and the audit exists for a resident carrier.
pub fn enacted_within_component_classes(
    complex: &PhysicalConstraintComplex,
    component: ConstraintComponentId,
    minimum_separation: u32,
    aperture: &DistanceAperture,
) -> Result<Vec<ContactClass>, IntakeRefusal> {
    let vertices = complex.component(component)?.vertices.clone();
    let pairs = complex.within_component_pairs(component, minimum_separation)?;
    let mut enacted = Vec::with_capacity(pairs.len());
    let at = |ordinal: u32| -> Result<ConstraintVertexId, IntakeRefusal> {
        vertices
            .get(ordinal as usize - 1)
            .copied()
            .ok_or(IntakeRefusal::Constraint(
                ConstraintError::MissingComponent(component),
            ))
    };
    for (left_ordinal, right_ordinal) in pairs {
        let left_vertex = at(left_ordinal)?;
        let right_vertex = at(right_ordinal)?;
        let distance = complex.vertices[&left_vertex]
            .position
            .squared_distance(&complex.vertices[&right_vertex].position);
        enacted.push(aperture.classify(&distance));
    }
    Ok(enacted)
}

/// The apertured graded family of a founded complex, so the open class reaches
/// [`crate::physical_constraint_grading`] with no further adapter.
pub fn graded_family(
    complex: &PhysicalConstraintComplex,
) -> Result<ConstraintComplexFamily, IntakeRefusal> {
    Ok(graded_constraint_family(complex)?)
}

// ---------------------------------------------------------------------------------------------
// The path into `grain_tower`
// ---------------------------------------------------------------------------------------------

/// One presented chain on the atom-grain scaled wire, with its declared representative located.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScaledComponentWire {
    /// Exterior lineage of the component, retained as testimony.
    pub lineage: String,
    /// The component coordinate of every address in this wire.
    pub component: u32,
    /// Every atom, addressed at all three grains.
    pub atoms: Vec<ScaledOccurrence>,
    /// How many residues the chain presents.
    pub residues: usize,
    /// The address of each residue's declared representative, in residue order.
    pub representatives: Vec<GrainAddress>,
    /// The residue source ordinals, in residue order.
    pub source_ordinals: Vec<i32>,
}

/// Emit the atom-grain scaled wire of one chain on a declared resident denominator.
///
/// Every atom is retained. `representative_label` names the atom each residue's *selection*
/// receiver reads; a residue with no such atom, or with two, is refused by name.
pub fn scaled_component_wire(
    chain: &ChainOccurrence,
    lineage: impl Into<String>,
    component: u32,
    resident_decimal_places: u32,
    representative_label: &str,
) -> Result<ScaledComponentWire, IntakeRefusal> {
    let mut atoms = Vec::with_capacity(chain.atom_occurrences);
    let mut representatives = Vec::with_capacity(chain.residues.len());
    let mut source_ordinals = Vec::with_capacity(chain.residues.len());
    for (residue_at, residue) in chain.residues.iter().enumerate() {
        let residue_ordinal = residue_at as u32 + 1;
        let representative = residue.labelled_atom(representative_label)?.ok_or_else(|| {
            IntakeRefusal::RepresentativeAtomAbsent {
                chain: chain.label_asym_id.clone(),
                residue: residue.source_ordinal,
                label: representative_label.to_owned(),
            }
        })?;
        representatives.push(GrainAddress::new(
            component,
            residue_ordinal,
            representative as u32 + 1,
        ));
        source_ordinals.push(residue.source_ordinal);
        for (atom_at, atom) in residue.atoms.iter().enumerate() {
            let (lower, upper) = atom.projected_wire(resident_decimal_places)?;
            atoms.push(ScaledOccurrence {
                address: GrainAddress::new(component, residue_ordinal, atom_at as u32 + 1),
                label: atom.label.clone(),
                lower,
                upper,
            });
        }
    }
    Ok(ScaledComponentWire {
        lineage: lineage.into(),
        component,
        atoms,
        residues: chain.residues.len(),
        representatives,
        source_ordinals,
    })
}

/// What one cross family returns when the atom grain is founded and the selection receiver is
/// compared against its restriction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GrainFamilyReturn {
    /// Exterior lineage of the family.
    pub lineage: String,
    /// The exact pair table.
    pub census: GrainCensus,
    /// The inflation the selection receiver actually needs on this family.
    pub inflation: InflationWitness,
    /// The reopen receipt of the selection's residual.
    pub reopen: GrainReopenReceipt,
    /// The tower, carrying the measured inflation as its declared relation.
    pub tower: GrainTower,
}

/// Found the atom-grain face of one cross family, restrict it, read it with the selection
/// receiver, and return the census, the inflation witness, the reopen receipt and the tower.
///
/// This is the library owner of what `grain_tower/tests.rs::enact_family` enacts test-locally.
pub fn enact_grain_family(
    lineage: impl Into<String>,
    left: &ScaledComponentWire,
    right: &ScaledComponentWire,
    aperture: &ScaledAperture,
    representative_lineage: &str,
) -> Result<GrainFamilyReturn, IntakeRefusal> {
    let lineage = lineage.into();
    if aperture.denominator == 0 {
        return Err(IntakeRefusal::Grain(GrainRefusal::ZeroDenominator));
    }
    let denominator = BigUint::from(aperture.denominator);
    let fine_aperture_squared = aperture.exact()?.squared;

    let atom_face = found_atom_face(&left.atoms, &right.atoms, aperture)?;
    let fine = atom_face.restricted(Grain::Residue)?;

    let selection = GrainSelection::declare(
        representative_lineage,
        Grain::Residue,
        Grain::Atom,
        left.representatives
            .iter()
            .chain(right.representatives.iter())
            .copied(),
    )?;
    let coarse = selection.apply(&atom_face);

    let census = GrainCensus::measure(
        lineage.clone(),
        left.residues * right.residues,
        &fine,
        &coarse,
    )?;
    let reopen = check_grain_reopen(&selection, &atom_face)?;

    let (positions, radii) = grain_radii(&[left, right], &denominator)?;
    let forcing = forcing_witnesses(&atom_face, &fine)?;
    let readings = coarse_readings(
        &selection,
        &fine,
        &positions,
        &radii,
        &denominator,
        &forcing,
    )?;
    let inflation =
        InflationWitness::measure(lineage.clone(), fine_aperture_squared, &readings)?;
    let tower = GrainTower::found(
        lineage.clone(),
        ApertureRelation::InflatedCoarse(Box::new(inflation.clone())),
        atom_face,
    )?;
    Ok(GrainFamilyReturn {
        lineage,
        census,
        inflation,
        reopen,
        tower,
    })
}

/// The representative positions and measured grain radii of one component population.
type GrainGeometry = (
    BTreeMap<GrainCell, ScaledOccurrence>,
    BTreeMap<GrainCell, Rat>,
);

/// The exact position of each residue's representative, and the measured grain radius of each
/// residue as an exact rational upper bound.
fn grain_radii(
    components: &[&ScaledComponentWire],
    denominator: &BigUint,
) -> Result<GrainGeometry, IntakeRefusal> {
    let root_denominator = BigUint::from(1_000_000_u32);
    let squared_denominator = {
        let den = BigInt::from(denominator.clone());
        Rat::new(BigInt::one(), &den * &den)
    };
    let mut positions: BTreeMap<GrainCell, ScaledOccurrence> = BTreeMap::new();
    let mut radii: BTreeMap<GrainCell, Rat> = BTreeMap::new();
    for component in components {
        let representative_of = component
            .representatives
            .iter()
            .map(|address| (address.cell(Grain::Residue), *address))
            .collect::<BTreeMap<_, _>>();
        for occurrence in &component.atoms {
            let residue_cell = occurrence.address.cell(Grain::Residue);
            let Some(representative) = representative_of.get(&residue_cell) else {
                return Err(IntakeRefusal::Grain(GrainRefusal::NoRepresentative {
                    cell: residue_cell,
                }));
            };
            if occurrence.address == *representative {
                positions.insert(occurrence.address.cell(Grain::Atom), occurrence.clone());
            }
        }
        for occurrence in &component.atoms {
            let residue_cell = occurrence.address.cell(Grain::Residue);
            let representative = representative_of[&residue_cell].cell(Grain::Atom);
            let position = positions.get(&representative).ok_or(IntakeRefusal::Grain(
                GrainRefusal::NoRepresentative {
                    cell: representative,
                },
            ))?;
            let (_, high) = ScaledAperture::squared_distance(position, occurrence)?;
            let squared = &Rat::from_integer(BigInt::from(high)) * &squared_denominator;
            let bound = rational_root_upper_bound(&squared, &root_denominator)?;
            let entry = radii.entry(residue_cell).or_insert_with(|| bound.clone());
            if bound > *entry {
                *entry = bound;
            }
        }
    }
    Ok((positions, radii))
}

/// For each coarse pair, the fine pair whose class the restriction's join took.
fn forcing_witnesses(
    atom_face: &GrainFace,
    fine: &GrainFace,
) -> Result<BTreeMap<GrainPair, GrainPair>, IntakeRefusal> {
    let mut forcing = BTreeMap::new();
    for (pair, class) in atom_face.classified() {
        let Some(coarse_pair) = pair.project(Grain::Residue)? else {
            continue;
        };
        if *class == fine.class(&coarse_pair) {
            forcing.entry(coarse_pair).or_insert(*pair);
        }
    }
    Ok(forcing)
}

/// The summed pair table of several cross families, and the coarse aperture the whole population
/// forces.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GrainCensusTotals {
    /// The complete declared pair population.
    pub pairs: usize,
    /// Pairs the fine restriction reads `Inside`.
    pub fine_inside: usize,
    /// Pairs the fine restriction reads `Open`.
    pub fine_open: usize,
    /// Pairs the selection receiver reads `Inside`.
    pub coarse_inside: usize,
    /// Pairs the selection receiver reads `Open`.
    pub coarse_open: usize,
    /// Fine `Inside`, coarse not `Inside`.
    pub fine_only_inside: usize,
    /// Coarse `Inside`, fine not `Inside`. Zero is a theorem, measured rather than assumed.
    pub coarse_only_inside: usize,
    /// Pairs both readings leave `Open`.
    pub open_shared: usize,
    /// The least coarse aperture squared that carries every fine contact of every family.
    pub required_coarse_aperture_squared: Rat,
    /// Where that maximum is attained.
    pub required_lineage: String,
}

impl GrainCensusTotals {
    /// Sum a family population. Refuses an empty population, because a total of nothing is not a
    /// measurement.
    pub fn over(families: &[GrainFamilyReturn]) -> Result<Self, IntakeRefusal> {
        let Some(first) = families.first() else {
            return Err(IntakeRefusal::EmptyFamilyPopulation);
        };
        let mut totals = Self {
            pairs: 0,
            fine_inside: 0,
            fine_open: 0,
            coarse_inside: 0,
            coarse_open: 0,
            fine_only_inside: 0,
            coarse_only_inside: 0,
            open_shared: 0,
            required_coarse_aperture_squared: first.inflation.coarse_aperture_squared.clone(),
            required_lineage: first.lineage.clone(),
        };
        for family in families {
            totals.pairs += family.census.pairs;
            totals.fine_inside += family.census.fine_inside;
            totals.fine_open += family.census.fine_open;
            totals.coarse_inside += family.census.coarse_inside;
            totals.coarse_open += family.census.coarse_open;
            totals.fine_only_inside += family.census.fine_only_inside;
            totals.coarse_only_inside += family.census.coarse_only_inside;
            totals.open_shared += family.census.open_shared;
            if family.inflation.coarse_aperture_squared > totals.required_coarse_aperture_squared {
                totals.required_coarse_aperture_squared =
                    family.inflation.coarse_aperture_squared.clone();
                totals.required_lineage = format!(
                    "{} at {:?}",
                    family.lineage, family.inflation.extremal.pair
                );
            }
        }
        Ok(totals)
    }
}

/// The scaled aperture of a declared contact radius in whole angstroms on a declared resident
/// denominator `10^places`.
pub fn contact_aperture(
    radius_angstroms: i128,
    resident_decimal_places: u32,
) -> Result<ScaledAperture, IntakeRefusal> {
    let denominator = 10_u64
        .checked_pow(resident_decimal_places)
        .ok_or(IntakeRefusal::ResidentDenominatorLeavesTheWire {
            places: resident_decimal_places,
        })?;
    let wire = i128::from(denominator);
    let aperture_squared_wire = radius_angstroms
        .checked_mul(radius_angstroms)
        .and_then(|square| square.checked_mul(wire))
        .and_then(|scaled| scaled.checked_mul(wire))
        .ok_or(IntakeRefusal::ResidentDenominatorLeavesTheWire {
            places: resident_decimal_places,
        })?;
    Ok(ScaledAperture {
        lineage: format!(
            "declared contact receiver: exact distance not greater than {radius_angstroms} \
             angstroms, on the resident denominator 10^{resident_decimal_places}"
        ),
        denominator,
        aperture_squared_wire,
    })
}

// ---------------------------------------------------------------------------------------------
// The one presented occurrence
// ---------------------------------------------------------------------------------------------

/// One addressed occurrence: a complete all-atom structure together with the uncertainty array and
/// the environment index that array was produced under.
///
/// [definition] An occurrence cannot be founded without its environment, because
/// [`AddressedUncertainty`] cannot be.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AddressedOccurrence {
    /// The schema this occurrence serializes under.
    pub schema: String,
    /// The complete all-atom presentation.
    pub structure: StructurePresentation,
    /// The uncertainty array with its environment index.
    pub uncertainty: AddressedUncertainty,
}

impl AddressedOccurrence {
    /// Found the occurrence from its two exterior charts.
    pub fn found(structure: StructurePresentation, uncertainty: AddressedUncertainty) -> Self {
        Self {
            schema: "holonic-engine.addressed-physical-occurrence.v1".to_owned(),
            structure,
            uncertainty,
        }
    }

    /// The environment index. Total.
    pub fn environment(&self) -> &EnvironmentIndex {
        self.uncertainty.environment()
    }

    /// Found the exact constraint complex of one declared cross family, with the directional
    /// uncertainty of every addressed pair supplied from this occurrence's own array.
    ///
    /// The two components become `ConstraintComponentId(1)` and `ConstraintComponentId(2)`.
    pub fn constraint_complex(
        &self,
        presentation_lineage: &str,
        source_event: EventId,
        left: &ChainOccurrence,
        right: &ChainOccurrence,
        presented: &ContactPresentation,
    ) -> Result<PhysicalConstraintComplex, IntakeRefusal> {
        let grain = &presented.grain;
        let resident_decimal_places = presented.resident_decimal_places;
        let left_material =
            component_material(left, presentation_lineage, grain, resident_decimal_places)?;
        let right_material =
            component_material(right, presentation_lineage, grain, resident_decimal_places)?;
        let left_tokens = component_vertex_tokens(left, grain)?;
        let right_tokens = component_vertex_tokens(right, grain)?;
        let uncertainty = self.uncertainty.pair_uncertainty(
            &left.label_asym_id,
            &left_tokens,
            &right.label_asym_id,
            &right_tokens,
        )?;
        found_constraint_complex(
            presentation_lineage,
            source_event,
            vec![left_material, right_material],
            vec![PresentedFamily {
                left: ConstraintComponentId(1),
                right: ConstraintComponentId(2),
                aperture: presented.aperture.clone(),
                uncertainty,
            }],
        )
    }
}

// ---------------------------------------------------------------------------------------------
// Refusals
// ---------------------------------------------------------------------------------------------

/// Why an intake refused. Every arm names what was wrong; no path in this module panics on input.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum IntakeRefusal {
    /// An exterior source could not be read at all.
    #[error("the source {origin} could not be read: {detail}")]
    SourceUnreadable {
        /// The source.
        origin: String,
        /// What the filesystem said.
        detail: String,
    },
    /// A ZIP container or one of its deflate streams is malformed.
    #[error("the archive {archive} is malformed: {detail}")]
    MalformedArchive {
        /// The container or member.
        archive: String,
        /// What failed.
        detail: String,
    },
    /// A member declares an uncompressed extent nothing has authenticated and its own payload
    /// cannot produce. The declaration is refused **before** it sizes anything.
    #[error(
        "the member {member} declares {declared} uncompressed octets over {compressed} compressed \
         octets, which exceeds the bound {bound}: {detail}"
    )]
    DeclaredExtentUnbounded {
        /// The member the declaration belongs to.
        member: String,
        /// The extent the container declares.
        declared: usize,
        /// How many compressed octets are actually present.
        compressed: usize,
        /// The largest extent that payload could lawfully produce.
        bound: usize,
        /// Which bound was exceeded and why.
        detail: String,
    },
    /// A declared shape or element width leaves the exact `usize` wire, so no extent it names can
    /// be checked against the payload that is present.
    #[error("the NumPy member {member} declares {detail}, which leaves the exact usize extent wire")]
    DeclaredExtentOverflows {
        /// The member.
        member: String,
        /// The declared product that overflowed.
        detail: String,
    },
    /// A `.npy` member is malformed.
    #[error("the NumPy member {member} is malformed: {detail}")]
    MalformedNumpyMember {
        /// The member.
        member: String,
        /// What failed.
        detail: String,
    },
    /// A float array is stored in a format this intake does not admit.
    #[error("the NumPy member {member} is {descr}, which is not one of the admitted {admitted}")]
    UnadmittedWordFormat {
        /// The member.
        member: String,
        /// The `descr` that was found.
        descr: String,
        /// What is admitted.
        admitted: String,
    },
    /// A named array is absent from a source.
    #[error("{origin} carries no {absent}; it carries {present:?}")]
    ArrayAbsent {
        /// The source.
        origin: String,
        /// The absent member.
        absent: String,
        /// What the source does carry.
        present: Vec<String>,
    },
    /// The environment and lineage arrays are absent, so no occurrence can be founded from this
    /// source alone.
    #[error(
        "{origin} carries no environment index: {absent:?} are absent. An external predictor \
         emits only the uncertainty array, so the environment this array was produced under must \
         be declared. The source carries {present:?}"
    )]
    EnvironmentArraysAbsent {
        /// The source.
        origin: String,
        /// Every absent array, named.
        absent: Vec<String>,
        /// What the source does carry.
        present: Vec<String>,
    },
    /// A declared environment index carried no declaration or no token population.
    #[error("a declared environment index needs both a stated ground and a token population")]
    EnvironmentDeclarationEmpty,
    /// The three token faces of a self-indexed source have different lengths.
    #[error(
        "{origin} presents {chains} chain, {residues} residue and {entities} entity token faces"
    )]
    TokenFacesDisagree {
        /// The source.
        origin: String,
        /// How many chain labels.
        chains: usize,
        /// How many residue ordinals.
        residues: usize,
        /// How many entity labels.
        entities: usize,
    },
    /// The uncertainty array is not square.
    #[error("{origin} presents an uncertainty array of shape {shape:?}, which is not square")]
    UncertaintyNotSquare {
        /// The source.
        origin: String,
        /// The presented shape.
        shape: Vec<usize>,
    },
    /// The payload does not carry `extent²` words.
    #[error("{origin} declares extent {extent} but carries {words} words")]
    UncertaintyExtentDisagrees {
        /// The source.
        origin: String,
        /// The declared extent.
        extent: usize,
        /// How many words were found.
        words: usize,
    },
    /// A cell outside the array was addressed.
    #[error("{origin} has extent {extent}; cell ({row},{column}) is outside it")]
    UncertaintyCellOutOfRange {
        /// The source.
        origin: String,
        /// The extent.
        extent: usize,
        /// The addressed row.
        row: usize,
        /// The addressed column.
        column: usize,
    },
    /// A stored word is infinite or not a number, so it decodes to no exact dyadic.
    #[error(
        "the {format} word at index {index} is {bits:#x}, which is not finite and decodes to no \
         exact dyadic: {detail}"
    )]
    NonFiniteUncertaintyWord {
        /// The format the word was read under.
        format: String,
        /// Where in the array it sits.
        index: usize,
        /// The exterior codeword.
        bits: u64,
        /// What the exact decoder said.
        detail: String,
    },
    /// The token population does not address the array.
    #[error("the environment names {tokens} tokens for an array of extent {extent} in {origin}")]
    TokenPopulationDisagrees {
        /// The source.
        origin: String,
        /// The array extent.
        extent: usize,
        /// How many tokens the environment names.
        tokens: usize,
    },
    /// Two tokens carry the same address, so the array's addressing is ambiguous.
    #[error("the environment of {origin} addresses one chain and residue twice")]
    TokenAddressRepeated {
        /// The source.
        origin: String,
    },
    /// An addressed token is absent from the environment.
    #[error("the uncertainty array carries no token {chain}:{residue}")]
    TokenAbsent {
        /// The addressed chain.
        chain: String,
        /// The addressed residue.
        residue: i32,
    },
    /// An mmCIF occurrence is malformed.
    #[error("the structure {origin} is malformed: {detail}")]
    MalformedStructure {
        /// The source.
        origin: String,
        /// What failed.
        detail: String,
    },
    /// A required `_atom_site` column is absent.
    #[error("the structure {origin} has no {column} column")]
    StructureColumnAbsent {
        /// The source.
        origin: String,
        /// The absent column.
        column: String,
    },
    /// A coordinate token is not a plain decimal.
    #[error("the coordinate token {token:?} is not a plain decimal")]
    CoordinateNotAPlainDecimal {
        /// The token.
        token: String,
    },
    /// A coordinate leaves the exact integer wire.
    #[error("the coordinate token {token:?} leaves the exact wire: {detail}")]
    CoordinateLeavesTheExactWire {
        /// The token.
        token: String,
        /// Which step overflowed.
        detail: String,
    },
    /// The resident denominator leaves the exact wire.
    #[error("a resident denominator of 10^{places} leaves the exact wire")]
    ResidentDenominatorLeavesTheWire {
        /// The declared decimal place count.
        places: u32,
    },
    /// An addressed chain is absent.
    #[error("{origin} carries no chain {label}; it carries {present:?}")]
    ChainAbsent {
        /// The source.
        origin: String,
        /// The addressed label.
        label: String,
        /// What the source does carry.
        present: Vec<String>,
    },
    /// A chain addressed by its residue count is not uniquely addressed.
    #[error("{origin} carries {matching} chains of {residues} residues, so the address is not one")]
    ChainCountAmbiguous {
        /// The source.
        origin: String,
        /// The addressed residue count.
        residues: usize,
        /// How many chains carry it.
        matching: usize,
    },
    /// A residue carries no atom with the declared representative label.
    #[error("chain {chain} residue {residue} carries no {label} atom, so it has no representative")]
    RepresentativeAtomAbsent {
        /// The chain.
        chain: String,
        /// The residue's source ordinal.
        residue: i32,
        /// The declared label.
        label: String,
    },
    /// A residue carries several atoms with the declared representative label.
    #[error("residue {residue} carries {occurrences} atoms labelled {label}; a representative is one")]
    RepeatedRepresentativeAtom {
        /// The residue's source ordinal.
        residue: i32,
        /// The declared label.
        label: String,
        /// How many atoms carry it.
        occurrences: usize,
    },
    /// A census was asked of no families.
    #[error("a census over an empty family population is not a measurement")]
    EmptyFamilyPopulation,
    /// The exact constraint complex refused.
    #[error("the constraint complex refused: {0}")]
    Constraint(#[from] ConstraintError),
    /// The apertured graded complex refused.
    #[error("the graded constraint complex refused: {0}")]
    Grading(#[from] ConstraintGradingError),
    /// The grain tower refused.
    #[error("the grain tower refused: {0}")]
    Grain(#[from] GrainRefusal),
}

#[cfg(test)]
#[path = "physical_intake/tests.rs"]
mod tests;
