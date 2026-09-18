//! The admitted Protenix PAE occurrence, read **through the library intake**.
//!
//! [definition] Every `.npy` header, every stored codeword and every directional reading in this
//! deed is `holonic_engine::physical_intake::numpy`'s. This file used to carry its own copy of
//! `NpyArray::{elements, binary16, i32_le, unicode}` — including the same unguarded
//! `shape.iter().product()` the library has since had to repair — and the copy is gone. What
//! remains is the M5 receipt: which members were extracted, with what digest, and the declared
//! environment the atlas binds against.

use std::collections::BTreeMap;
use std::path::Path;

use holonic_engine::physical_constraint_complex::PairUncertainty;
use holonic_engine::physical_intake::numpy::{NumpySource, UncertaintyWordFormat};
use holonic_engine::physical_intake::{
    AddressedUncertainty, ENVIRONMENT_ARRAYS, EnvironmentIndex, UncertaintyArray,
};
use serde::Serialize;

use super::input::digest_path;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NpyMember {
    pub name: String,
    pub local_path: String,
    pub sha256: String,
    pub descr: String,
    pub shape: Vec<usize>,
    pub octets: u64,
}

#[derive(Debug, Serialize)]
pub struct PaeAtlas {
    pub schema: String,
    pub source_npz_release_path: String,
    pub source_npz_sha256: String,
    pub extracted_members: Vec<NpyMember>,
    pub design_uuid: String,
    pub design_name: String,
    pub target: String,
    pub cofolding_model: String,
    pub stoichiometry: String,
    pub target_form: String,
    pub seed: String,
    pub matrix_shape: [usize; 2],
    pub finite_binary16_words: usize,
    pub refused_nonfinite_words: usize,
    pub token_population: usize,
    pub uncertainty_law: String,
    #[serde(skip)]
    occurrence: AddressedUncertainty,
}

impl PaeAtlas {
    /// The directional uncertainty of every pair of one declared cross population, straight from
    /// `AddressedUncertainty::pair_uncertainty`: the token addressing, the distinct-address check
    /// and the exact decoding of both directions are the library's.
    pub fn pair_uncertainty(
        &self,
        left_chain: &str,
        left_residues: &[i32],
        right_chain: &str,
        right_residues: &[i32],
    ) -> Result<BTreeMap<(u32, u32), PairUncertainty>, String> {
        self.occurrence
            .pair_uncertainty(left_chain, left_residues, right_chain, right_residues)
            .map_err(|error| error.to_string())
    }
}

pub fn read(
    directory: &Path,
    source_npz_release_path: &str,
    source_npz_sha256: &str,
) -> Result<PaeAtlas, String> {
    let source = NumpySource::read_directory(directory).map_err(|error| error.to_string())?;
    let mut extracted_members = Vec::new();
    for name in ENVIRONMENT_ARRAYS {
        let member = source.member(name).map_err(|error| error.to_string())?;
        let path = directory.join(name);
        extracted_members.push(NpyMember {
            name: name.to_owned(),
            local_path: path.display().to_string(),
            sha256: digest_path(&path)?,
            descr: member.descr.clone(),
            shape: member.shape.clone(),
            octets: std::fs::metadata(&path)
                .map_err(|error| error.to_string())?
                .len(),
        });
    }

    let environment =
        EnvironmentIndex::from_numpy_source(&source).map_err(|error| error.to_string())?;
    let array = UncertaintyArray::from_numpy_source(&source).map_err(|error| error.to_string())?;
    // The M5 release stores `<f2`; the library admits `<f4` and `<f8` as well, so the deed states
    // the wire it was measured on rather than inheriting whatever the source happens to carry.
    if array.format != UncertaintyWordFormat::Binary16 {
        return Err(format!(
            "the admitted M5 PAE wire is <f2; {} carries {}",
            directory.display(),
            array.format.descr()
        ));
    }
    let extent = array.extent;
    // Every word decoded to a finite exact dyadic, because `UncertaintyArray::found` refuses the
    // first word that does not and this read succeeded. The refused count is therefore zero by
    // construction rather than by a second scan.
    let finite_binary16_words = array.finite_words;
    let occurrence =
        AddressedUncertainty::found(environment, array).map_err(|error| error.to_string())?;
    let ecology = &occurrence.environment().ecology;
    let lineage = &occurrence.environment().lineage;
    Ok(PaeAtlas {
        schema: "holonics.m5.exact-binary16-pae-atlas.v1".to_owned(),
        source_npz_release_path: source_npz_release_path.to_owned(),
        source_npz_sha256: source_npz_sha256.to_owned(),
        extracted_members,
        design_uuid: lineage.design_uuid.clone(),
        design_name: lineage.design_name.clone(),
        target: ecology.target.clone(),
        cofolding_model: ecology.cofolding_model.clone(),
        stoichiometry: ecology.stoichiometry.clone(),
        target_form: ecology.target_form.clone(),
        seed: lineage.seed.clone(),
        matrix_shape: [extent, extent],
        finite_binary16_words,
        refused_nonfinite_words: 0,
        token_population: occurrence.environment().tokens.len(),
        uncertainty_law: occurrence.array().reading_law.clone(),
        occurrence,
    })
}
