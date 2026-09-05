//! Exterior acquisition and standard tensor storage of additional native input sections.
//! This extends material, not Soulkiller's witnessed signature family. Source paths/names stay
//! in this application; the resident intake receives only native ordinals and integer codewords.

use crate::{publish_new, HnaBaseDependency, HnaInputMaterialDependency, HnaSessionError};
use holonic_engine::{
    foreign_map::{manifest_safetensors, manifest_safetensors_file, ForeignDtype},
    native_ecology::holonic_intelligence::{
        dismantle_full_native_operator, NativeConeRestrictedEcology, NativeInputExtendedIntake,
        NativeInputRowExtension,
    },
};
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::{
    collections::{BTreeMap, BTreeSet},
    io::Write,
    path::Path,
};

const SCHEMA: &str = "org.holonics.hna.input-material.v1";
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Section {
    population: u32,
    rows: usize,
    dim: usize,
}

#[derive(Debug, Serialize)]
pub struct HnaInputAcquisitionReceipt {
    pub schema: String,
    pub material: HnaInputMaterialDependency,
    pub source_container: String,
    pub added_rows: BTreeMap<u32, usize>,
    pub added_codewords: usize,
}

fn error(value: impl std::fmt::Display) -> HnaSessionError {
    HnaSessionError::Base(format!("input material: {value}"))
}

pub(crate) fn acquire(
    base: &NativeConeRestrictedEcology,
    dependency: &HnaBaseDependency,
    held: &[NativeInputRowExtension],
    source_root: &Path,
    addresses: &[u32],
    output: &Path,
) -> Result<HnaInputAcquisitionReceipt, HnaSessionError> {
    if addresses.is_empty() {
        return Err(error("empty requested material"));
    }
    let intake =
        NativeInputExtendedIntake::new(base.intake(dependency.class).map_err(error)?, held)
            .map_err(error)?;
    let missing = intake.missing_input_rows(addresses);
    if missing.is_empty() {
        return Err(error("all requested input sections are already present"));
    }
    let source = dismantle_full_native_operator(source_root).map_err(error)?;
    if source.native != base.ecology {
        return Err(error("source operator chart differs from the target chart"));
    }
    // This equality aligns the source chart only. It does not identify all source coefficients,
    // enlarge the old signature family, or make source inference the native emitter.
    let (mut file, container) =
        manifest_safetensors(&source.exterior.source_container).map_err(error)?;
    let mut additions = Vec::new();
    for (population, addresses) in missing {
        let target = &base.cross_sections[population as usize];
        let cold = source
            .exterior
            .populations
            .get(population as usize)
            .ok_or_else(|| error("source population"))?;
        if cold.ordinal.0 != population {
            return Err(error("source ordinal"));
        }
        let mut words = Vec::new();
        for row in &addresses {
            let (returned, dim) = container
                .read_rows_bf16(&mut file, &cold.source_name, *row as usize, 1)
                .map_err(error)?;
            if dim != target.dim {
                return Err(error("source input width"));
            }
            words.extend(returned);
        }
        additions.push(NativeInputRowExtension {
            population,
            rows: target.rows,
            dim: target.dim,
            addresses,
            words,
        });
    }
    // The native constructor refuses replacement, overlap and a population with any non-lookup
    // use. Validate the complete composition before publishing any file.
    let combined = merge(
        held.iter()
            .cloned()
            .chain(additions.iter().cloned())
            .collect(),
    )?;
    NativeInputExtendedIntake::new(base.intake(dependency.class).map_err(error)?, &combined)
        .map_err(error)?;
    write_material(output, dependency, &additions)?;
    Ok(HnaInputAcquisitionReceipt {
        schema: "org.holonics.hna.input-acquisition.v1".into(),
        material: HnaInputMaterialDependency::capture(output)?,
        source_container: source.exterior.source_container,
        added_rows: additions
            .iter()
            .map(|section| (section.population, section.addresses.len()))
            .collect(),
        added_codewords: additions.iter().map(|section| section.words.len()).sum(),
    })
}

/// The artifact is ordinary Safetensors: U32 addresses and BF16 sections, with an explicit
/// target-base wire pin. It is input material, not a standard executable model export.
fn write_material(
    path: &Path,
    base: &HnaBaseDependency,
    sections: &[NativeInputRowExtension],
) -> Result<(), HnaSessionError> {
    let mut entries = serde_json::Map::new();
    let specs: Vec<_> = sections
        .iter()
        .map(|s| Section {
            population: s.population,
            rows: s.rows,
            dim: s.dim,
        })
        .collect();
    entries.insert(
        "__metadata__".into(),
        json!({"schema":SCHEMA,"target_base_octets":base.octets.to_string(),
        "target_base_sha256":base.sha256,"sections":serde_json::to_string(&specs).map_err(error)?}),
    );
    let mut offset = 0usize;
    for section in sections {
        let addresses = section
            .addresses
            .len()
            .checked_mul(4)
            .ok_or_else(|| error("address extent"))?;
        let words = section
            .words
            .len()
            .checked_mul(2)
            .ok_or_else(|| error("codeword extent"))?;
        let address_end = offset
            .checked_add(addresses)
            .ok_or_else(|| error("payload extent"))?;
        let end = address_end
            .checked_add(words)
            .ok_or_else(|| error("payload extent"))?;
        entries.insert(
            format!("input/{}/addresses", section.population),
            json!({"dtype":"U32",
            "shape":[section.addresses.len()],"data_offsets":[offset,address_end]}),
        );
        entries.insert(
            format!("input/{}/words", section.population),
            json!({"dtype":"BF16",
            "shape":[section.addresses.len(),section.dim],"data_offsets":[address_end,end]}),
        );
        offset = end;
    }
    let mut header = serde_json::to_vec(&entries).map_err(error)?;
    header.resize(header.len().next_multiple_of(8), b' ');
    publish_new(path, |out| {
        out.write_all(&(header.len() as u64).to_le_bytes())?;
        out.write_all(&header)?;
        let mut buffered = std::io::BufWriter::new(out);
        for section in sections {
            for row in &section.addresses {
                buffered.write_all(&row.to_le_bytes())?;
            }
            for word in &section.words {
                buffered.write_all(&word.to_le_bytes())?;
            }
        }
        buffered.flush()
    })
    .map_err(error)?;
    Ok(())
}

pub(crate) fn load(
    base: &HnaBaseDependency,
) -> Result<Vec<NativeInputRowExtension>, HnaSessionError> {
    let mut sections = Vec::new();
    for pin in &base.input_material {
        let (mut file, container) =
            manifest_safetensors_file(pin.open_verified()?, &pin.path.display().to_string())
                .map_err(error)?;
        let metadata = &container.container_metadata;
        if metadata.get("schema").map(String::as_str) != Some(SCHEMA)
            || metadata.get("target_base_octets") != Some(&base.octets.to_string())
            || metadata.get("target_base_sha256") != Some(&base.sha256)
            || !container.refused.is_empty()
        {
            return Err(error("schema, target base, or refused tensor"));
        }
        let specs: Vec<Section> = serde_json::from_str(
            metadata
                .get("sections")
                .ok_or_else(|| error("section declarations"))?,
        )
        .map_err(error)?;
        let mut claimed = BTreeSet::new();
        for spec in specs {
            let address_name = format!("input/{}/addresses", spec.population);
            let word_name = format!("input/{}/words", spec.population);
            if !claimed.insert(address_name.clone()) || !claimed.insert(word_name.clone()) {
                return Err(error("repeated section"));
            }
            let address_tensor = container
                .tensors
                .get(&address_name)
                .ok_or_else(|| error("address tensor"))?;
            let word_tensor = container
                .tensors
                .get(&word_name)
                .ok_or_else(|| error("section tensor"))?;
            if address_tensor.dtype != ForeignDtype::U32
                || address_tensor.shape.len() != 1
                || word_tensor.dtype != ForeignDtype::Bf16
                || word_tensor.shape != [address_tensor.shape[0], spec.dim]
            {
                return Err(error("input tensor shape/dtype"));
            }
            let raw = container
                .read_elements(&mut file, &address_name, 0, address_tensor.shape[0] as u64)
                .map_err(error)?;
            let addresses = raw
                .chunks_exact(4)
                .map(|chunk| u32::from_le_bytes(chunk.try_into().expect("four bytes")))
                .collect();
            let words = container
                .read_bf16_whole(&mut file, &word_name)
                .map_err(error)?;
            sections.push(NativeInputRowExtension {
                population: spec.population,
                rows: spec.rows,
                dim: spec.dim,
                addresses,
                words,
            });
        }
        if claimed.len() != container.tensors.len() {
            return Err(error("unclaimed input tensor"));
        }
    }
    merge(sections)
}

fn merge(
    sections: Vec<NativeInputRowExtension>,
) -> Result<Vec<NativeInputRowExtension>, HnaSessionError> {
    let mut grouped: BTreeMap<u32, (usize, usize, BTreeMap<u32, Vec<u16>>)> = BTreeMap::new();
    for section in sections {
        if section.dim == 0
            || section.rows == 0
            || section.addresses.is_empty()
            || section.addresses.len().checked_mul(section.dim) != Some(section.words.len())
            || section.addresses.windows(2).any(|pair| pair[0] >= pair[1])
        {
            return Err(error("malformed section extent or order"));
        }
        let entry = grouped
            .entry(section.population)
            .or_insert_with(|| (section.rows, section.dim, BTreeMap::new()));
        if (entry.0, entry.1) != (section.rows, section.dim) {
            return Err(error("conflicting population extents"));
        }
        for (row, words) in section
            .addresses
            .into_iter()
            .zip(section.words.chunks_exact(section.dim))
        {
            if row as usize >= section.rows || entry.2.insert(row, words.to_vec()).is_some() {
                return Err(error("overlapping or outside input row"));
            }
        }
    }
    Ok(grouped
        .into_iter()
        .map(|(population, (rows, dim, sections))| {
            let addresses = sections.keys().copied().collect();
            let words = sections.into_values().flatten().collect();
            NativeInputRowExtension {
                population,
                rows,
                dim,
                addresses,
                words,
            }
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn standard_input_material_roundtrips_and_rejects_wrong_base_and_overlap() {
        let dir = tempfile::tempdir().unwrap();
        let base_file = dir.path().join("base");
        std::fs::write(&base_file, b"immutable base").unwrap();
        let mut base = HnaBaseDependency::capture(&base_file, None).unwrap();
        let section = NativeInputRowExtension {
            population: 7,
            rows: 5,
            dim: 2,
            addresses: vec![1, 3],
            words: vec![0x3f80, 0x4000, 0x4040, 0x4080],
        };
        let path = dir.path().join("input.safetensors");
        write_material(&path, &base, std::slice::from_ref(&section)).unwrap();
        base.input_material
            .push(HnaInputMaterialDependency::capture(&path).unwrap());
        assert_eq!(load(&base).unwrap(), vec![section.clone()]);
        let valid_pin = base.input_material[0].clone();
        base.input_material[0].path = dir.path().join("missing.safetensors");
        assert!(load(&base).is_err());
        base.input_material[0] = valid_pin.clone();
        base.input_material[0].sha256 = "stale-wire".into();
        assert!(load(&base).is_err());
        base.input_material[0] = valid_pin;
        base.input_material.push(base.input_material[0].clone());
        assert!(load(&base).is_err());
        base.input_material.pop();
        base.sha256 = "not-the-base".into();
        assert!(load(&base).is_err());
        assert!(merge(vec![section.clone(), section]).is_err());
    }
}
