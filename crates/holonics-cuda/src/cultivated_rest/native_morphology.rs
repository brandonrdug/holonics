use std::collections::BTreeSet;
use std::path::Path;

use serde::{Deserialize, Serialize};

use super::schema::*;
use super::{canonical_laws_digest, digest, factor_values_bytes, valid_digest};
use crate::native_occurrence::NativeOccurrence;
use crate::source_occurrence::RegionIdentity;

/// Path-free testimony borrowed from the existing [`NativeOccurrence`] witness.  Only the
/// authenticated native morphology header crosses this product seam; its locator and payload do
/// not.  This is an identity/receipt, not a second native-rest implementation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeMorphologyWitness {
    pub content_sha256: String,
    pub extent: u64,
    pub header_sha256: String,
    pub regions: Vec<RegionIdentity>,
    pub declarations: Vec<(String, String)>,
    pub left_population: String,
    pub right_population: String,
    pub left_sha256: String,
    pub right_sha256: String,
    pub left_shape: Vec<usize>,
    pub right_shape: Vec<usize>,
    pub left_exponent: i32,
    pub right_exponent: i32,
    pub rank: u32,
    pub resident_grain: u32,
    pub predecessor_sha256: String,
    pub constitutive_sha256: String,
}

impl NativeMorphologyWitness {
    pub fn from_occurrence(occurrence: &NativeOccurrence) -> Result<Self, CultivatedRestRefusal> {
        let content_sha256 = occurrence.container.content_sha256.clone().ok_or_else(|| {
            CultivatedRestRefusal::InvalidIdentity("native morphology content".to_owned())
        })?;
        let mut regions: Vec<_> = occurrence.container.regions.values().cloned().collect();
        regions.sort_by(|left, right| left.population.cmp(&right.population));
        let mut declarations: Vec<_> = occurrence
            .declarations
            .iter()
            .map(|(key, value)| (key.clone(), value.clone()))
            .collect();
        declarations.sort();
        Ok(Self {
            content_sha256,
            extent: occurrence.container.octets,
            header_sha256: occurrence.container.header_sha256.clone(),
            regions,
            declarations,
            left_population: String::new(),
            right_population: String::new(),
            left_sha256: String::new(),
            right_sha256: String::new(),
            left_shape: Vec::new(),
            right_shape: Vec::new(),
            left_exponent: 0,
            right_exponent: 0,
            rank: 0,
            resident_grain: 0,
            predecessor_sha256: String::new(),
            constitutive_sha256: String::new(),
        })
    }

    pub(crate) fn validate(&self) -> Result<(), CultivatedRestRefusal> {
        if !valid_digest(&self.content_sha256)
            || !valid_digest(&self.header_sha256)
            || !valid_digest(&self.left_sha256)
            || !valid_digest(&self.right_sha256)
            || !valid_digest(&self.predecessor_sha256)
            || !valid_digest(&self.constitutive_sha256)
            || self.extent == 0
            || self.regions.is_empty()
            || self.declarations.is_empty()
            || self.left_population.is_empty()
            || self.right_population.is_empty()
            || self.rank == 0
            || self.resident_grain == 0
        {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "native morphology witness".to_owned(),
            ));
        }
        let mut names = BTreeSet::new();
        for region in &self.regions {
            if region.population.is_empty()
                || region.dtype != "I64"
                || region.end < region.start
                || region.sha256.is_none()
                || !names.insert(region.population.as_str())
            {
                return Err(CultivatedRestRefusal::InvalidIdentity(
                    "native morphology region".to_owned(),
                ));
            }
        }
        if self.left_shape.len() != 2 || self.right_shape.len() != 2 {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "native morphology factor shape".to_owned(),
            ));
        }
        let left = self
            .regions
            .iter()
            .find(|region| region.population == self.left_population)
            .ok_or_else(|| {
                CultivatedRestRefusal::InvalidIdentity("native morphology left region".to_owned())
            })?;
        let right = self
            .regions
            .iter()
            .find(|region| region.population == self.right_population)
            .ok_or_else(|| {
                CultivatedRestRefusal::InvalidIdentity("native morphology right region".to_owned())
            })?;
        if left.sha256.as_deref() != Some(self.left_sha256.as_str())
            || right.sha256.as_deref() != Some(self.right_sha256.as_str())
            || left.shape != self.left_shape
            || right.shape != self.right_shape
            || left.shape != vec![self.left_shape[0], self.rank as usize]
            || right.shape != vec![self.rank as usize, self.right_shape[1]]
        {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "native morphology factor binding".to_owned(),
            ));
        }
        let declarations: std::collections::BTreeMap<_, _> =
            self.declarations.iter().cloned().collect();
        for (key, expected) in [
            (
                "phoenix.morphology.left-exponent",
                self.left_exponent.to_string(),
            ),
            (
                "phoenix.morphology.right-exponent",
                self.right_exponent.to_string(),
            ),
            ("phoenix.morphology.rank", self.rank.to_string()),
            (
                "phoenix.morphology.resident-grain",
                self.resident_grain.to_string(),
            ),
            (
                "phoenix.morphology.predecessor",
                self.predecessor_sha256.clone(),
            ),
            (
                "phoenix.morphology.constitutive",
                self.constitutive_sha256.clone(),
            ),
        ] {
            if declarations.get(key).map(String::as_str) != Some(expected.as_str()) {
                return Err(CultivatedRestRefusal::InvalidIdentity(format!(
                    "native morphology declaration {key}"
                )));
            }
        }
        if self
            .declarations
            .windows(2)
            .any(|pair| pair[0].0 >= pair[1].0)
            || self
                .declarations
                .iter()
                .any(|(key, value)| key.is_empty() || value.is_empty())
        {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "native morphology declarations".to_owned(),
            ));
        }
        Ok(())
    }
}

/// Input to the small native morphology safetensors seam. The two populations are the raw I64
/// factor regions; the product rest later binds their separate digests and shapes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeMorphologyInput {
    pub left_population: String,
    pub right_population: String,
    pub left_shape: Vec<usize>,
    pub right_shape: Vec<usize>,
    pub left_exponent: i32,
    pub right_exponent: i32,
    pub rank: u32,
    pub resident_grain: u32,
    pub predecessor: PredecessorProductIdentity,
    pub laws: Vec<TypedLaw>,
    pub left: Vec<i64>,
    pub right: Vec<i64>,
}

impl NativeMorphologyInput {
    fn validate(&self) -> Result<(), CultivatedRestRefusal> {
        self.predecessor.validate()?;
        let expected_left = self
            .left_shape
            .first()
            .and_then(|rows| rows.checked_mul(self.rank as usize));
        let expected_right = self
            .right_shape
            .get(1)
            .and_then(|columns| columns.checked_mul(self.rank as usize));
        if self.left_population.is_empty()
            || self.right_population.is_empty()
            || self.left_population == self.right_population
            || self.left_population == "__metadata__"
            || self.right_population == "__metadata__"
            || self.left_population.starts_with("phoenix.morphology.")
            || self.right_population.starts_with("phoenix.morphology.")
            || self.left_shape.len() != 2
            || self.right_shape.len() != 2
            || self.rank == 0
            || self.resident_grain == 0
            || self.left_shape != vec![self.left_shape[0], self.rank as usize]
            || self.right_shape != vec![self.rank as usize, self.right_shape[1]]
            || expected_left != Some(self.left.len())
            || expected_right != Some(self.right.len())
        {
            return Err(CultivatedRestRefusal::PayloadShape);
        }
        let mut port_names = BTreeSet::new();
        let mut ports = Vec::new();
        for name in self
            .laws
            .iter()
            .flat_map(|law| law.inputs.iter().chain(law.outputs.iter()))
        {
            if port_names.insert(name.as_str()) {
                ports.push(TypedPort {
                    name: name.clone(),
                    direction: PortDirection::Input,
                    carrier: "native-i64".to_owned(),
                    rows: ExtentOrigin::Runtime,
                    width: 1,
                    octave_bound: OctaveBoundOrigin::RuntimeDerived,
                });
            }
        }
        let mut laws = self.laws.clone();
        super::wire::validate_ports_laws(&mut ports, &mut laws)?;
        if self.laws.iter().any(|law| {
            law.name.is_empty()
                || law.name == "__metadata__"
                || law.name.starts_with("phoenix.morphology.")
        }) {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "native morphology law metadata key".to_owned(),
            ));
        }
        Ok(())
    }

    fn metadata(&self) -> Result<Vec<(String, String)>, CultivatedRestRefusal> {
        self.validate()?;
        let mut metadata = vec![
            (
                "phoenix.morphology.constitutive".to_owned(),
                canonical_laws_digest(&self.laws),
            ),
            (
                "phoenix.morphology.left-exponent".to_owned(),
                self.left_exponent.to_string(),
            ),
            (
                "phoenix.morphology.right-exponent".to_owned(),
                self.right_exponent.to_string(),
            ),
            (
                "phoenix.morphology.predecessor".to_owned(),
                self.predecessor.sha256.clone(),
            ),
            ("phoenix.morphology.rank".to_owned(), self.rank.to_string()),
            (
                "phoenix.morphology.resident-grain".to_owned(),
                self.resident_grain.to_string(),
            ),
            (
                "phoenix.morphology.left-population".to_owned(),
                self.left_population.clone(),
            ),
            (
                "phoenix.morphology.right-population".to_owned(),
                self.right_population.clone(),
            ),
        ];
        for (index, law) in self.laws.iter().enumerate() {
            let prefix = format!("phoenix.morphology.law.{index:04}");
            metadata.push((format!("{prefix}.name"), law.name.clone()));
            metadata.push((
                format!("{prefix}.inputs"),
                serde_json::to_string(&law.inputs)
                    .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?,
            ));
            metadata.push((
                format!("{prefix}.outputs"),
                serde_json::to_string(&law.outputs)
                    .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?,
            ));
            metadata.push((
                format!("{prefix}.constitutive"),
                law.constitutive_digest.clone(),
            ));
        }
        let mut keys = BTreeSet::new();
        if metadata
            .iter()
            .any(|(key, value)| key.is_empty() || value.is_empty() || !keys.insert(key.as_str()))
        {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "duplicate native morphology metadata key".to_owned(),
            ));
        }
        Ok(metadata)
    }
}

/// Emit the authenticated two-region I64 native morphology occurrence consumed by
/// [`NativeOccurrence::read`]. No floating-point carrier or source locator enters the payload.
pub fn write_native_morphology(
    path: impl AsRef<Path>,
    input: &NativeMorphologyInput,
) -> Result<(), CultivatedRestRefusal> {
    let bytes = native_morphology_bytes(input)?;
    std::fs::write(path, bytes)
        .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))
}

pub fn native_morphology_bytes(
    input: &NativeMorphologyInput,
) -> Result<Vec<u8>, CultivatedRestRefusal> {
    let metadata = input.metadata()?;
    let left_end = input
        .left
        .len()
        .checked_mul(8)
        .ok_or(CultivatedRestRefusal::PayloadShape)?;
    let right_end = left_end
        .checked_add(
            input
                .right
                .len()
                .checked_mul(8)
                .ok_or(CultivatedRestRefusal::PayloadShape)?,
        )
        .ok_or(CultivatedRestRefusal::PayloadShape)?;
    let mut json = String::from("{\"__metadata__\":{");
    for (index, (key, value)) in metadata.iter().enumerate() {
        if index > 0 {
            json.push(',');
        }
        json.push_str(
            &serde_json::to_string(key)
                .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?,
        );
        json.push(':');
        json.push_str(
            &serde_json::to_string(value)
                .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?,
        );
    }
    json.push_str("},");
    json.push_str(
        &serde_json::to_string(&input.left_population)
            .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?,
    );
    json.push_str(&format!(
        ":{{\"dtype\":\"I64\",\"shape\":[{},{}],\"data_offsets\":[0,{}]}},",
        input.left_shape[0], input.left_shape[1], left_end
    ));
    json.push_str(
        &serde_json::to_string(&input.right_population)
            .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?,
    );
    json.push_str(&format!(
        ":{{\"dtype\":\"I64\",\"shape\":[{},{}],\"data_offsets\":[{},{}]}}}}",
        input.right_shape[0], input.right_shape[1], left_end, right_end
    ));
    let mut header = json.into_bytes();
    while header.len() % 8 != 0 {
        header.push(b' ');
    }
    let mut bytes = Vec::with_capacity(8 + header.len() + right_end);
    bytes.extend_from_slice(&(header.len() as u64).to_le_bytes());
    bytes.extend_from_slice(&header);
    bytes.extend_from_slice(&factor_values_bytes(&input.left));
    bytes.extend_from_slice(&factor_values_bytes(&input.right));
    Ok(bytes)
}

pub(crate) fn hydrate_region_digests(
    occurrence: &NativeOccurrence,
    witness: &mut NativeMorphologyWitness,
) -> Result<(), CultivatedRestRefusal> {
    use std::io::{Seek, SeekFrom};
    let mut file = std::fs::File::open(&occurrence.container.locator)
        .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?;
    let base = 8u64.saturating_add(occurrence.container.header_octets);
    for region in &mut witness.regions {
        file.seek(SeekFrom::Start(base.saturating_add(region.start)))
            .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?;
        let mut bytes = vec![
            0u8;
            usize::try_from(region.end.saturating_sub(region.start))
                .map_err(|_| CultivatedRestRefusal::PayloadShape)?
        ];
        std::io::Read::read_exact(&mut file, &mut bytes)
            .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?;
        region.sha256 = Some(digest(&bytes));
    }
    Ok(())
}
