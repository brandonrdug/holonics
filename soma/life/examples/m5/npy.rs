//! Exact NumPy faces for the admitted Protenix PAE occurrence.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use holonic_engine::exact_value::ExactInterval;
use holonic_engine::exact_value::ieee754::{FloatReading, decode_binary16_bits};
use holonic_engine::physical_constraint_complex::PairUncertainty;
use serde::Serialize;

use super::input::digest_path;

const REQUIRED: &[&str] = &[
    "pae.npy",
    "token_chain_ids.npy",
    "token_res_ids.npy",
    "design_uuid.npy",
    "design_name.npy",
    "target.npy",
    "cofolding_model.npy",
    "stoichiometry.npy",
    "target_form.npy",
    "seed.npy",
];

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
    words: Vec<u16>,
    #[serde(skip)]
    token_chain_ids: Vec<String>,
    #[serde(skip)]
    token_res_ids: Vec<i32>,
}

impl PaeAtlas {
    pub fn pair_uncertainty(
        &self,
        left_chain: &str,
        left_residues: &[i32],
        right_chain: &str,
        right_residues: &[i32],
    ) -> Result<BTreeMap<(u32, u32), PairUncertainty>, String> {
        let mut token = BTreeMap::<(String, i32), usize>::new();
        for (at, (chain, residue)) in self
            .token_chain_ids
            .iter()
            .zip(&self.token_res_ids)
            .enumerate()
        {
            if token.insert((chain.clone(), *residue), at).is_some() {
                return Err(format!(
                    "PAE token address {chain}:{residue} occurs more than once"
                ));
            }
        }
        let width = self.matrix_shape[1];
        let mut result = BTreeMap::new();
        for (left_at, left_residue) in left_residues.iter().enumerate() {
            let left_token = *token
                .get(&(left_chain.to_owned(), *left_residue))
                .ok_or_else(|| format!("PAE has no token {left_chain}:{left_residue}"))?;
            for (right_at, right_residue) in right_residues.iter().enumerate() {
                let right_token = *token
                    .get(&(right_chain.to_owned(), *right_residue))
                    .ok_or_else(|| format!("PAE has no token {right_chain}:{right_residue}"))?;
                let row_word = self.words[left_token * width + right_token];
                let column_word = self.words[right_token * width + left_token];
                let row = decode_binary16_bits(row_word).map_err(|error| error.to_string())?;
                let column = decode_binary16_bits(column_word).map_err(|error| error.to_string())?;
                result.insert(
                    (left_at as u32 + 1, right_at as u32 + 1),
                    PairUncertainty {
                        source_lineage: format!(
                            "{} / directional PAE {left_chain}:{left_residue}<->{right_chain}:{right_residue}",
                            self.source_npz_release_path
                        ),
                        row_given_column_bits: row_word,
                        column_given_row_bits: column_word,
                        row_given_column: ExactInterval::point(
                            row.enclosure(FloatReading::ExactBitPattern).lower,
                        ),
                        column_given_row: ExactInterval::point(
                            column.enclosure(FloatReading::ExactBitPattern).lower,
                        ),
                        row_given_column_ulp: row.unit_in_last_place(),
                        column_given_row_ulp: column.unit_in_last_place(),
                    },
                );
            }
        }
        Ok(result)
    }
}

pub fn read(
    directory: &Path,
    source_npz_release_path: &str,
    source_npz_sha256: &str,
) -> Result<PaeAtlas, String> {
    let mut arrays = BTreeMap::<String, NpyArray>::new();
    let mut extracted_members = Vec::new();
    for name in REQUIRED {
        let path = directory.join(name);
        let array = NpyArray::read(&path)?;
        extracted_members.push(NpyMember {
            name: (*name).to_owned(),
            local_path: path.display().to_string(),
            sha256: digest_path(&path)?,
            descr: array.descr.clone(),
            shape: array.shape.clone(),
            octets: std::fs::metadata(&path)
                .map_err(|error| error.to_string())?
                .len(),
        });
        arrays.insert((*name).to_owned(), array);
    }
    let words = arrays["pae.npy"].binary16()?;
    let shape = &arrays["pae.npy"].shape;
    if shape.len() != 2 || shape[0] != shape[1] {
        return Err(format!("PAE shape {shape:?} is not a square matrix"));
    }
    let token_chain_ids = arrays["token_chain_ids.npy"].unicode()?;
    let token_res_ids = arrays["token_res_ids.npy"].i32_le()?;
    if token_chain_ids.len() != shape[0] || token_res_ids.len() != shape[0] {
        return Err(format!(
            "PAE extent {} disagrees with chain {} / residue {} token faces",
            shape[0],
            token_chain_ids.len(),
            token_res_ids.len()
        ));
    }
    let mut finite_binary16_words = 0usize;
    let mut refused_nonfinite_words = 0usize;
    for word in &words {
        if decode_binary16_bits(*word).is_ok() {
            finite_binary16_words += 1;
        } else {
            refused_nonfinite_words += 1;
        }
    }
    if refused_nonfinite_words != 0 {
        return Err(format!(
            "PAE carries {refused_nonfinite_words} non-finite binary16 words"
        ));
    }
    let scalar = |name: &str| -> Result<String, String> {
        let values = arrays[name].unicode()?;
        match values.as_slice() {
            [value] => Ok(value.clone()),
            _ => Err(format!("{name} is not one scalar string")),
        }
    };
    let matrix_shape = [shape[0], shape[1]];
    Ok(PaeAtlas {
        schema: "holonics.m5.exact-binary16-pae-atlas.v1".to_owned(),
        source_npz_release_path: source_npz_release_path.to_owned(),
        source_npz_sha256: source_npz_sha256.to_owned(),
        extracted_members,
        design_uuid: scalar("design_uuid.npy")?,
        design_name: scalar("design_name.npy")?,
        target: scalar("target.npy")?,
        cofolding_model: scalar("cofolding_model.npy")?,
        stoichiometry: scalar("stoichiometry.npy")?,
        target_form: scalar("target_form.npy")?,
        seed: scalar("seed.npy")?,
        matrix_shape,
        finite_binary16_words,
        refused_nonfinite_words,
        token_population: token_chain_ids.len(),
        uncertainty_law: "every <f2 word is decoded as its exact IEEE binary16 dyadic; the directional PAE value is retained as a point and its format ulp is carried separately; PAE is predictor testimony, not a coordinate enclosure or physical measurement".to_owned(),
        words,
        token_chain_ids,
        token_res_ids,
    })
}

struct NpyArray {
    path: PathBuf,
    descr: String,
    shape: Vec<usize>,
    data: Vec<u8>,
}

impl NpyArray {
    fn read(path: &Path) -> Result<Self, String> {
        let bytes = std::fs::read(path).map_err(|error| error.to_string())?;
        if bytes.len() < 10 || &bytes[..6] != b"\x93NUMPY" {
            return Err(format!("{} is not an NPY occurrence", path.display()));
        }
        let major = bytes[6];
        let header_octets = match major {
            1 => u16::from_le_bytes([bytes[8], bytes[9]]) as usize,
            2 | 3 => {
                if bytes.len() < 12 {
                    return Err(format!("{} has a truncated NPY header", path.display()));
                }
                u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]) as usize
            }
            _ => return Err(format!("{} uses unsupported NPY major {major}", path.display())),
        };
        let header_start = if major == 1 { 10 } else { 12 };
        let data_start = header_start + header_octets;
        if data_start > bytes.len() {
            return Err(format!("{} NPY header leaves the file", path.display()));
        }
        let header = std::str::from_utf8(&bytes[header_start..data_start])
            .map_err(|error| error.to_string())?;
        if !header.contains("'fortran_order': False") {
            return Err(format!("{} is not row-major NPY material", path.display()));
        }
        let descr = between(header, "'descr': '", "'")?.to_owned();
        let shape_text = between(header, "'shape': (", ")")?;
        let shape = shape_text
            .split(',')
            .map(str::trim)
            .filter(|field| !field.is_empty())
            .map(|field| field.parse::<usize>().map_err(|error| error.to_string()))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            path: path.to_owned(),
            descr,
            shape,
            data: bytes[data_start..].to_vec(),
        })
    }

    fn elements(&self) -> usize {
        if self.shape.is_empty() {
            1
        } else {
            self.shape.iter().product()
        }
    }

    fn binary16(&self) -> Result<Vec<u16>, String> {
        if self.descr != "<f2" || self.data.len() != self.elements() * 2 {
            return Err(format!(
                "{} is {:?}, not a complete <f2 array",
                self.path.display(),
                self.descr
            ));
        }
        Ok(self
            .data
            .chunks_exact(2)
            .map(|word| u16::from_le_bytes([word[0], word[1]]))
            .collect())
    }

    fn i32_le(&self) -> Result<Vec<i32>, String> {
        if self.descr != "<i4" || self.data.len() != self.elements() * 4 {
            return Err(format!(
                "{} is {:?}, not a complete <i4 array",
                self.path.display(),
                self.descr
            ));
        }
        Ok(self
            .data
            .chunks_exact(4)
            .map(|word| i32::from_le_bytes([word[0], word[1], word[2], word[3]]))
            .collect())
    }

    fn unicode(&self) -> Result<Vec<String>, String> {
        let width = self
            .descr
            .strip_prefix("<U")
            .ok_or_else(|| format!("{} is not a little-endian Unicode array", self.path.display()))?
            .parse::<usize>()
            .map_err(|error| error.to_string())?;
        let bytes_per = width * 4;
        if self.data.len() != self.elements() * bytes_per {
            return Err(format!("{} has a truncated Unicode payload", self.path.display()));
        }
        self.data
            .chunks_exact(bytes_per)
            .map(|item| {
                item.chunks_exact(4)
                    .map(|word| u32::from_le_bytes([word[0], word[1], word[2], word[3]]))
                    .take_while(|code| *code != 0)
                    .map(|code| {
                        char::from_u32(code).ok_or_else(|| {
                            format!("{} contains invalid Unicode scalar {code}", self.path.display())
                        })
                    })
                    .collect()
            })
            .collect()
    }
}

fn between<'a>(text: &'a str, prefix: &str, suffix: &str) -> Result<&'a str, String> {
    let start = text
        .find(prefix)
        .ok_or_else(|| format!("NPY header lacks {prefix}"))?
        + prefix.len();
    let end = text[start..]
        .find(suffix)
        .ok_or_else(|| format!("NPY header lacks closing {suffix}"))?
        + start;
    Ok(&text[start..end])
}
