//! The one M5 coordinate family, read **through the library intake**.
//!
//! [definition] Every decimal token, enclosure and outward resident projection in this deed is
//! `holonic_engine::physical_intake::mmcif`'s. This file used to carry its own copy of
//! `DecimalToken::parse` and `DecimalToken::projected_wire`; the copy is gone, and what remains is
//! only the M5 receiver's own two choices: the alpha-carbon representative of each residue, and
//! the binding of a component by its complete ordered one-letter sequence. Neither is a reader.

use std::path::Path;

use holonic_engine::physical_constraint_complex::{
    ComponentMaterial, CoordinateBox3, ResidueMaterial,
};
use holonic_engine::physical_intake::mmcif::{AtomOccurrence, StructurePresentation};
use serde::Serialize;

/// The `_atom_site.label_atom_id` this deed selects as each residue's representative.
pub const REPRESENTATIVE: &str = "CA";

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CifResidue {
    pub source_ordinal: i32,
    pub monomer: String,
    /// The residue's representative atom, retained as the library's own occurrence: its three
    /// coordinate tokens keep their written significands and their own decimal places.
    pub ca: AtomOccurrence,
}

impl CifResidue {
    /// The representative's scaled integer wire on `10^places`, rounded strictly outward by
    /// `mmcif::DecimalToken::projected_wire`.
    pub fn wire(&self, places: u32) -> Result<([i64; 3], [i64; 3]), String> {
        self.ca.projected_wire(places).map_err(|error| error.to_string())
    }

    /// The same projection as an exact rational box.
    pub fn box3_at_places(&self, places: u32) -> Result<CoordinateBox3, String> {
        self.ca.projected_box(places).map_err(|error| error.to_string())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CifComponent {
    pub source_chain: String,
    pub residues: Vec<CifResidue>,
    pub one_letter_sequence: String,
}

impl CifComponent {
    pub fn material_at_places(
        &self,
        presentation: &str,
        decimal_places: u32,
    ) -> Result<ComponentMaterial, String> {
        Ok(ComponentMaterial {
            lineage: format!(
                "{presentation} / source chain {} / outward resident decimal projection 10^-{decimal_places}",
                self.source_chain
            ),
            residues: self
                .residues
                .iter()
                .map(|residue| {
                    Ok(ResidueMaterial {
                        source_ordinal: residue.source_ordinal,
                        monomer: residue.monomer.clone(),
                        position: residue.box3_at_places(decimal_places)?,
                    })
                })
                .collect::<Result<Vec<_>, String>>()?,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CifPresentation {
    pub schema: String,
    pub source_path: String,
    pub source_sha256: String,
    pub components: Vec<CifComponent>,
    pub ca_occurrences: usize,
    pub maximum_decimal_places: u32,
    pub coordinate_interval_law: String,
}

impl CifPresentation {
    pub fn component_with_sequence(&self, sequence: &str) -> Result<usize, String> {
        let matches = self
            .components
            .iter()
            .enumerate()
            .filter_map(|(at, component)| (component.one_letter_sequence == sequence).then_some(at))
            .collect::<Vec<_>>();
        match matches.as_slice() {
            [at] => Ok(*at),
            [] => Err(format!(
                "{} has no component with the addressed ordered sequence",
                self.source_path
            )),
            _ => Err(format!(
                "{} has multiple components with the addressed ordered sequence; lineage is open",
                self.source_path
            )),
        }
    }
}

/// Read one mmCIF occurrence through the library's all-atom intake and select this deed's
/// alpha-carbon representatives.
///
/// The library retains every `_atom_site` row; the selection here keeps the residues that carry a
/// representative and drops the chains that carry none — the zinc occurrences of the CUL1-RBX1
/// form have no alpha carbon and are not protein components.
pub fn read(path: &Path, source_sha256: &str) -> Result<CifPresentation, String> {
    let presentation = StructurePresentation::read(path).map_err(|error| error.to_string())?;
    let mut components = Vec::new();
    let mut maximum_decimal_places = 0_u32;
    for chain in &presentation.chains {
        let mut residues = Vec::new();
        for residue in &chain.residues {
            let Some(at) = residue
                .labelled_atom(REPRESENTATIVE)
                .map_err(|error| error.to_string())?
            else {
                continue;
            };
            let ca = residue.atoms[at].clone();
            maximum_decimal_places = maximum_decimal_places.max(ca.decimal_places());
            residues.push(CifResidue {
                source_ordinal: residue.source_ordinal,
                monomer: residue.monomer.clone(),
                ca,
            });
        }
        if residues.is_empty() {
            continue;
        }
        let one_letter_sequence = residues
            .iter()
            .map(|residue| one_letter(&residue.monomer))
            .collect::<Result<String, _>>()?;
        components.push(CifComponent {
            source_chain: chain.label_asym_id.clone(),
            residues,
            one_letter_sequence,
        });
    }
    if components.is_empty() {
        return Err(format!(
            "{} presents no component carrying a {REPRESENTATIVE} representative",
            path.display()
        ));
    }
    let ca_occurrences = components.iter().map(|body| body.residues.len()).sum();
    Ok(CifPresentation {
        schema: "holonics.m5.cif-ca-presentation.v1".to_owned(),
        source_path: path.display().to_string(),
        source_sha256: source_sha256.to_owned(),
        components,
        ca_occurrences,
        maximum_decimal_places,
        coordinate_interval_law: presentation.coordinate_interval_law,
    })
}

fn one_letter(monomer: &str) -> Result<char, String> {
    match monomer {
        "ALA" => Ok('A'),
        "ARG" => Ok('R'),
        "ASN" => Ok('N'),
        "ASP" => Ok('D'),
        "CYS" => Ok('C'),
        "GLN" => Ok('Q'),
        "GLU" => Ok('E'),
        "GLY" => Ok('G'),
        "HIS" => Ok('H'),
        "ILE" => Ok('I'),
        "LEU" => Ok('L'),
        "LYS" => Ok('K'),
        "MET" => Ok('M'),
        "PHE" => Ok('F'),
        "PRO" => Ok('P'),
        "SER" => Ok('S'),
        "THR" => Ok('T'),
        "TRP" => Ok('W'),
        "TYR" => Ok('Y'),
        "VAL" => Ok('V'),
        other => Err(format!(
            "the admitted protein component contains unsupported monomer {other}"
        )),
    }
}
