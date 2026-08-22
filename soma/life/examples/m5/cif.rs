//! Narrow mmCIF atom-site face for the one M5 coordinate family.

use std::collections::BTreeMap;
use std::path::Path;

use holonic_engine::physical_constraint_complex::{
    ComponentMaterial, CoordinateBox3, ResidueMaterial,
};
use num_bigint::BigInt;
use relational_geometry::Rat;
use serde::Serialize;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DecimalCoordinate {
    pub token: String,
    pub significand: i64,
    pub decimal_places: u32,
    pub outward_last_place: CoordinateInterval,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CoordinateInterval {
    pub lower: Rat,
    pub upper: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CifPoint {
    pub x: DecimalCoordinate,
    pub y: DecimalCoordinate,
    pub z: DecimalCoordinate,
}

impl CifPoint {
    pub fn wire(&self, decimal_places: u32) -> Result<([i64; 3], [i64; 3]), String> {
        let wire = |coordinate: &DecimalCoordinate| -> Result<(i64, i64), String> {
            if decimal_places >= coordinate.decimal_places {
                let shift = decimal_places - coordinate.decimal_places;
                let multiplier = 10_i64
                    .checked_pow(shift)
                    .ok_or_else(|| "the coordinate scale exceeds the exact i64 wire".to_owned())?;
                let center = coordinate
                    .significand
                    .checked_mul(multiplier)
                    .ok_or_else(|| "the coordinate center exceeds the exact i64 wire".to_owned())?;
                Ok((
                    center
                        .checked_sub(multiplier)
                        .ok_or_else(|| "coordinate lower bound overflow".to_owned())?,
                    center
                        .checked_add(multiplier)
                        .ok_or_else(|| "coordinate upper bound overflow".to_owned())?,
                ))
            } else {
                // Project the source interval [(s-1)/10^p,(s+1)/10^p] outward onto the
                // coarser resident denominator 10^q. `div_euclid` is floor for the positive
                // divisor; negating the floor of the negation is exact ceiling.
                let divisor = 10_i64
                    .checked_pow(coordinate.decimal_places - decimal_places)
                    .ok_or_else(|| "the coordinate divisor exceeds the exact i64 wire".to_owned())?;
                let lower_numerator = coordinate
                    .significand
                    .checked_sub(1)
                    .ok_or_else(|| "coordinate lower bound overflow".to_owned())?;
                let upper_numerator = coordinate
                    .significand
                    .checked_add(1)
                    .ok_or_else(|| "coordinate upper bound overflow".to_owned())?;
                let lower = lower_numerator.div_euclid(divisor);
                let upper = upper_numerator
                    .checked_neg()
                    .ok_or_else(|| "coordinate upper ceiling overflow".to_owned())?
                    .div_euclid(divisor)
                    .checked_neg()
                    .ok_or_else(|| "coordinate upper ceiling overflow".to_owned())?;
                Ok((lower, upper))
            }
        };
        let (lx, ux) = wire(&self.x)?;
        let (ly, uy) = wire(&self.y)?;
        let (lz, uz) = wire(&self.z)?;
        Ok(([lx, ly, lz], [ux, uy, uz]))
    }

    pub fn box3_at_places(&self, decimal_places: u32) -> Result<CoordinateBox3, String> {
        let (lower, upper) = self.wire(decimal_places)?;
        let denominator = BigInt::from(
            10_i64
                .checked_pow(decimal_places)
                .ok_or_else(|| "the coordinate denominator exceeds i64".to_owned())?,
        );
        Ok(CoordinateBox3 {
            x: holonic_engine::exact_value::ExactInterval {
                lower: Rat::new(BigInt::from(lower[0]), denominator.clone()),
                upper: Rat::new(BigInt::from(upper[0]), denominator.clone()),
            },
            y: holonic_engine::exact_value::ExactInterval {
                lower: Rat::new(BigInt::from(lower[1]), denominator.clone()),
                upper: Rat::new(BigInt::from(upper[1]), denominator.clone()),
            },
            z: holonic_engine::exact_value::ExactInterval {
                lower: Rat::new(BigInt::from(lower[2]), denominator.clone()),
                upper: Rat::new(BigInt::from(upper[2]), denominator),
            },
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CifResidue {
    pub source_ordinal: i32,
    pub monomer: String,
    pub ca: CifPoint,
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
                        position: residue.ca.box3_at_places(decimal_places)?,
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

pub fn read(path: &Path, source_sha256: &str) -> Result<CifPresentation, String> {
    let text = std::fs::read_to_string(path).map_err(|error| error.to_string())?;
    let lines = text.lines().collect::<Vec<_>>();
    let mut headers = Vec::<String>::new();
    let mut rows = Vec::<Vec<&str>>::new();
    let mut at = 0usize;
    while at < lines.len() {
        if lines[at].trim() != "loop_" {
            at += 1;
            continue;
        }
        let mut cursor = at + 1;
        let mut candidate = Vec::<String>::new();
        while cursor < lines.len() && lines[cursor].trim_start().starts_with('_') {
            candidate.push(lines[cursor].trim().to_owned());
            cursor += 1;
        }
        if !candidate.iter().any(|name| name.starts_with("_atom_site.")) {
            at = cursor;
            continue;
        }
        headers = candidate;
        while cursor < lines.len() {
            let line = lines[cursor].trim();
            if line == "#" || line == "loop_" || line.starts_with('_') {
                break;
            }
            if !line.is_empty() {
                let fields = line.split_whitespace().collect::<Vec<_>>();
                if fields.len() != headers.len() {
                    return Err(format!(
                        "{} atom_site row {} has {} fields under {} headers",
                        path.display(),
                        cursor + 1,
                        fields.len(),
                        headers.len()
                    ));
                }
                rows.push(fields);
            }
            cursor += 1;
        }
        break;
    }
    if headers.is_empty() || rows.is_empty() {
        return Err(format!("{} has no atom_site loop", path.display()));
    }
    let column = |name: &str| -> Result<usize, String> {
        headers
            .iter()
            .position(|candidate| candidate == name)
            .ok_or_else(|| format!("{} has no {name} atom_site face", path.display()))
    };
    let atom = column("_atom_site.label_atom_id")?;
    let monomer = column("_atom_site.label_comp_id")?;
    let chain = column("_atom_site.label_asym_id")?;
    let residue = column("_atom_site.label_seq_id")?;
    let x = column("_atom_site.Cartn_x")?;
    let y = column("_atom_site.Cartn_y")?;
    let z = column("_atom_site.Cartn_z")?;

    let mut by_chain = BTreeMap::<String, BTreeMap<i32, CifResidue>>::new();
    let mut maximum_decimal_places = 0_u32;
    for row in rows.into_iter().filter(|row| unquote(row[atom]) == "CA") {
        let source_chain = unquote(row[chain]).to_owned();
        let source_ordinal = unquote(row[residue])
            .parse::<i32>()
            .map_err(|error| error.to_string())?;
        let point = CifPoint {
            x: parse_decimal(row[x])?,
            y: parse_decimal(row[y])?,
            z: parse_decimal(row[z])?,
        };
        maximum_decimal_places = maximum_decimal_places
            .max(point.x.decimal_places)
            .max(point.y.decimal_places)
            .max(point.z.decimal_places);
        let body = CifResidue {
            source_ordinal,
            monomer: unquote(row[monomer]).to_owned(),
            ca: point,
        };
        if by_chain
            .entry(source_chain.clone())
            .or_default()
            .insert(source_ordinal, body)
            .is_some()
        {
            return Err(format!(
                "{} repeats the CA occurrence {source_chain}:{source_ordinal}",
                path.display()
            ));
        }
    }
    let components = by_chain
        .into_iter()
        .map(|(source_chain, residues)| {
            let residues = residues.into_values().collect::<Vec<_>>();
            let one_letter_sequence = residues
                .iter()
                .map(|residue| one_letter(&residue.monomer))
                .collect::<Result<String, _>>()?;
            Ok(CifComponent {
                source_chain,
                residues,
                one_letter_sequence,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let ca_occurrences = components.iter().map(|body| body.residues.len()).sum();
    Ok(CifPresentation {
        schema: "holonics.m5.cif-ca-presentation.v1".to_owned(),
        source_path: path.display().to_string(),
        source_sha256: source_sha256.to_owned(),
        components,
        ca_occurrences,
        maximum_decimal_places,
        coordinate_interval_law: "each stored decimal is retained as its exact rational center with one complete last-decimal unit outward on each side; this is an exterior quantization aperture, not a claim about predictor error".to_owned(),
    })
}

fn parse_decimal(raw: &str) -> Result<DecimalCoordinate, String> {
    let token = unquote(raw);
    let negative = token.starts_with('-');
    let unsigned = token.trim_start_matches(['-', '+']);
    let (whole, fraction) = unsigned.split_once('.').unwrap_or((unsigned, ""));
    if whole.is_empty()
        || !whole.chars().all(|ch| ch.is_ascii_digit())
        || !fraction.chars().all(|ch| ch.is_ascii_digit())
    {
        return Err(format!("coordinate token {raw:?} is not a plain decimal"));
    }
    let decimal_places = fraction.len() as u32;
    let scale = 10_i64
        .checked_pow(decimal_places)
        .ok_or_else(|| format!("coordinate token {raw:?} exceeds the exact decimal wire"))?;
    let whole = whole.parse::<i64>().map_err(|error| error.to_string())?;
    let fraction = if fraction.is_empty() {
        0
    } else {
        fraction.parse::<i64>().map_err(|error| error.to_string())?
    };
    let magnitude = whole
        .checked_mul(scale)
        .and_then(|value| value.checked_add(fraction))
        .ok_or_else(|| format!("coordinate token {raw:?} overflows"))?;
    let significand = if negative { -magnitude } else { magnitude };
    let center = Rat::new(BigInt::from(significand), BigInt::from(scale));
    let unit = Rat::new(BigInt::from(1), BigInt::from(scale));
    Ok(DecimalCoordinate {
        token: token.to_owned(),
        significand,
        decimal_places,
        outward_last_place: CoordinateInterval {
            lower: &center - &unit,
            upper: &center + &unit,
        },
    })
}

fn unquote(token: &str) -> &str {
    token
        .strip_prefix('\'')
        .and_then(|body| body.strip_suffix('\''))
        .or_else(|| token.strip_prefix('"').and_then(|body| body.strip_suffix('"')))
        .unwrap_or(token)
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
        other => Err(format!("the admitted protein component contains unsupported monomer {other}")),
    }
}
