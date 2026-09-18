//! All-atom mmCIF `_atom_site` intake, with exact rational coordinates and no float anywhere.
//!
//! # The coordinate-exactness discipline this library owns
//!
//! [definition] **A coordinate's enclosure is the last place of its own written token, and the
//! scaled integer wire is a separately declared, always-outward projection.**
//!
//! A stored token such as `4.697824` declares six decimal places. The intake retains it as the
//! exact pair `(significand, decimal_places) = (4_697_824, 6)`, whose exact rational centre is
//! `4697824/10^6` and whose enclosure is `[(s−1)/10^p, (s+1)/10^p]` — one complete last-place unit
//! outward on each side. That is an exterior *quantization* aperture and never a claim about
//! predictor error.
//!
//! The two readers this replaced both derived **one** decimal count for a whole family and
//! re-expressed every token on it at parse time (the M5 deed's own `CifPoint::wire`, since
//! migrated onto [`DecimalToken::projected_wire`] and deleted, through
//! `fold.rs::derive_resident_places`; and `grain_tower/tests.rs::outward_wire` with a hard-coded
//! seven). Three reasons the library owns the per-token discipline instead:
//!
//! 1. **The precision belongs to the token.** A token written `12.3` and one written `12.300` are
//!    different testimony. Collapsing both onto a family-wide denominator at parse time destroys
//!    that distinction before anything is founded.
//! 2. **An enclosure must not depend on other coordinates.** A family-wide count is derived from
//!    the widest token in the file, so on the old path the enclosure of *this* atom changed when
//!    an unrelated atom elsewhere was written with more digits. That is a receiver-side choice
//!    wearing the costume of a source property.
//! 3. **Projection is a receiver's declaration and is checkable.** [`DecimalToken::projected_wire`]
//!    onto a declared denominator rounds strictly outward, so the projected interval *contains*
//!    the source enclosure. Containment is exactly the hypothesis of
//!    `Foundation/ExteriorIntake.lean::widening_never_flips_a_decision`: a widened interval can
//!    turn a decided contact `Open`, and can never turn `Inside` into `Outside` or the reverse.
//!    The resident wire is therefore a safe coarsening with a stated law, not a silent rounding.
//!
//! The consequence for the measured census is nil and that is the point: the M5 coordinate tokens
//! carry three to eleven decimal places and the declared resident wire is `10^7`, so the
//! projection is exact multiplication where `p ≤ 7` and an outward widening where `p > 7`, which
//! is what `grain_tower/tests.rs` already enacts. The discipline changes what the library
//! *guarantees*, not what this data returns.
//!
//! # No float
//!
//! Parsing is digit arithmetic on `i64` with `checked_*` at every step; the exact centre and
//! enclosure are `relational_geometry::Rat` over `BigInt`; the wire is `i64` numerators over a
//! declared power of ten. There is no `f32`, no `f64`, no `parse::<f64>()` and no cast between an
//! integer and a float in this file. A token that is not a plain decimal, a row whose field count
//! disagrees with the header, an absent column and an overflowing significand are each a typed
//! [`IntakeRefusal`], never a panic.

use std::collections::BTreeMap;
use std::path::Path;

use num_bigint::BigInt;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};

use crate::exact_value::ExactInterval;
use crate::physical_constraint_complex::CoordinateBox3;

use super::IntakeRefusal;

/// One written decimal coordinate token, retained exactly as the source declares it.
///
/// Lean counterpart: `Foundation/ExteriorIntake.lean::DecimalToken` with
/// `tokenEnclosure_contains_centre`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DecimalToken {
    /// The token exactly as it was written, retained as testimony.
    pub token: String,
    /// The signed integer significand: the token with its decimal point removed.
    pub significand: i64,
    /// How many decimal places the token declares.
    pub decimal_places: u32,
}

impl DecimalToken {
    /// Parse a plain decimal token. Scientific notation, an empty integer part and a non-digit are
    /// each refused by name; nothing is coerced.
    pub fn parse(raw: &str) -> Result<Self, IntakeRefusal> {
        let token = unquote(raw);
        // Exactly one optional leading sign, stripped once. Trimming the whole run of signs would
        // read `"+-4.5"` and `"--4.5"` as plain decimals and give them the sign of the first
        // character, which is testimony the source never wrote; the single strip leaves the second
        // sign inside `whole`, where the digit check below refuses the token by name.
        let (negative, unsigned) = match token.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, token.strip_prefix('+').unwrap_or(token)),
        };
        let (whole, fraction) = unsigned.split_once('.').unwrap_or((unsigned, ""));
        if whole.is_empty()
            || !whole.chars().all(|ch| ch.is_ascii_digit())
            || !fraction.chars().all(|ch| ch.is_ascii_digit())
        {
            return Err(IntakeRefusal::CoordinateNotAPlainDecimal {
                token: raw.to_owned(),
            });
        }
        let decimal_places = fraction.len() as u32;
        let overflow = || IntakeRefusal::CoordinateLeavesTheExactWire {
            token: raw.to_owned(),
            detail: "the decimal significand exceeds the exact i64 wire".to_owned(),
        };
        let scale = 10_i64.checked_pow(decimal_places).ok_or_else(overflow)?;
        let whole = whole.parse::<i64>().map_err(|_| overflow())?;
        let fraction_value = if fraction.is_empty() {
            0
        } else {
            fraction.parse::<i64>().map_err(|_| overflow())?
        };
        let magnitude = whole
            .checked_mul(scale)
            .and_then(|value| value.checked_add(fraction_value))
            .ok_or_else(overflow)?;
        Ok(Self {
            token: token.to_owned(),
            significand: if negative { -magnitude } else { magnitude },
            decimal_places,
        })
    }

    /// `10^decimal_places`, the token's own denominator.
    pub fn denominator(&self) -> Result<i64, IntakeRefusal> {
        10_i64
            .checked_pow(self.decimal_places)
            .ok_or_else(|| IntakeRefusal::CoordinateLeavesTheExactWire {
                token: self.token.clone(),
                detail: "the token denominator exceeds the exact i64 wire".to_owned(),
            })
    }

    /// The exact rational the token names. This is not an approximation of the token; it **is**
    /// the token.
    pub fn exact_centre(&self) -> Result<Rat, IntakeRefusal> {
        Ok(Rat::new(
            BigInt::from(self.significand),
            BigInt::from(self.denominator()?),
        ))
    }

    /// The source enclosure `[(s−1)/10^p, (s+1)/10^p]`: one complete last-place unit outward on
    /// each side of the written centre.
    pub fn source_enclosure(&self) -> Result<ExactInterval, IntakeRefusal> {
        let denominator = BigInt::from(self.denominator()?);
        Ok(ExactInterval {
            lower: Rat::new(BigInt::from(self.significand) - 1, denominator.clone()),
            upper: Rat::new(BigInt::from(self.significand) + 1, denominator),
        })
    }

    /// The source enclosure's numerators on a declared denominator `10^places`, rounded **strictly
    /// outward**: the lower endpoint floors and the upper ceils.
    ///
    /// The returned interval therefore contains [`Self::source_enclosure`] for every `places`, so
    /// `Foundation/ExteriorIntake.lean::widening_never_flips_a_decision` applies to it.
    pub fn projected_wire(&self, places: u32) -> Result<(i64, i64), IntakeRefusal> {
        let overflow = |detail: &str| IntakeRefusal::CoordinateLeavesTheExactWire {
            token: self.token.clone(),
            detail: detail.to_owned(),
        };
        if places >= self.decimal_places {
            let multiplier = 10_i64
                .checked_pow(places - self.decimal_places)
                .ok_or_else(|| overflow("the projection multiplier leaves the i64 wire"))?;
            let centre = self
                .significand
                .checked_mul(multiplier)
                .ok_or_else(|| overflow("the projected centre leaves the i64 wire"))?;
            Ok((
                centre
                    .checked_sub(multiplier)
                    .ok_or_else(|| overflow("the projected lower bound leaves the i64 wire"))?,
                centre
                    .checked_add(multiplier)
                    .ok_or_else(|| overflow("the projected upper bound leaves the i64 wire"))?,
            ))
        } else {
            // `div_euclid` is the floor for a positive divisor; negating the floor of the negation
            // is the exact ceiling. Both are integer operations.
            let divisor = 10_i64
                .checked_pow(self.decimal_places - places)
                .ok_or_else(|| overflow("the projection divisor leaves the i64 wire"))?;
            let lower_numerator = self
                .significand
                .checked_sub(1)
                .ok_or_else(|| overflow("the source lower bound leaves the i64 wire"))?;
            let upper_numerator = self
                .significand
                .checked_add(1)
                .ok_or_else(|| overflow("the source upper bound leaves the i64 wire"))?;
            let lower = lower_numerator.div_euclid(divisor);
            let upper = upper_numerator
                .checked_neg()
                .ok_or_else(|| overflow("the ceiling negation leaves the i64 wire"))?
                .div_euclid(divisor)
                .checked_neg()
                .ok_or_else(|| overflow("the ceiling negation leaves the i64 wire"))?;
            Ok((lower, upper))
        }
    }

    /// [`Self::projected_wire`] as an exact rational interval on `10^places`.
    pub fn projected_enclosure(&self, places: u32) -> Result<ExactInterval, IntakeRefusal> {
        let (lower, upper) = self.projected_wire(places)?;
        let denominator = BigInt::from(10_i64.checked_pow(places).ok_or_else(|| {
            IntakeRefusal::CoordinateLeavesTheExactWire {
                token: self.token.clone(),
                detail: "the resident denominator exceeds the exact i64 wire".to_owned(),
            }
        })?);
        Ok(ExactInterval {
            lower: Rat::new(BigInt::from(lower), denominator.clone()),
            upper: Rat::new(BigInt::from(upper), denominator),
        })
    }
}

/// One `_atom_site` row, retained whole. **Every** row is retained: there is no alpha-carbon
/// filter and no element filter anywhere in this module.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtomOccurrence {
    /// `_atom_site.label_atom_id`.
    pub label: String,
    /// `_atom_site.type_symbol`, when the presentation carries that column.
    pub element: Option<String>,
    /// `_atom_site.label_alt_id`, when the presentation carries that column.
    pub alternate: Option<String>,
    /// The `x` coordinate token.
    pub x: DecimalToken,
    /// The `y` coordinate token.
    pub y: DecimalToken,
    /// The `z` coordinate token.
    pub z: DecimalToken,
}

impl AtomOccurrence {
    /// The exact coordinate box from each token's own last place.
    pub fn source_box(&self) -> Result<CoordinateBox3, IntakeRefusal> {
        Ok(CoordinateBox3 {
            x: self.x.source_enclosure()?,
            y: self.y.source_enclosure()?,
            z: self.z.source_enclosure()?,
        })
    }

    /// The exact coordinate box projected outward onto a declared denominator `10^places`.
    pub fn projected_box(&self, places: u32) -> Result<CoordinateBox3, IntakeRefusal> {
        Ok(CoordinateBox3 {
            x: self.x.projected_enclosure(places)?,
            y: self.y.projected_enclosure(places)?,
            z: self.z.projected_enclosure(places)?,
        })
    }

    /// The scaled integer wire `grain_tower::ScaledOccurrence` carries, on `10^places`.
    pub fn projected_wire(&self, places: u32) -> Result<([i64; 3], [i64; 3]), IntakeRefusal> {
        let (lx, ux) = self.x.projected_wire(places)?;
        let (ly, uy) = self.y.projected_wire(places)?;
        let (lz, uz) = self.z.projected_wire(places)?;
        Ok(([lx, ly, lz], [ux, uy, uz]))
    }

    /// The widest declared decimal place count among the three tokens.
    pub fn decimal_places(&self) -> u32 {
        self.x
            .decimal_places
            .max(self.y.decimal_places)
            .max(self.z.decimal_places)
    }
}

/// One monomer of a presented chain, with **every** atom the presentation gave it, in file order.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResidueOccurrence {
    /// `_atom_site.label_seq_id`, the source's own ordinal.
    pub source_ordinal: i32,
    /// `_atom_site.label_comp_id`.
    pub monomer: String,
    /// Every atom, in the order the presentation wrote them.
    pub atoms: Vec<AtomOccurrence>,
}

impl ResidueOccurrence {
    /// The position, among this residue's atoms, of the atom carrying a declared label. `None`
    /// when the residue has none; a refusal when it has several, because a representative must be
    /// unique to be a representative.
    pub fn labelled_atom(&self, label: &str) -> Result<Option<usize>, IntakeRefusal> {
        let matches = self
            .atoms
            .iter()
            .enumerate()
            .filter(|(_, atom)| atom.label == label)
            .map(|(at, _)| at)
            .collect::<Vec<_>>();
        match matches.as_slice() {
            [] => Ok(None),
            [at] => Ok(Some(*at)),
            several => Err(IntakeRefusal::RepeatedRepresentativeAtom {
                residue: self.source_ordinal,
                label: label.to_owned(),
                occurrences: several.len(),
            }),
        }
    }
}

/// One presented chain: its residues in ascending source ordinal, each with all of its atoms.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChainOccurrence {
    /// `_atom_site.label_asym_id`.
    pub label_asym_id: String,
    /// `_atom_site.label_entity_id`, when the presentation carries that column.
    pub entity: Option<String>,
    /// The residues, ascending by source ordinal.
    pub residues: Vec<ResidueOccurrence>,
    /// How many atom occurrences this chain retains.
    pub atom_occurrences: usize,
}

impl ChainOccurrence {
    /// The source ordinals of this chain's residues, ascending.
    pub fn source_ordinals(&self) -> Vec<i32> {
        self.residues
            .iter()
            .map(|residue| residue.source_ordinal)
            .collect()
    }
}

/// One complete all-atom presentation of one mmCIF occurrence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StructurePresentation {
    /// The schema this presentation serializes under.
    pub schema: String,
    /// Exterior lineage of the source, retained as testimony and never used as a semantic taxon.
    pub source_lineage: String,
    /// Every presented chain, ordered by `label_asym_id`.
    pub chains: Vec<ChainOccurrence>,
    /// How many `_atom_site` rows were retained. This equals the number of rows in the loop: the
    /// intake discards none.
    pub atom_occurrences: usize,
    /// How many rows the loop carried, so that retention is checkable rather than asserted.
    pub presented_rows: usize,
    /// The widest decimal place count any coordinate token declares.
    pub maximum_decimal_places: u32,
    /// The declared coordinate law, retained in the artifact so a consumer reads it.
    pub coordinate_interval_law: String,
}

impl StructurePresentation {
    /// Read one mmCIF occurrence from the filesystem.
    pub fn read(path: &Path) -> Result<Self, IntakeRefusal> {
        let text =
            std::fs::read_to_string(path).map_err(|error| IntakeRefusal::SourceUnreadable {
                origin: path.display().to_string(),
                detail: error.to_string(),
            })?;
        Self::parse(path.display().to_string(), &text)
    }

    /// Parse one mmCIF occurrence from its text.
    pub fn parse(source_lineage: impl Into<String>, text: &str) -> Result<Self, IntakeRefusal> {
        let source_lineage = source_lineage.into();
        let refusal = |detail: String| IntakeRefusal::MalformedStructure {
            origin: source_lineage.clone(),
            detail,
        };
        let (headers, rows) = atom_site_loop(&source_lineage, text)?;
        let column = |name: &str| -> Result<usize, IntakeRefusal> {
            headers
                .iter()
                .position(|candidate| candidate == name)
                .ok_or_else(|| IntakeRefusal::StructureColumnAbsent {
                    origin: source_lineage.clone(),
                    column: name.to_owned(),
                })
        };
        let optional = |name: &str| headers.iter().position(|candidate| candidate == name);
        let atom_column = column("_atom_site.label_atom_id")?;
        let monomer_column = column("_atom_site.label_comp_id")?;
        let chain_column = column("_atom_site.label_asym_id")?;
        let residue_column = column("_atom_site.label_seq_id")?;
        let x_column = column("_atom_site.Cartn_x")?;
        let y_column = column("_atom_site.Cartn_y")?;
        let z_column = column("_atom_site.Cartn_z")?;
        let element_column = optional("_atom_site.type_symbol");
        let alternate_column = optional("_atom_site.label_alt_id");
        let entity_column = optional("_atom_site.label_entity_id");

        // `label_asym_id -> label_seq_id -> (monomer, atoms in file order)`. Both maps are ordered,
        // so chains are addressed by label and residues ascend by the source's own ordinal.
        type Chain = BTreeMap<i32, (String, Vec<AtomOccurrence>)>;
        let mut chains: BTreeMap<String, (Option<String>, Chain)> = BTreeMap::new();
        let mut maximum_decimal_places = 0_u32;
        let presented_rows = rows.len();
        for row in &rows {
            let source_ordinal = row[residue_column].parse::<i32>().map_err(|error| {
                refusal(format!(
                    "label_seq_id {:?} is not an integer: {error}",
                    row[residue_column]
                ))
            })?;
            let atom = AtomOccurrence {
                label: unquote(&row[atom_column]).to_owned(),
                element: element_column.map(|at| unquote(&row[at]).to_owned()),
                alternate: alternate_column.map(|at| unquote(&row[at]).to_owned()),
                x: DecimalToken::parse(&row[x_column])?,
                y: DecimalToken::parse(&row[y_column])?,
                z: DecimalToken::parse(&row[z_column])?,
            };
            maximum_decimal_places = maximum_decimal_places.max(atom.decimal_places());
            let chain_label = unquote(&row[chain_column]).to_owned();
            let entity = entity_column.map(|at| unquote(&row[at]).to_owned());
            let monomer = unquote(&row[monomer_column]).to_owned();
            let chain = chains.entry(chain_label).or_insert((entity, BTreeMap::new()));
            chain
                .1
                .entry(source_ordinal)
                .or_insert((monomer, Vec::new()))
                .1
                .push(atom);
        }

        let chains = chains
            .into_iter()
            .map(|(label_asym_id, (entity, residues))| {
                let residues = residues
                    .into_iter()
                    .map(|(source_ordinal, (monomer, atoms))| ResidueOccurrence {
                        source_ordinal,
                        monomer,
                        atoms,
                    })
                    .collect::<Vec<_>>();
                let atom_occurrences = residues.iter().map(|residue| residue.atoms.len()).sum();
                ChainOccurrence {
                    label_asym_id,
                    entity,
                    residues,
                    atom_occurrences,
                }
            })
            .collect::<Vec<_>>();
        let atom_occurrences = chains.iter().map(|chain| chain.atom_occurrences).sum();
        if atom_occurrences != presented_rows {
            return Err(refusal(format!(
                "{atom_occurrences} atoms were retained from {presented_rows} presented rows; \
                 all-atom intake retains every row"
            )));
        }
        Ok(Self {
            schema: "holonic-engine.all-atom-structure-presentation.v1".to_owned(),
            source_lineage,
            chains,
            atom_occurrences,
            presented_rows,
            maximum_decimal_places,
            coordinate_interval_law:
                "each written coordinate token is retained as its exact rational centre with one \
                 complete last-decimal unit outward on each side; a projection onto a declared \
                 resident denominator rounds strictly outward and therefore contains it. This is \
                 an exterior quantization aperture, not a claim about predictor error"
                    .to_owned(),
        })
    }

    /// The chain carrying a declared `label_asym_id`.
    pub fn chain(&self, label_asym_id: &str) -> Result<&ChainOccurrence, IntakeRefusal> {
        self.chains
            .iter()
            .find(|chain| chain.label_asym_id == label_asym_id)
            .ok_or_else(|| IntakeRefusal::ChainAbsent {
                origin: self.source_lineage.clone(),
                label: label_asym_id.to_owned(),
                present: self
                    .chains
                    .iter()
                    .map(|chain| chain.label_asym_id.clone())
                    .collect(),
            })
    }

    /// The unique chain carrying a declared residue count. Ambiguity is a refusal, never a first
    /// match: a component addressed by its size is only addressed when the size is unique.
    pub fn chain_with_residue_count(
        &self,
        residues: usize,
    ) -> Result<&ChainOccurrence, IntakeRefusal> {
        let matching = self
            .chains
            .iter()
            .filter(|chain| chain.residues.len() == residues)
            .collect::<Vec<_>>();
        match matching.as_slice() {
            [chain] => Ok(chain),
            other => Err(IntakeRefusal::ChainCountAmbiguous {
                origin: self.source_lineage.clone(),
                residues,
                matching: other.len(),
            }),
        }
    }
}

/// The `_atom_site` loop's headers and its rows, already tokenized and length-checked.
fn atom_site_loop(
    source_lineage: &str,
    text: &str,
) -> Result<(Vec<String>, Vec<Vec<String>>), IntakeRefusal> {
    let refusal = |detail: String| IntakeRefusal::MalformedStructure {
        origin: source_lineage.to_owned(),
        detail,
    };
    let lines = text.lines().collect::<Vec<_>>();
    let mut at = 0usize;
    while at < lines.len() {
        if lines[at].trim() != "loop_" {
            at += 1;
            continue;
        }
        let mut cursor = at + 1;
        let mut headers = Vec::<String>::new();
        while cursor < lines.len() && lines[cursor].trim_start().starts_with('_') {
            headers.push(lines[cursor].trim().to_owned());
            cursor += 1;
        }
        if !headers.iter().any(|name| name.starts_with("_atom_site.")) {
            at = cursor;
            continue;
        }
        let mut rows = Vec::<Vec<String>>::new();
        while cursor < lines.len() {
            let line = lines[cursor].trim();
            if line == "#" || line == "loop_" || line.starts_with('_') {
                break;
            }
            if line.starts_with(';') {
                return Err(refusal(format!(
                    "atom_site row {} opens a multi-line text field, which this intake does not \
                     admit",
                    cursor + 1
                )));
            }
            if !line.is_empty() {
                let fields = tokenize(line);
                if fields.len() != headers.len() {
                    return Err(refusal(format!(
                        "atom_site row {} has {} fields under {} headers",
                        cursor + 1,
                        fields.len(),
                        headers.len()
                    )));
                }
                rows.push(fields);
            }
            cursor += 1;
        }
        if rows.is_empty() {
            return Err(refusal("the atom_site loop carries no rows".to_owned()));
        }
        return Ok((headers, rows));
    }
    Err(refusal("no atom_site loop".to_owned()))
}

/// Split one CIF data line into fields, honouring single and double quoting.
fn tokenize(line: &str) -> Vec<String> {
    let mut fields = Vec::new();
    let mut current = String::new();
    let mut quote: Option<char> = None;
    let mut open = false;
    for ch in line.chars() {
        match quote {
            Some(mark) => {
                if ch == mark {
                    quote = None;
                } else {
                    current.push(ch);
                }
            }
            None => {
                if ch == '\'' || ch == '"' {
                    quote = Some(ch);
                    open = true;
                } else if ch.is_whitespace() {
                    if open || !current.is_empty() {
                        fields.push(std::mem::take(&mut current));
                        open = false;
                    }
                } else {
                    current.push(ch);
                }
            }
        }
    }
    if open || !current.is_empty() {
        fields.push(current);
    }
    fields
}

fn unquote(token: &str) -> &str {
    token
        .strip_prefix('\'')
        .and_then(|body| body.strip_suffix('\''))
        .or_else(|| {
            token
                .strip_prefix('"')
                .and_then(|body| body.strip_suffix('"'))
        })
        .unwrap_or(token)
}
