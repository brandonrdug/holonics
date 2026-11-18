//! **The boundary chart** (`Codec`): a passage's units read as the classes a region's sites carry, and back. Moved from the store line's
//! harness (`complete_language/field_train.rs`) by C4 of the consolidation (#603), each item's text as it stood but for its visibility.
//!
//! [definition; Brandon, November 12] The table of classes stands until the symbol's word replaces it: a symbol is its key on a few coprime
//! rings, located by the machine, never a class index with free rows (CLAUDE.md, Method, "A symbol is a word"). Its replacement is a law
//! build of the engine's line (THE_CONSOLIDATION §11), not a move.

use crate::units::Units;
use std::collections::HashMap;

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

pub fn count(s: &str) -> Result<usize> {
    Ok(s.parse::<usize>()?)
}

/// The GSM8K boundary codec: the founded units, the units the passage uses (each one class, in
/// unit order) and the answer's longest extent in classes.
///
/// [definition; theory, November 12 (the record of the opening's room, §4 item 4)] **The void at a kept index**
/// (`field-codec-v3`): a codec founded on one passage holds the void as its last class (`field-codec-v2`, read and written
/// as before); extended at a crossing to a store ([`Codec::extended`]) it keeps every class where it stood, the void
/// among them, and takes the fresh units after them, so `used` lists the units in class order with the void's index
/// skipped. Decoding stops at the void by equality.
pub struct Codec {
    units: Units,
    used: Vec<u32>,
    class_of_unit: HashMap<u32, usize>,
    /// The longest training answer in classes, plus its void: the answer sites a release opens.
    pub answer: usize,
    /// The void's class: `used.len()` (the last) on a `field-codec-v2`, kept where it stood on a `field-codec-v3`.
    void: usize,
    /// Whether the codec is written as `field-codec-v3` (its void at a kept index).
    kept_void: bool,
}

impl Codec {
    /// The codec of a training passage's problems.
    pub fn found(units: Units, problems: &[(Vec<u8>, Vec<u8>)]) -> Result<Self> {
        let mut used: Vec<u32> = Vec::new();
        for (q, a) in problems {
            used.extend(units.parse(&question_text(q)).map_err(|e| e.to_string())?);
            used.extend(units.parse(a).map_err(|e| e.to_string())?);
        }
        used.sort_unstable();
        used.dedup();
        let void = used.len();
        let mut codec = Self::with(units, used, 0, void, false);
        codec.answer = problems.iter().map(|(_, a)| codec.encode(a).map(|c| c.len())).collect::<Result<Vec<_>>>()?.into_iter().max().unwrap_or(0) + 1;
        Ok(codec)
    }

    fn with(units: Units, used: Vec<u32>, answer: usize, void: usize, kept_void: bool) -> Self {
        let class_of_unit = used.iter().enumerate().map(|(i, &u)| (u, if i < void { i } else { i + 1 })).collect();
        Self { units, used, class_of_unit, answer, void, kept_void }
    }

    /// [definition; theory, November 12] **The codec extended by fresh units** at a crossing (`field-codec-v3`): every class keeps its
    /// index, the void its own, and the fresh units take the classes after the last, in the order given. A unit the codec holds is refused.
    pub fn extended(&self, fresh: &[u32]) -> Result<Self> {
        if let Some(u) = fresh.iter().find(|u| self.class_of_unit.contains_key(u)) {
            return Err(format!("unit {u} is already in the codec").into());
        }
        if fresh.iter().any(|&u| u as usize >= self.units.len()) {
            return Err("a fresh unit outside the units".into());
        }
        let mut used = self.used.clone();
        used.extend_from_slice(fresh);
        Ok(Self::with(self.units.clone(), used, self.answer, self.void, true))
    }

    /// The void class: the last on a codec founded on one passage, kept where it stood on an extended one.
    pub fn void(&self) -> usize {
        self.void
    }

    pub fn alphabet(&self) -> usize {
        self.used.len() + 1
    }

    /// A class's unit (none for the void).
    fn unit_of(&self, class: usize) -> Option<u32> {
        match class.cmp(&self.void) {
            std::cmp::Ordering::Less => self.used.get(class).copied(),
            std::cmp::Ordering::Equal => None,
            std::cmp::Ordering::Greater => self.used.get(class - 1).copied(),
        }
    }

    /// A text's classes; a unit the training passage never used is refused.
    pub fn encode(&self, text: &[u8]) -> Result<Vec<usize>> {
        self.units.parse(text).map_err(|e| e.to_string())?.into_iter().map(|u| self.class_of_unit.get(&u).copied().ok_or_else(|| format!("unit {u} is not in the codec").into())).collect()
    }

    /// Classes back to bytes, up to the first void.
    pub fn decode(&self, classes: &[usize]) -> Vec<u8> {
        let mut out = Vec::new();
        for &c in classes.iter().take_while(|&&c| c != self.void) {
            if let Some(u) = self.unit_of(c) {
                out.extend_from_slice(self.units.piece(u as usize));
            }
        }
        out
    }

    /// The codec as text: its head line, then the used units on one line (`field-codec-v2 ANSWER`, or `field-codec-v3 ANSWER VOID`).
    pub fn to_text(&self) -> String {
        let used: Vec<String> = self.used.iter().map(u32::to_string).collect();
        if self.kept_void {
            return format!("field-codec-v3 {} {}\n{}\n", self.answer, self.void, used.join(" "));
        }
        format!("field-codec-v2 {}\n{}\n", self.answer, used.join(" "))
    }

    pub fn from_text(text: &str, units: Units) -> Result<Self> {
        let mut lines = text.lines();
        let head: Vec<&str> = lines.next().unwrap_or("").split(' ').collect();
        let (answer, void) = match (head.first().copied(), head.len()) {
            (Some("field-codec-v2"), 2) => (count(head[1])?, None),
            (Some("field-codec-v3"), 3) => (count(head[1])?, Some(count(head[2])?)),
            _ => return Err("a codec that is not field-codec-v2 or field-codec-v3".into()),
        };
        let used = lines.next().unwrap_or("").split(' ').map(|w| w.parse::<u32>()).collect::<std::result::Result<Vec<_>, _>>()?;
        if used.iter().any(|&u| u as usize >= units.len()) {
            return Err("a codec's unit outside the units".into());
        }
        let mut seen = used.clone();
        seen.sort_unstable();
        seen.dedup();
        if seen.len() != used.len() {
            return Err("a codec that holds a unit twice".into());
        }
        match void {
            None => {
                let void = used.len();
                Ok(Self::with(units, used, answer, void, false))
            }
            Some(v) if v <= used.len() => Ok(Self::with(units, used, answer, v, true)),
            Some(_) => Err("a codec's void past its classes".into()),
        }
    }
}

/// A problem's question as its region opens it: the question, then the line it ends on.
pub fn question_text(q: &[u8]) -> Vec<u8> {
    let mut out = q.to_vec();
    out.push(b'\n');
    out
}

/// The record separator and the unit separator of a passage of records (ASCII `RS` and `US`).
pub const RECORD: u8 = 0x1E;

pub const UNIT: u8 = 0x1F;
