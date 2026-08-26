//! Shared receiver and Station-C artifact owner for the Phoenix tower.
//!
//! The codebook is an authenticated exterior chart.  This module never opens the foreign model
//! root or reparses its tokenizer; callers provide the W1 codebook rest (or its authenticated TSV
//! companion).  The receiver faces are exact rational potential sections, the plural candidate
//! population, the final normed standing, and the collapsed-population census.

use holonic_engine::foreign_codec_rest::ExteriorCodebookRest;
use holonic_engine::resident_section::{ResidentGrain, word_value};
use relational_geometry::Rat;

#[derive(Debug, Clone)]
pub struct FutureSection {
    pub position: usize,
    pub top_lower: Rat,
    pub plural: Vec<(usize, Rat, Rat)>,
    pub separated: usize,
}

/// A vocabulary display chart backed by the authenticated W1 codebook, never by the source root.
pub struct Vocabulary<'a> {
    codebook: &'a ExteriorCodebookRest,
}

impl<'a> Vocabulary<'a> {
    pub fn new(codebook: &'a ExteriorCodebookRest) -> Self {
        Self { codebook }
    }

    pub fn extent(&self) -> usize {
        self.codebook.vocabulary_extent as usize
    }

    pub fn surface(&self, id: usize) -> Result<String, String> {
        let piece = self
            .codebook
            .native_surface(id as u32)
            .map_err(|error| format!("native codebook surface {id}: {error}"))?;
        if let Some(hex) = piece
            .strip_prefix("<0x")
            .and_then(|rest| rest.strip_suffix('>'))
        {
            if let Ok(octet) = u8::from_str_radix(hex, 16) {
                return Ok(String::from_utf8_lossy(&[octet]).into_owned());
            }
        }
        Ok(piece.replace('\u{2581}', " "))
    }
}

pub fn future_section(
    potential: &[(i64, i64)],
    position: usize,
    vocabulary: &Vocabulary<'_>,
    grain: ResidentGrain,
    top: usize,
) -> Result<FutureSection, String> {
    let vocabulary_extent = vocabulary.extent();
    if vocabulary_extent == 0 {
        return Err("future receiver has zero vocabulary extent".to_owned());
    }
    let start = position
        .checked_mul(vocabulary_extent)
        .ok_or_else(|| "future receiver position overflow".to_owned())?;
    let end = start
        .checked_add(vocabulary_extent)
        .ok_or_else(|| "future receiver extent overflow".to_owned())?;
    let row = potential.get(start..end).ok_or_else(|| {
        format!("potential has no complete row {position} of width {vocabulary_extent}")
    })?;
    let mut top_lower = word_value(row[0].0, grain);
    for (lo, _) in row {
        let value = word_value(*lo, grain);
        if value > top_lower {
            top_lower = value;
        }
    }
    let mut plural: Vec<(usize, Rat, Rat)> = row
        .iter()
        .enumerate()
        .filter(|(_, (_, hi))| word_value(*hi, grain) >= top_lower)
        .map(|(vocabulary_id, (lo, hi))| {
            (
                vocabulary_id,
                word_value(*lo, grain),
                word_value(*hi, grain),
            )
        })
        .collect();
    plural.sort_by(|a, b| b.1.cmp(&a.1));
    let separated = vocabulary_extent - plural.len();
    plural.truncate(top.max(plural.len().min(top)));
    Ok(FutureSection {
        position,
        top_lower,
        plural,
        separated,
    })
}

#[derive(Debug, Clone)]
pub struct Committed {
    pub collapsed: String,
    pub future: String,
    pub candidates: Vec<String>,
    pub final_normed: Vec<(i64, i64)>,
    pub source_runtime_cross_chart: String,
}

pub fn read_committed(path: &str, tokens: &[usize]) -> Result<Committed, String> {
    let text = std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?;
    let wanted = format!("tokens {tokens:?} ");
    let input_header = text
        .lines()
        .find(|line| line.starts_with("input ") && line.contains(&wanted))
        .ok_or_else(|| format!("{path} carries no input with tokens {tokens:?}"))?;
    let quoted_prefix = input_header
        .strip_prefix("input ")
        .and_then(|header| header.split_once(" tokens ").map(|(quoted, _)| quoted))
        .ok_or_else(|| format!("{path} matching input header has no quoted-text prefix"))?;
    let mut lines = text.lines();
    if !lines.any(|line| line == input_header) {
        return Err(format!(
            "{path} matching input header could not be revisited"
        ));
    }
    let mut collapsed = String::new();
    let mut future = String::new();
    let mut candidates = Vec::new();
    let mut final_normed = Vec::new();
    let mut reading_final = false;
    for line in lines {
        if line.starts_with("input ") {
            break;
        }
        if let Some(rest) = line.strip_prefix("  collapsed population per layer ") {
            collapsed = rest.to_owned();
        } else if line.starts_with("  plural future section at position ") {
            future = line.to_owned();
        } else if !future.is_empty() && !reading_final && line.starts_with("    ") {
            candidates.push(line.to_owned());
        } else if line.starts_with("  final normed standing (") {
            reading_final = true;
        } else if reading_final && line.starts_with("    ") {
            let mut parts = line.split_whitespace();
            let _position = parts.next();
            let lower: i64 = parts
                .next()
                .ok_or("final normed lower")?
                .parse()
                .map_err(|_| "final normed lower")?;
            let upper: i64 = parts
                .next()
                .ok_or("final normed upper")?
                .parse()
                .map_err(|_| "final normed upper")?;
            final_normed.push((lower, upper));
        }
    }
    let source_runtime_cross_chart = text
        .lines()
        .position(|line| line == "source/runtime comparison:")
        .and_then(|section| {
            text.lines().skip(section + 1).find(|line| {
                let candidate = line.trim_start();
                candidate
                    .strip_prefix(quoted_prefix)
                    .is_some_and(|rest| rest.starts_with(':'))
            })
        })
        .ok_or_else(|| format!("{path} has no source/runtime comparison face for {quoted_prefix}"))?
        .to_owned();
    Ok(Committed {
        collapsed,
        future,
        candidates,
        final_normed,
        source_runtime_cross_chart,
    })
}

pub fn candidate_lines(
    future: &FutureSection,
    vocabulary: &Vocabulary<'_>,
) -> Result<Vec<String>, String> {
    future
        .plural
        .iter()
        .map(|(id, lo, hi)| {
            vocabulary
                .surface(*id)
                .map(|surface| format!("    {id} {:?} [{lo}, {hi}]", surface))
        })
        .collect()
}

#[derive(Debug, Clone)]
pub struct Comparison {
    pub future_line: String,
    pub candidates: Vec<String>,
    pub future_equal: bool,
    pub final_normed_equal: bool,
    pub collapsed_equal: bool,
    pub final_difference: Option<usize>,
    pub summary: String,
}

/// Compare all three committed receiver faces.  The full vectors remain in the caller's receipt;
/// this returned summary is only a compact receiver shadow for W2's receipt.
pub fn compare(
    committed: &Committed,
    future: &FutureSection,
    vocabulary: &Vocabulary<'_>,
    final_normed: &[(i64, i64)],
    collapsed: &str,
) -> Result<Comparison, String> {
    let future_line = format!(
        "  plural future section at position {}: top lower {} · {} not separated · {} separated",
        future.position,
        future.top_lower,
        future.plural.len(),
        future.separated
    );
    let candidates = candidate_lines(future, vocabulary)?;
    let final_difference = committed
        .final_normed
        .iter()
        .zip(final_normed)
        .position(|(left, right)| left != right);
    let final_normed_equal =
        committed.final_normed.len() == final_normed.len() && final_difference.is_none();
    let future_equal = future_line == committed.future && candidates == committed.candidates;
    let collapsed_equal = collapsed == committed.collapsed;
    let summary = format!(
        "future={} candidates={} final_normed={} collapsed={} final_lengths={} / {} first_difference={:?}",
        future_equal,
        candidates.len(),
        final_normed_equal,
        collapsed_equal,
        committed.final_normed.len(),
        final_normed.len(),
        final_difference
    );
    Ok(Comparison {
        future_line,
        candidates,
        future_equal,
        final_normed_equal,
        collapsed_equal,
        final_difference,
        summary,
    })
}
