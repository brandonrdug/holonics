//! Exterior J2 reader of explicitly supplied historical class strands (Refs #62 #73).
//!
//! Usage: `cargo run -p holonics --example solenoidal_coupling -- INPUT.tsv`
//! Each line is `label<TAB>heard_csv<TAB>target_csv`, without a header. An empty CSV
//! is an empty strand. Classes are decimal integers in `0..32`; surrounding CSV-cell
//! whitespace is accepted. Supply whole class strands when available: the existing
//! `coupling32` owner excludes only the trailing `[0,0]` framing end and refuses an
//! internal end. In particular `[0,16]` is a zero octet, not an end letter.
//!
//! Output is TSV containing exact lambda/F_star, all plural-contact/plateau and
//! unresolved totals, plus every maximal contiguous plateau `(i,j,length,first_rank)`.
//! The union of optimal contacts is plural and may contain crossing alternatives.
//! Historical logs carry no explicit current/key phase anchor. This executable reports
//! only the native ordered-contact reader's lambda/F_star; it infers no absolute phase,
//! Lock difference or Own-ring lag. It neither mounts nor trains a predictor.

use holonics::receiver::coupling::{CouplingRefusal, FramedCoupling, Strand, coupling32};
use std::collections::BTreeSet;
use std::error::Error;
use std::io::Write;
use thiserror::Error;

const USAGE: &str = "usage: solenoidal_coupling INPUT.tsv\n\
Each input line: label<TAB>heard_csv<TAB>target_csv (no header; empty CSV is empty).\n\
Classes must be in 0..32. Whole strands retain their trailing 0,0 framing end.\n\
Reports native lambda/F_star and plural contacts only; no historical absolute phase anchor is inferred.";

const HEADER: &str = "label\tlambda\tF_star\th_cells\tt_cells\th_framing_end\tt_framing_end\tplural_contacts\tcontact_plateaus\tplateau_contacts\tunresolved_h_per_optimum\tunresolved_t_per_optimum\tnever_held_h\tnever_held_t\tmay_be_unresolved_h\tmay_be_unresolved_t\talways_held_h\talways_held_t\tnonempty_zero_friction\tplateaus_i_j_length_first_rank";

#[derive(Debug, Error)]
enum InputError {
    #[error("input is empty")]
    Empty,
    #[error("line {line}: {reason}")]
    Format { line: usize, reason: &'static str },
    #[error("line {line}: {strand:?} CSV cell {index} is not a decimal class")]
    Decimal {
        line: usize,
        strand: Strand,
        index: usize,
    },
    #[error("line {line}: {reason}")]
    Coupling {
        line: usize,
        #[source]
        reason: CouplingRefusal,
    },
}

struct Reading {
    label: String,
    framed: FramedCoupling,
}

fn classes(csv: &str, line: usize, strand: Strand) -> Result<Vec<usize>, InputError> {
    if csv.is_empty() {
        return Ok(Vec::new());
    }
    csv.split(',')
        .enumerate()
        .map(|(index, value)| {
            let value = value.trim();
            let refuse = || InputError::Decimal {
                line,
                strand,
                index,
            };
            if value.is_empty() || !value.bytes().all(|b| b.is_ascii_digit()) {
                return Err(refuse());
            }
            value.parse().map_err(|_| refuse())
        })
        .collect()
}

/// Validate every row before producing any report, so a refused row cannot look like a
/// successful shorter read. Input strands are consumed only by the existing J2 owner.
fn read(input: &str) -> Result<Vec<Reading>, InputError> {
    let mut labels = BTreeSet::new();
    let mut readings = Vec::new();
    for (index, row) in input.lines().enumerate() {
        let line = index + 1;
        let mut columns = row.split('\t');
        let label = columns.next().unwrap_or("");
        let h = columns.next();
        let t = columns.next();
        if label.trim().is_empty()
            || label.chars().any(char::is_control)
            || h.is_none()
            || t.is_none()
            || columns.next().is_some()
        {
            return Err(InputError::Format {
                line,
                reason: "expected a nonempty label and exactly two CSV columns",
            });
        }
        if !labels.insert(label.to_owned()) {
            return Err(InputError::Format {
                line,
                reason: "duplicate label",
            });
        }
        let h = classes(
            h.expect("the three-column shape was checked"),
            line,
            Strand::H,
        )?;
        let t = classes(
            t.expect("the three-column shape was checked"),
            line,
            Strand::T,
        )?;
        let framed = coupling32(&h, &t).map_err(|reason| InputError::Coupling { line, reason })?;
        readings.push(Reading {
            label: label.to_owned(),
            framed,
        });
    }
    if readings.is_empty() {
        return Err(InputError::Empty);
    }
    Ok(readings)
}

impl Reading {
    fn line(&self) -> String {
        let q = &self.framed.coupling;
        let plateaus = q
            .maximal_contiguous_plateaus
            .iter()
            .map(|p| format!("{}:{}:{}:{}", p.h_start, p.t_start, p.length, p.first_rank))
            .collect::<Vec<_>>()
            .join(";");
        let plateau_contacts: usize = q.maximal_contiguous_plateaus.iter().map(|p| p.length).sum();
        format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            self.label,
            q.lambda,
            q.least_friction,
            q.h_cells,
            q.t_cells,
            self.framed.h_framing_end_present,
            self.framed.t_framing_end_present,
            q.plural_optimal_contacts.len(),
            q.maximal_contiguous_plateaus.len(),
            plateau_contacts,
            q.unresolved_h_per_optimum,
            q.unresolved_t_per_optimum,
            q.never_held_h_indices.len(),
            q.never_held_t_indices.len(),
            q.may_be_unresolved_h_indices.len(),
            q.may_be_unresolved_t_indices.len(),
            q.always_held_h_indices.len(),
            q.always_held_t_indices.len(),
            q.nonempty_zero_friction,
            if plateaus.is_empty() { "-" } else { &plateaus },
        )
    }
}

#[allow(
    clippy::disallowed_methods,
    reason = "this exterior reader reads the user-supplied historical class TSV only"
)]
fn main() -> Result<(), Box<dyn Error>> {
    let arguments: Vec<_> = std::env::args().skip(1).collect();
    if arguments.as_slice() == ["--help"] || arguments.as_slice() == ["-h"] {
        println!("{USAGE}");
        return Ok(());
    }
    if arguments.len() != 1 {
        return Err(USAGE.into());
    }
    let input = std::fs::read_to_string(&arguments[0])?;
    let readings = read(&input)?;
    let mut output = String::from(HEADER);
    output.push('\n');
    for reading in readings {
        output.push_str(&reading.line());
        output.push('\n');
    }
    std::io::stdout().lock().write_all(output.as_bytes())?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn whole_strands_preserve_zero_octet_and_exclude_only_terminal_framing() {
        let rows = read("zero\t0,16,0,0\t0,16,0,0\r\nempty\t\t\n").unwrap();
        let q = &rows[0].framed.coupling;
        assert_eq!((q.lambda, q.least_friction), (2, 0));
        assert!(rows[0].framed.h_framing_end_present);
        assert!(rows[0].framed.t_framing_end_present);
        assert_eq!((q.h_cells, q.t_cells), (2, 2));
        assert_eq!(rows[1].framed.coupling.lambda, 0);
        assert!(!rows[1].framed.coupling.nonempty_zero_friction);
        assert_eq!(
            rows[0].line().split('\t').count(),
            HEADER.split('\t').count()
        );
        assert!(rows[0].line().ends_with("0:0:2:1"));
    }

    #[test]
    fn crossing_alternatives_remain_plural_and_unresolved_totals_are_not_a_chosen_match() {
        let rows = read("cross\t1, 2\t2,1\n").unwrap();
        let q = &rows[0].framed.coupling;
        assert_eq!((q.lambda, q.least_friction), (1, 2));
        assert_eq!(q.plural_optimal_contacts.len(), 2);
        assert_eq!(q.maximal_contiguous_plateaus.len(), 2);
        assert_eq!(q.unresolved_h_per_optimum, 1);
        assert_eq!(q.may_be_unresolved_h_indices.len(), 2);
        assert!(rows[0].line().ends_with("0:1:1:1;1:0:1:1"));
    }

    #[test]
    fn malformed_decimal_shape_duplicate_and_framing_are_refused() {
        assert!(matches!(read(""), Err(InputError::Empty)));
        for text in [
            "label\t1",
            "\t1\t1",
            "label\t1\t1\textra",
            "a\t1\t1\na\t2\t2",
        ] {
            assert!(matches!(read(text), Err(InputError::Format { .. })));
        }
        for csv in ["1,,2", "1,", "-1", "+1", "x", " "] {
            assert!(matches!(
                read(&format!("bad\t{csv}\t1")),
                Err(InputError::Decimal {
                    strand: Strand::H,
                    ..
                })
            ));
        }
        assert!(matches!(
            read("bad\t32\t1"),
            Err(InputError::Coupling {
                reason: CouplingRefusal::Class {
                    strand: Strand::H,
                    ..
                },
                ..
            })
        ));
        assert!(matches!(
            read("bad\t1\t0,0,1"),
            Err(InputError::Coupling {
                reason: CouplingRefusal::InternalEnd {
                    strand: Strand::T,
                    ..
                },
                ..
            })
        ));
    }
}
