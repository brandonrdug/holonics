//! Exterior M2 join: fixed source-moment counts, never the contemporary learned E.
//!
//! `ReceiptRatio::between(H,T)` owns each undivided (T:H); `Absorption::between`
//! owns its first separating coordinate. Phase lives in the region, terminal ring
//! windings remain explicit. No pending handle, target fibre or deposition is read.
//! Anchor::new must run on the actual release fork BEFORE its first draw.

use super::{Result, sections};
use holonics::compression::keys::duplex::{Absorption, ReceiverClass};
use holonics::hnn::SourceMoment;
use holonics::hnn::encoding::observed::PairedObservation;
use holonics::hnn::field::{Current, Field};
use holonics::ratio::Rat;
use holonics::receiver::receipt::{Comparison, Receipt, ReceiptRatio, RegionChart};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::collections::{BTreeMap, BTreeSet};

/// Frozen actual draw site; the admitted boundary only labels Encoded cells.
/// No multiplication through its injection/decoder occurs in this count receiver.
#[derive(Clone, Debug)]
pub(super) struct Anchor {
    field: Field,
    current: Current,
    boundary: PairedObservation,
}

impl Anchor {
    pub(super) fn new(
        field: &Field,
        current: &Current,
        boundary: &PairedObservation,
    ) -> Result<Self> {
        let current = Current::at(field, current.lift().to_vec())?;
        field.admit(&boundary.encode(&[])?)?;
        if !field.is_source(0) || !field.offsets().contains(&1) || !field.offsets().contains(&2) {
            return Err("M2 requires source ring 0 and its existing pair offsets 1 and 2".into());
        }
        for class in 0..field.alphabet() {
            if field.class_advance(0, class)? != 1 {
                return Err("M2's fixed source transport requires one ring-0 tick per cell".into());
            }
        }
        Ok(Self {
            field: field.clone(),
            current,
            boundary: boundary.clone(),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Region {
    Class {
        phase: usize,
        class: usize,
    },
    Pair {
        phase: usize,
        lag: usize,
        current: usize,
        previous: usize,
    },
}
impl Region {
    fn phase(&self) -> usize {
        match *self {
            Self::Class { phase, .. } | Self::Pair { phase, .. } => phase,
        }
    }
    fn local_order(&self) -> (usize, usize, usize, usize) {
        match *self {
            Self::Class { class, .. } => (0, 0, class, 0),
            Self::Pair {
                lag,
                current,
                previous,
                ..
            } => (1, lag, current, previous),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct TerminalLift {
    pub ring: usize,
    pub period: u64,
    pub absolute: BigInt,
    pub winding: BigInt,
    pub residue: BigInt,
}

struct Placed {
    counts: BTreeMap<Region, u64>,
    terminal: Vec<TerminalLift>,
    cells: usize,
    excluded: usize,
}

/// End letters are framing, not zero bytes; held decisions never enter classes.
/// An internal end is refused rather than cutting a sequence to suit its target.
fn chart_cells(classes: &[usize]) -> Result<&[usize]> {
    if classes.iter().any(|&class| class >= sections::CLASSES) {
        return Err("M2 chart class outside the declared alphabet".into());
    }
    let end = sections::end_cells();
    match classes.windows(end.len()).position(|pair| pair == end) {
        Some(at) if at + end.len() == classes.len() => Ok(&classes[..at]),
        Some(_) => Err("M2 refuses cells after an internal framing end".into()),
        None => Ok(classes),
    }
}

fn place(anchor: &Anchor, classes: &[usize]) -> Result<Placed> {
    let mut current = anchor.current.clone();
    let mut moment = SourceMoment::open(&anchor.field, &current);
    for &class in classes {
        // Actual SourceMoment law steps first, then bins the class and lags 1/2.
        // Single-cell ingest preserves every cell even across a joint carry-out.
        let cell = anchor.boundary.encode(&[class])?;
        let received = moment.ingest(&anchor.field, &mut current, &cell)?;
        if received.cells != 1 {
            return Err("M2 source transport failed to consume one cell".into());
        }
    }
    let period = usize::try_from(anchor.field.ring(0).period())?;
    let alphabet = anchor.field.alphabet();
    let mut counts = BTreeMap::new();
    for phase in 0..period {
        for (class, &count) in moment.phase_counts(0, phase)?.iter().enumerate() {
            if count != 0 {
                counts.insert(Region::Class { phase, class }, count);
            }
        }
        for lag in [1, 2] {
            for (index, &count) in moment.offset_counts(0, lag, phase)?.iter().enumerate() {
                if count != 0 {
                    counts.insert(
                        Region::Pair {
                            phase,
                            lag,
                            current: index / alphabet,
                            previous: index % alphabet,
                        },
                        count,
                    );
                }
            }
        }
    }
    let terminal = current
        .lift()
        .iter()
        .enumerate()
        .map(|(ring, absolute)| {
            let period = anchor.field.ring(ring).period();
            let divisor = BigInt::from(period);
            TerminalLift {
                ring,
                period,
                absolute: absolute.clone(),
                winding: absolute / &divisor,
                residue: absolute % &divisor,
            }
        })
        .collect();
    // SourceMoment's declared closed rotor count receiver has every phase bin.
    // Unlike learned Encoding::encode it has no Unreached column. Thus every
    // admitted occurrence here is reached; do not invent an E-dependent mask.
    Ok(Placed {
        counts,
        terminal,
        cells: classes.len(),
        excluded: 0,
    })
}

#[derive(Clone, Debug)]
pub(super) struct RegionReading {
    pub region: Region,
    pub comparison: Comparison,
    pub locked: bool,
    /// Integer ratio quotient/remainder only when the H count is nonzero.
    pub quotient_remainder: Option<(u64, u64)>,
}

#[derive(Clone, Debug)]
pub(super) struct Reading {
    pub anchored: bool,
    pub drawn_classes: usize,
    pub generated_cells: usize,
    pub target_cells: usize,
    pub generated_excluded: usize,
    pub target_excluded: usize,
    pub regions: Vec<RegionReading>,
    pub locks: usize,
    pub residuals: usize,
    pub target_only: usize,
    pub generated_only: usize,
    pub absorption: Option<Absorption>,
    pub generated_terminal: Vec<TerminalLift>,
    pub target_terminal: Vec<TerminalLift>,
    pub terminal_lifts_equal: Option<bool>,
}

fn between(
    anchor: &Anchor,
    generated: Placed,
    target: Placed,
    drawn_classes: usize,
) -> Result<Reading> {
    let period = usize::try_from(anchor.field.ring(0).period())?;
    let start = usize::try_from(anchor.current.phase(&anchor.field, 0)?)?;
    let mut support: Vec<_> = generated
        .counts
        .keys()
        .chain(target.counts.keys())
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    support.sort_by_key(|region| {
        (
            (region.phase() + period - start) % period,
            region.local_order(),
        )
    });
    let count_chart = RegionChart::new(Rat::one(), Rat::one(), 0)?;
    let make_receipt = |counts: &BTreeMap<Region, u64>| -> Result<Receipt> {
        let readings = support
            .iter()
            .map(|region| Rat::from_integer(BigInt::from(*counts.get(region).unwrap_or(&0))))
            .collect();
        Ok(Receipt::new(
            readings,
            vec![count_chart.clone(); support.len()],
        )?)
    };
    let h = make_receipt(&generated.counts)?;
    let t = make_receipt(&target.counts)?;
    let ratio = ReceiptRatio::between(&h, &t)?;
    // Owner bridge supplied by root: common scalar per receipt region. The zero
    // scalar winding here carries no ring geometry; all ring lifts stay below.
    let absorption = Absorption::between(
        &ReceiverClass::from_receipt(&t, 0),
        &ReceiverClass::from_receipt(&h, 0),
    );
    let mut regions = Vec::with_capacity(support.len());
    let (mut locks, mut residuals, mut target_only, mut generated_only) = (0, 0, 0, 0);
    for (region, comparison) in support.into_iter().zip(ratio.regions()) {
        let pair = comparison
            .presentation()
            .ok_or("M2 nonzero union support returned an undetermined ratio")?;
        let locked = pair.numerator() == pair.denominator() && !pair.numerator().is_zero();
        if locked {
            locks += 1;
        } else {
            residuals += 1;
            target_only += usize::from(pair.denominator().is_zero());
            generated_only += usize::from(pair.numerator().is_zero());
        }
        let hc = *generated.counts.get(&region).unwrap_or(&0);
        let tc = *target.counts.get(&region).unwrap_or(&0);
        regions.push(RegionReading {
            region,
            comparison: comparison.clone(),
            locked,
            quotient_remainder: (hc != 0).then(|| (tc / hc, tc % hc)),
        });
    }
    let first = regions.iter().position(|region| !region.locked);
    if absorption != first.map_or(Absorption::Absorbed, |at| Absorption::Residual { at }) {
        return Err(
            "M2 receipt-ratio and absorption owners disagree on their common coordinates".into(),
        );
    }
    let terminal_lifts_equal = Some(generated.terminal == target.terminal);
    Ok(Reading {
        anchored: true,
        drawn_classes,
        generated_cells: generated.cells,
        target_cells: target.cells,
        generated_excluded: generated.excluded,
        target_excluded: target.excluded,
        regions,
        locks,
        residuals,
        target_only,
        generated_only,
        absorption: Some(absorption),
        generated_terminal: generated.terminal,
        target_terminal: target.terminal,
        terminal_lifts_equal,
    })
}

/// Both sequences start at the ONE actual admitted draw anchor. No padding/cut,
/// target-derived phase, contemporary E projection, fibre, or live Resident mutation.
pub(super) fn compare(
    anchor: Option<&Anchor>,
    generated: &[usize],
    target: &[usize],
) -> Result<Reading> {
    let drawn_classes = generated.len();
    let generated = chart_cells(generated)?;
    let target = chart_cells(target)?;
    match anchor {
        Some(anchor) => between(
            anchor,
            place(anchor, generated)?,
            place(anchor, target)?,
            drawn_classes,
        ),
        None => Ok(Reading {
            anchored: false,
            drawn_classes,
            generated_cells: generated.len(),
            target_cells: target.len(),
            generated_excluded: generated.len(),
            target_excluded: target.len(),
            regions: Vec::new(),
            locks: 0,
            residuals: 0,
            target_only: 0,
            generated_only: 0,
            absorption: None,
            generated_terminal: Vec::new(),
            target_terminal: Vec::new(),
            terminal_lifts_equal: None,
        }),
    }
}

impl Reading {
    pub(super) fn line(&self, section: usize) -> String {
        format!(
            "observed_mutual section={section} anchored={} generated_cells={} target_cells={} excluded_h={} excluded_t={} locks={} residuals={} target_only={} generated_only={} absorption={:?} terminal_equal={:?} h_lifts={:?} t_lifts={:?} regions={:?}",
            self.anchored,
            self.generated_cells,
            self.target_cells,
            self.generated_excluded,
            self.target_excluded,
            self.locks,
            self.residuals,
            self.target_only,
            self.generated_only,
            self.absorption,
            self.terminal_lifts_equal,
            self.generated_terminal,
            self.target_terminal,
            self.regions
        )
    }
}

/// Eligibility is computed after all passes, over identical items in each chart.
#[derive(Default)]
pub(super) struct Book(BTreeMap<(sections::ChartKind, usize, usize), Reading>);
#[derive(Debug)]
pub(super) struct ChartTotals {
    pub chart: sections::ChartKind,
    pub eligible_items: Vec<usize>,
    pub locks_by_pass: Vec<usize>,
}
impl Book {
    pub(super) fn record(
        &mut self,
        chart: sections::ChartKind,
        item: usize,
        pass: usize,
        reading: Reading,
    ) -> Result<()> {
        if self.0.contains_key(&(chart, item, pass)) {
            return Err("duplicate M2 item/pass".into());
        }
        self.0.insert((chart, item, pass), reading);
        Ok(())
    }
    pub(super) fn totals(&self, passes: usize) -> Result<Vec<ChartTotals>> {
        if passes == 0 {
            return Err("M2 requires at least one declared pass".into());
        }
        let charts: BTreeSet<_> = self.0.keys().map(|&(chart, _, _)| chart).collect();
        let mut totals = Vec::new();
        for chart in charts {
            let items: BTreeSet<_> = self
                .0
                .keys()
                .filter(|&&(c, _, _)| c == chart)
                .map(|&(_, item, _)| item)
                .collect();
            let eligible_items: Vec<_> = items
                .into_iter()
                .filter(|&item| {
                    (0..passes).all(|pass| {
                        self.0
                            .get(&(chart, item, pass))
                            .is_some_and(|reading| reading.drawn_classes != 0)
                    })
                })
                .collect();
            let mut locks_by_pass = vec![0usize; passes];
            for &item in &eligible_items {
                for (pass, total) in locks_by_pass.iter_mut().enumerate() {
                    *total = total
                        .checked_add(self.0[&(chart, item, pass)].locks)
                        .ok_or("M2 lock sum overflow")?;
                }
            }
            totals.push(ChartTotals {
                chart,
                eligible_items,
                locks_by_pass,
            });
        }
        Ok(totals)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn anchor() -> Anchor {
        let port = super::super::Reference::new(4, super::super::BUDGET);
        let (resident, pairing) = super::super::mounted(&port, 65536).unwrap();
        let boundary =
            PairedObservation::admit(resident.field(), resident.constitution(), &pairing).unwrap();
        Anchor::new(resident.field(), resident.current(), &boundary).unwrap()
    }
    #[test]
    fn empty_and_missing_anchor_lock_nothing() {
        let a = anchor();
        let both_empty = compare(Some(&a), &[], &[]).unwrap();
        assert_eq!(both_empty.locks, 0);
        assert!(both_empty.regions.is_empty());
        let empty = compare(Some(&a), &[], &[1]).unwrap();
        assert_eq!(empty.locks, 0);
        assert_eq!(empty.target_only, 1);
        let absent = compare(None, &[1], &[1]).unwrap();
        assert_eq!(absent.locks, 0);
        assert!(absent.regions.is_empty());
        assert_eq!(absent.absorption, None);
        assert_eq!((absent.generated_excluded, absent.target_excluded), (1, 1));
    }
    #[test]
    fn equal_sequences_lock_the_whole_nonzero_support() {
        let a = anchor();
        let r = compare(Some(&a), &[1, 2, 3, 0, 0], &[1, 2, 3, 0, 0]).unwrap();
        assert_eq!(r.generated_cells, 3);
        assert_eq!(r.locks, r.regions.len());
        assert_eq!(r.locks, 6);
        assert_eq!(r.absorption, Some(Absorption::Absorbed));
        assert_eq!(r.terminal_lifts_equal, Some(true));
    }
    #[test]
    fn one_cell_phase_shift_separates_two_regions() {
        let a = anchor();
        let mut shifted = a.clone();
        let one = shifted.boundary.encode(&[1]).unwrap();
        shifted.current.step(&shifted.field, &one, 0).unwrap();
        let r = between(
            &a,
            place(&a, &[2]).unwrap(),
            place(&shifted, &[2]).unwrap(),
            1,
        )
        .unwrap();
        assert_eq!(r.locks, 0);
        assert_eq!(r.residuals, 2);
        assert_eq!((r.target_only, r.generated_only), (1, 1));
        assert!(matches!(r.absorption, Some(Absorption::Residual { .. })));
    }
    #[test]
    fn unequal_lengths_keep_one_sided_support_and_terminal_lifts() {
        let a = anchor();
        let period = usize::try_from(a.field.ring(0).period()).unwrap();
        let r = compare(Some(&a), &[1], &vec![1; period + 1]).unwrap();
        assert_eq!((r.generated_cells, r.target_cells), (1, period + 1));
        assert!(r.target_only > 0);
        assert_eq!(r.generated_only, 0);
        assert_eq!(r.terminal_lifts_equal, Some(false));
        for lift in r.generated_terminal.iter().chain(&r.target_terminal) {
            assert_eq!(
                &lift.winding * BigInt::from(lift.period) + &lift.residue,
                lift.absolute
            );
        }
    }
    #[test]
    fn totals_use_identical_items_that_drew_in_every_pass() {
        let a = anchor();
        let mut book = Book::default();
        for pass in 0..3 {
            book.record(
                sections::ChartKind::Octets,
                0,
                pass,
                compare(Some(&a), if pass == 0 { &[] } else { &[1] }, &[1]).unwrap(),
            )
            .unwrap();
            book.record(
                sections::ChartKind::Octets,
                1,
                pass,
                compare(Some(&a), &[1], &[1]).unwrap(),
            )
            .unwrap();
        }
        let totals = book.totals(3).unwrap();
        assert_eq!(totals.len(), 1);
        assert_eq!(totals[0].eligible_items, vec![1]);
        assert_eq!(totals[0].locks_by_pass, vec![1, 1, 1]);
    }
}
