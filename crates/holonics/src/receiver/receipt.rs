//! **Receipts and the receipt ratio: readings in their own frames and clocks, compared after their
//! common transport.**
//!
//! [definition] A receipt is a field of readings over a partition into regions, each region's
//! reading carried in its own frame and clock ([§10](../../../../docs/ELEMENTARY_OBJECTS.md#10-receipt)).
//! A region's [`RegionChart`] holds the units that transport its reading into the declared common
//! frame and common clock: the frame unit multiplies, and a clock that runs `c` times the common
//! clock divides the reading by `c^k`, where `k` is the reading's clock exponent — `1` for a rate,
//! `0` for a count or a phase, which a change of clock leaves fixed (§10's measurement
//! conventions: under `t' = at + b` a rate becomes `r/a`).
//!
//! [definition] **The receipt ratio** ([`ReceiptRatio::between`], the contract's
//! `Ratio::between`) compares two receipts region by region *after* their common transport and
//! keeps each comparison as the undivided pair `(b : a)`, "`b` per `a`". A region where both
//! transported readings vanish returns [`Comparison::Undetermined`]: the pair `(0 : 0)` is not an
//! admitted ratio (Lean `Aeon/Clock/Reading.Admitted`), and it is typed rather than carried as
//! one. Composition is the ratio's own ([`crate::ratio::Presentation::follow`]).
//!
//! | Lean `Holarchy/Receipt` | Rust |
//! |---|---|
//! | `Receipt`, `Receipt.clockExponent`, `Receipt.common`, `Receipt.common_reclock`, `ReceiptLaw.receive` | [`Receipt`], [`RegionChart::common`], [`ReceiptLaw::receive`] |
//! | `between`, `between_operands` | [`ReceiptRatio::between`] |
//! | `between_reframe`, `between_reframe_projectivelyEq`, `between_reclock`, `between_reclock_projectivelyEq`, `between_reclock_count` | [`Receipt::reframe`], [`Receipt::reclock`] |
//! | `followRatio_eq`, `between_comp`, `between_comp_projectivelyEq`, `between_comp_through_zero` | [`ReceiptRatio::follow`] |
//! | `raw_comparison_is_frame_dependent`, `rate_against_count_is_clock_dependent` | tests, the clock-exponent refusal |
//!
//! [open] Rust refuses to compare two readings of different clock exponents, which Lean returns
//! and shows clock-dependent (`rate_against_count_is_clock_dependent`). Frames are scalar units:
//! the gauge chart (`GaugeReceipt`, `betweenGauge_reframe`, `betweenGauge_comp`) and the log chart
//! (`between_log_comp`, `between_log_winding`) have no Rust consumer here. As in Lean, a receipt's
//! source, receiver, locus, grain, variability over ticks and interface flux are carried by the
//! interaction return and the view, not by the receipt; joining them into one receipt is owed in
//! #62.

use num_traits::{One, Zero};

use crate::holon::HolonError;
use crate::ratio::linear::vector::dot;
use crate::ratio::{Presentation, Rat};

/// [definition] **A region's chart**: the frame unit, the clock unit and the reading's clock
/// exponent. Both units are nonzero, so the transport is always invertible.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegionChart {
    frame: Rat,
    clock: Rat,
    clock_exponent: i32,
}

impl RegionChart {
    /// Refuses a zero frame or clock: neither is a unit of ℚ.
    pub fn new(frame: Rat, clock: Rat, clock_exponent: i32) -> Result<Self, HolonError> {
        if frame.is_zero() {
            return Err(HolonError::Singular {
                what: "a region's frame unit",
            });
        }
        if clock.is_zero() {
            return Err(HolonError::Singular {
                what: "a region's clock unit",
            });
        }
        Ok(Self {
            frame,
            clock,
            clock_exponent,
        })
    }

    /// The common unit chart: frame and clock `1`, rate exponent `1`.
    pub fn rate() -> Self {
        Self {
            frame: Rat::one(),
            clock: Rat::one(),
            clock_exponent: 1,
        }
    }

    pub fn frame(&self) -> &Rat {
        &self.frame
    }

    pub fn clock(&self) -> &Rat {
        &self.clock
    }

    pub fn clock_exponent(&self) -> i32 {
        self.clock_exponent
    }

    /// [definition] **A reading transported into the common frame and clock** (Lean
    /// `Holarchy/Receipt.Receipt.common`): `frame · reading · clock^(−k)`.
    pub fn common(&self, reading: &Rat) -> Rat {
        &self.frame * reading * self.clock.pow(-self.clock_exponent)
    }
}

/// [definition] **A receipt**: one reading per region, each with its region's chart.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Receipt {
    readings: Vec<Rat>,
    charts: Vec<RegionChart>,
}

impl Receipt {
    pub fn new(readings: Vec<Rat>, charts: Vec<RegionChart>) -> Result<Self, HolonError> {
        if readings.len() != charts.len() {
            return Err(HolonError::Shape {
                what: "receipt charts (one per region)",
                expected: readings.len(),
                found: charts.len(),
            });
        }
        Ok(Self { readings, charts })
    }

    pub fn regions(&self) -> usize {
        self.readings.len()
    }

    pub fn readings(&self) -> &[Rat] {
        &self.readings
    }

    pub fn charts(&self) -> &[RegionChart] {
        &self.charts
    }

    /// Region `r`'s reading in the common frame and clock.
    pub fn common(&self, region: usize) -> Option<Rat> {
        Some(self.charts.get(region)?.common(&self.readings[region]))
    }

    fn units(&self, units: &[Rat]) -> Result<(), HolonError> {
        if units.len() != self.regions() {
            return Err(HolonError::Shape {
                what: "one unit per region",
                expected: self.regions(),
                found: units.len(),
            });
        }
        if units.iter().any(Zero::is_zero) {
            return Err(HolonError::Singular {
                what: "a change of frame or clock",
            });
        }
        Ok(())
    }

    /// [definition] **A common change of frame** (Lean `Receipt.reframe`): each region's frame
    /// composed with `units[r]`; its common reading scales by that unit
    /// (`Receipt.common_reframe`).
    pub fn reframe(&self, units: &[Rat]) -> Result<Self, HolonError> {
        self.units(units)?;
        let charts = self
            .charts
            .iter()
            .zip(units)
            .map(|(chart, unit)| RegionChart {
                frame: unit * &chart.frame,
                ..chart.clone()
            })
            .collect();
        Ok(Self {
            readings: self.readings.clone(),
            charts,
        })
    }

    /// [definition] **A common change of clock** (Lean `Receipt.reclock`): each region's clock
    /// composed with `units[r]`; its common reading scales by `units[r]^(−k)`
    /// (`Receipt.common_reclock`).
    pub fn reclock(&self, units: &[Rat]) -> Result<Self, HolonError> {
        self.units(units)?;
        let charts = self
            .charts
            .iter()
            .zip(units)
            .map(|(chart, unit)| RegionChart {
                clock: unit * &chart.clock,
                ..chart.clone()
            })
            .collect();
        Ok(Self {
            readings: self.readings.clone(),
            charts,
        })
    }
}

/// [definition] **A receipt law** (Lean `ReceiptLaw`): how a participant's state is read, region by
/// region — a covector per region with its chart.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiptLaw {
    readers: Vec<Vec<Rat>>,
    charts: Vec<RegionChart>,
    extent: usize,
}

impl ReceiptLaw {
    /// A law on states of `extent` coordinates; every reader has that length.
    pub fn new(
        extent: usize,
        readers: Vec<Vec<Rat>>,
        charts: Vec<RegionChart>,
    ) -> Result<Self, HolonError> {
        if readers.len() != charts.len() {
            return Err(HolonError::Shape {
                what: "receipt-law charts (one per region)",
                expected: readers.len(),
                found: charts.len(),
            });
        }
        if let Some(bad) = readers.iter().find(|reader| reader.len() != extent) {
            return Err(HolonError::Shape {
                what: "region reader",
                expected: extent,
                found: bad.len(),
            });
        }
        Ok(Self {
            readers,
            charts,
            extent,
        })
    }

    pub fn extent(&self) -> usize {
        self.extent
    }

    /// The receipt this law returns on a state (Lean `ReceiptLaw.receive`).
    pub fn receive(&self, state: &[Rat]) -> Result<Receipt, HolonError> {
        if state.len() != self.extent {
            return Err(HolonError::Shape {
                what: "received state",
                expected: self.extent,
                found: state.len(),
            });
        }
        Receipt::new(
            self.readers
                .iter()
                .map(|reader| dot(reader, state))
                .collect(),
            self.charts.clone(),
        )
    }
}

/// [definition] **One region's comparison**: the undivided pair `(b : a)` of the two transported
/// readings, or undetermined when both vanish.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Comparison {
    Determined(Presentation),
    /// Both transported readings vanish: `(0 : 0)` names no ratio.
    Undetermined,
}

impl Comparison {
    fn of(pair: Presentation) -> Self {
        if pair.is_degenerate() {
            Self::Undetermined
        } else {
            Self::Determined(pair)
        }
    }

    pub fn presentation(&self) -> Option<&Presentation> {
        match self {
            Self::Determined(pair) => Some(pair),
            Self::Undetermined => None,
        }
    }
}

/// [definition] **The receipt ratio**: one [`Comparison`] per region.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiptRatio {
    regions: Vec<Comparison>,
}

impl ReceiptRatio {
    /// [definition] **`Ratio::between(a, b)`** (Lean `Holarchy/Receipt.between`): in each region,
    /// `b` per `a`, both transported into the common frame and clock and kept as the undivided
    /// pair; refused when the receipts cover different regions or a region's two readings have
    /// different clock exponents.
    pub fn between(a: &Receipt, b: &Receipt) -> Result<Self, HolonError> {
        if a.regions() != b.regions() {
            return Err(HolonError::Shape {
                what: "compared receipt regions",
                expected: a.regions(),
                found: b.regions(),
            });
        }
        let mut regions = Vec::with_capacity(a.regions());
        for r in 0..a.regions() {
            if a.charts[r].clock_exponent != b.charts[r].clock_exponent {
                return Err(HolonError::UnitsMismatch);
            }
            regions.push(Comparison::of(Presentation::new(
                b.charts[r].common(&b.readings[r]),
                a.charts[r].common(&a.readings[r]),
            )));
        }
        Ok(Self { regions })
    }

    pub fn regions(&self) -> &[Comparison] {
        &self.regions
    }

    /// [definition] **The ratio's own composition, region by region** (Lean
    /// `Holarchy/Receipt.followRatio`): `between a b` followed by `between b c` is exactly
    /// `between a c` scaled by `b`'s common reading (`between_comp`); an undetermined region stays
    /// undetermined, and a composite pair whose entries both vanish is undetermined, never read as
    /// a ratio (`between_comp_through_zero`).
    pub fn follow(&self, next: &Self) -> Result<Self, HolonError> {
        if self.regions.len() != next.regions.len() {
            return Err(HolonError::Shape {
                what: "followed ratio regions",
                expected: self.regions.len(),
                found: next.regions.len(),
            });
        }
        Ok(Self {
            regions: self
                .regions
                .iter()
                .zip(&next.regions)
                .map(|pair| match pair {
                    (Comparison::Determined(p), Comparison::Determined(q)) => {
                        Comparison::of(p.follow(q))
                    }
                    _ => Comparison::Undetermined,
                })
                .collect(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::{integer, rat};

    fn chart(frame: Rat, clock: Rat) -> RegionChart {
        RegionChart::new(frame, clock, 1).unwrap()
    }

    fn receipt(readings: &[Rat], charts: &[RegionChart]) -> Receipt {
        Receipt::new(readings.to_vec(), charts.to_vec()).unwrap()
    }

    fn pair(ratio: &ReceiptRatio, region: usize) -> &Presentation {
        ratio.regions()[region].presentation().unwrap()
    }

    /// `Holarchy/Receipt.between_reframe_projectivelyEq`, `between_reclock_projectivelyEq`: a
    /// common change of frame scales each region's pair by that region's unit, and a common change
    /// of clock by the unit's `−k`-th power; the comparison is projectively unchanged.
    #[test]
    fn between_is_invariant_under_a_common_change_of_frame_and_clock() {
        let charts = [chart(integer(2), integer(3)), chart(rat(1, 5), integer(-1))];
        let a = receipt(&[integer(4), integer(-1)], &charts);
        let b = receipt(&[integer(6), integer(7)], &charts);
        let base = ReceiptRatio::between(&a, &b).unwrap();
        let units = [rat(3, 2), integer(-4)];
        let reframed =
            ReceiptRatio::between(&a.reframe(&units).unwrap(), &b.reframe(&units).unwrap())
                .unwrap();
        let reclocked =
            ReceiptRatio::between(&a.reclock(&units).unwrap(), &b.reclock(&units).unwrap())
                .unwrap();
        for (region, unit) in units.iter().enumerate() {
            assert_eq!(*pair(&reframed, region), pair(&base, region).scaled(unit));
            assert_eq!(
                *pair(&reclocked, region),
                pair(&base, region).scaled(&(Rat::one() / unit))
            );
            assert!(pair(&reframed, region).projectively_equal(pair(&base, region)));
            assert!(pair(&reclocked, region).projectively_equal(pair(&base, region)));
        }
    }

    /// `Holarchy/Receipt.between_comp` in its exact form: `between a b` followed by `between b c`
    /// is `between a c` scaled by `b`'s transported reading, hence projectively equal to it when
    /// that reading is nonzero.
    #[test]
    fn between_composes_as_a_ratio_through_a_nonzero_middle() {
        let charts = [chart(integer(2), rat(1, 3))];
        let (a, b, c) = (
            receipt(&[integer(5)], &charts),
            receipt(&[integer(-2)], &charts),
            receipt(&[integer(9)], &charts),
        );
        let followed = ReceiptRatio::between(&a, &b)
            .unwrap()
            .follow(&ReceiptRatio::between(&b, &c).unwrap())
            .unwrap();
        let direct = ReceiptRatio::between(&a, &c).unwrap();
        assert_eq!(
            *pair(&followed, 0),
            pair(&direct, 0).scaled(&b.common(0).unwrap())
        );
        assert!(pair(&followed, 0).projectively_equal(pair(&direct, 0)));
    }

    /// `Holarchy/Receipt.between_comp_through_zero`: through a zero middle reading the composite is
    /// `(0 : 0)`, returned undetermined rather than as a ratio equal to `between a c`.
    #[test]
    fn a_zero_middle_reading_leaves_the_composite_undetermined() {
        let charts = [RegionChart::rate()];
        let (a, b, c) = (
            receipt(&[integer(5)], &charts),
            receipt(&[integer(0)], &charts),
            receipt(&[integer(9)], &charts),
        );
        let followed = ReceiptRatio::between(&a, &b)
            .unwrap()
            .follow(&ReceiptRatio::between(&b, &c).unwrap())
            .unwrap();
        assert_eq!(followed.regions(), &[Comparison::Undetermined]);
        assert!(
            ReceiptRatio::between(&a, &c).unwrap().regions()[0]
                .presentation()
                .is_some()
        );
    }

    /// `Holarchy/Receipt.raw_comparison_is_frame_dependent`: one reading `2`, carried raw `1` in
    /// frame `2` and raw `2` in frame `1`, compares raw as `(2 : 1)` but as `(2 : 2)` after the
    /// common transport.
    #[test]
    fn raw_readings_compared_before_transport_are_frame_dependent() {
        let a = receipt(&[integer(1)], &[chart(integer(2), integer(1))]);
        let b = receipt(&[integer(2)], &[RegionChart::rate()]);
        let raw = Presentation::new(b.readings()[0].clone(), a.readings()[0].clone());
        assert!(!raw.projectively_equal(&Presentation::new(integer(1), integer(1))));
        assert_eq!(
            *pair(&ReceiptRatio::between(&a, &b).unwrap(), 0),
            Presentation::new(integer(2), integer(2))
        );
    }

    /// `Holarchy/Receipt.between_reclock_count`, `Receipt.common_reclock`: two counts (clock
    /// exponent `0`) compare identically under any change of clock, and two durations (exponent
    /// `−1`) scale by the clock unit itself.
    #[test]
    fn counts_are_clock_invariant_and_durations_scale_by_the_clock() {
        let count = RegionChart::new(integer(3), rat(2, 5), 0).unwrap();
        let duration = RegionChart::new(integer(3), rat(2, 5), -1).unwrap();
        let units = [integer(7), rat(-1, 4)];
        let charts = [count.clone(), duration.clone()];
        let a = receipt(&[integer(4), integer(-6)], &charts);
        let b = receipt(&[integer(-1), integer(9)], &charts);
        let base = ReceiptRatio::between(&a, &b).unwrap();
        let reclocked =
            ReceiptRatio::between(&a.reclock(&units).unwrap(), &b.reclock(&units).unwrap())
                .unwrap();
        assert_eq!(pair(&reclocked, 0), pair(&base, 0));
        assert_eq!(*pair(&reclocked, 1), pair(&base, 1).scaled(&units[1]));
        assert_eq!(
            a.reclock(&units).unwrap().common(1).unwrap(),
            &units[1] * a.common(1).unwrap()
        );
    }

    /// `Holarchy/Receipt.rate_against_count_is_clock_dependent`: a rate (clock exponent `1`) and a
    /// count (exponent `0`) transport differently under a change of clock, so they are refused
    /// rather than compared.
    #[test]
    fn a_rate_is_not_compared_with_a_count() {
        let rate = receipt(&[integer(3)], &[RegionChart::rate()]);
        let count = receipt(
            &[integer(3)],
            &[RegionChart::new(Rat::one(), Rat::one(), 0).unwrap()],
        );
        assert_eq!(
            ReceiptRatio::between(&rate, &count),
            Err(HolonError::UnitsMismatch)
        );
    }
}
