//! Exterior exact-clock consumer for Solenoidal Framework Workbench Alpha (Refs #63 #62).
//! Usage: solenoidal_workbench phase PERIOD_CSV STEP_CSV
//!
//! [agent-inferred] A declared ordered carry cascade has owner modulus N. One input integer a
//! advances the shared SolenoidalChart by a/N turns. The receiving integer face is N*s, the
//! retained tick lift is N*(w+s), and Odometer reads the ring digits. The shared chart owns signed
//! Euclidean carry; this application implements no division-with-remainder or stepping law.
//! Prefix moduli are read from Odometer and form the chart's finite circle-cover tower.
//!
//! This touches the helix, receiver faces and finite tower; pair contacts, cell holonomy and tube
//! dynamics remain attached to their native owners. No HNN Field/Current is instantiated:
//! Current::step admits forward nonnegative occurrences, whereas this explicit clock accepts signed
//! passage. A finite operator receipt witnesses neither a learned capability nor a new proof.
//! The lessons' detached-consumer and fixture-as-learning failures are avoided by executing the
//! library operators and retaining this scope in the machine-readable output.
//!
//! The process retains only its contemporary chart. The returned before/after series is an exterior
//! receipt of this call, never a learned constitution or native retained passage archive.

use std::error::Error;
use std::fmt::Display;

use holonics::geometry::solenoid::{FiniteSolenoidalTower, SolenoidalChart};
use holonics::geometry::winding::Odometer;
use holonics::ratio::places::PlaceReading;
use holonics::ratio::{Rat, integer};
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;

// Exterior request/render bounds, not restrictions on the native operators. Factoring at most
// 16 periods <= 65536 and rendering at most 256 bounded integers keeps this local request small.
const MAX_PERIODS: usize = 16;
const MAX_STEPS: usize = 256;
const MAX_DECIMAL_DIGITS: usize = 128;
const MAX_PERIOD: u64 = 65_536;

type Result<T> = std::result::Result<T, Box<dyn Error>>;

#[derive(Debug, PartialEq, Eq)]
struct Face {
    residue: BigUint,
    winding: BigInt,
    lift: BigInt,
    digits: Vec<BigUint>,
    phase: Rat,
    cover_residues: Vec<BigUint>,
}

struct ClockFace {
    periods: Vec<BigUint>,
    modulus: BigUint,
    chart: SolenoidalChart,
}

impl ClockFace {
    fn new(periods: Vec<BigUint>) -> Result<Self> {
        let cascade = Odometer::new(periods.clone())?;
        let modulus = cascade.modulus();
        let moduli = (1..=periods.len())
            .map(|levels| Odometer::new(periods[..levels].to_vec()).map(|o| o.modulus()))
            .collect::<std::result::Result<Vec<_>, _>>()?;
        let tower = FiniteSolenoidalTower::new(moduli)?;
        let chart = SolenoidalChart::from_transverse(
            tower,
            integer(0),
            vec![BigUint::zero(); periods.len()],
        )?;
        Ok(Self {
            periods,
            modulus,
            chart,
        })
    }

    fn face(&self) -> Result<Face> {
        let scale = Rat::from_integer(BigInt::from(self.modulus.clone()));
        let residue = self.chart.phase() * &scale;
        let lift = self.chart.longitudinal_lift() * scale;
        if !residue.is_integer() || !lift.is_integer() {
            return Err("the shared clock face left the declared integer tick grain".into());
        }
        let residue = residue
            .to_integer()
            .to_biguint()
            .ok_or("negative phase residue")?;
        let cascade = Odometer::from_value(self.periods.clone(), &residue)?;
        let cover_residues = (0..self.chart.tower().levels())
            .map(|level| self.chart.residue(level).cloned())
            .collect::<std::result::Result<Vec<_>, _>>()?;
        Ok(Face {
            residue,
            winding: self.chart.winding().clone(),
            lift: lift.to_integer(),
            digits: cascade.digits().to_vec(),
            phase: self.chart.phase().clone(),
            cover_residues,
        })
    }

    fn advance(&mut self, input: &BigInt) -> Result<(Face, Face, BigInt)> {
        let before = self.face()?;
        self.chart = self
            .chart
            .advance(&Rat::new(input.clone(), BigInt::from(self.modulus.clone())))?;
        let after = self.face()?;
        let carry = &after.winding - &before.winding;
        Ok((before, after, carry))
    }
}

// Every value interpolated into JSON is a validated exact numeric Display or a static string.
// No caller-provided text is interpolated into a JSON string.
fn strings<T: Display>(values: &[T]) -> String {
    format!(
        "[{}]",
        values
            .iter()
            .map(|v| format!("\"{v}\""))
            .collect::<Vec<_>>()
            .join(",")
    )
}

fn face_json(face: &Face) -> String {
    format!(
        "{{\"residue\":\"{}\",\"winding\":\"{}\",\"lift\":\"{}\",\"digits\":{},\"phase\":{{\"numerator\":\"{}\",\"denominator\":\"{}\"}},\"cover_residues\":{}}}",
        face.residue,
        face.winding,
        face.lift,
        strings(&face.digits),
        face.phase.numer(),
        face.phase.denom(),
        strings(&face.cover_residues),
    )
}

fn decimal(text: &str, signed: bool) -> Result<&str> {
    let text = text.trim();
    let digits = if signed {
        text.strip_prefix('-')
            .or_else(|| text.strip_prefix('+'))
            .unwrap_or(text)
    } else {
        text
    };
    if digits.is_empty()
        || digits.len() > MAX_DECIMAL_DIGITS
        || !digits.bytes().all(|b| b.is_ascii_digit())
    {
        return Err("expected a decimal integer within the declared digit limit; exponent notation is not accepted".into());
    }
    Ok(text)
}

fn parse_periods(csv: &str) -> Result<Vec<BigUint>> {
    let cells: Vec<_> = csv.split(',').collect();
    if cells.is_empty() || cells.len() > MAX_PERIODS {
        return Err("the exterior request needs between 1 and 16 periods".into());
    }
    cells.into_iter().map(|cell| {
        let period: u64 = decimal(cell, false)?.parse()?;
        if !(2..=MAX_PERIOD).contains(&period) {
            return Err("periods must be between 2 and 65536; the shared odometer requires at least two states per ring".into());
        }
        Ok(BigUint::from(period))
    }).collect()
}

fn parse_steps(csv: &str) -> Result<Vec<BigInt>> {
    let cells: Vec<_> = csv.split(',').collect();
    if cells.is_empty() || cells.len() > MAX_STEPS {
        return Err("the exterior request needs between 1 and 256 signed integer steps".into());
    }
    cells
        .into_iter()
        .map(|cell| Ok(decimal(cell, true)?.parse()?))
        .collect()
}

fn run(period_csv: &str, step_csv: &str) -> Result<String> {
    let periods = parse_periods(period_csv)?;
    let steps = parse_steps(step_csv)?;
    let period_factors = periods
        .iter()
        .map(|period| {
            Ok(format!(
                "[{}]",
                PlaceReading::of(&Rat::from_integer(BigInt::from(period.clone())))?
                    .places()
                    .iter()
                    .map(|place| format!("[\"{}\",\"{}\"]", place.prime(), place.valuation()))
                    .collect::<Vec<_>>()
                    .join(",")
            ))
        })
        .collect::<Result<Vec<_>>>()?;
    let mut clock = ClockFace::new(periods)?;
    let initial = clock.face()?;
    let mut readings = Vec::with_capacity(steps.len());
    for input in steps {
        let (before, after, carry) = clock.advance(&input)?;
        readings.push(format!(
            "{{\"input\":\"{input}\",\"before\":{},\"after\":{},\"carry\":\"{carry}\"}}",
            face_json(&before),
            face_json(&after),
        ));
    }
    Ok(format!(
        concat!(
            "{{\"operator\":\"phase\",\"periods\":{},\"period_factors\":[{}],\"modulus\":\"{}\",",
            "\"modulus_relation\":\"ordered product of periods; coprimality is not required\",",
            "\"initial\":{},\"steps\":[{}],",
            "\"scope\":\"finite explicit-clock operator; signed SolenoidalChart advance and Odometer digit receiver; no signed HNN Current::step, learning, persistence, or new proof claim\",",
            "\"units\":{{\"input\":\"integer ticks\",\"phase\":\"turns\",\"lift\":\"integer ticks\",\"winding\":\"whole turns\",\"carry\":\"signed section crossings on this input\",\"digits\":\"ordered mixed-radix ring residues, lowest ring first\",\"cover_residues\":\"shared chart section at prefix-product cover moduli\"}},",
            "\"limits\":{{\"max_periods\":\"{}\",\"max_steps\":\"{}\",\"max_decimal_digits\":\"{}\",\"min_period\":\"2\",\"max_period\":\"{}\",\"notation\":\"decimal integers only\",\"scope\":\"exterior request and rendering bounds\"}},",
            "\"owners\":[\"crates/holonics/src/geometry/solenoid.rs\",\"crates/holonics/src/geometry/winding.rs\",\"crates/holonics/src/ratio/places.rs\",\"crates/holonics/src/ratio/surprisal.rs\"]}}"
        ),
        strings(&clock.periods),
        period_factors.join(","),
        clock.modulus,
        face_json(&initial),
        readings.join(","),
        MAX_PERIODS,
        MAX_STEPS,
        MAX_DECIMAL_DIGITS,
        MAX_PERIOD,
    ))
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let result = match arguments.as_slice() {
        [operator, periods, steps] if operator == "phase" => run(periods, steps),
        _ => Err("usage: solenoidal_workbench phase PERIOD_CSV STEP_CSV".into()),
    };
    match result {
        Ok(receipt) => println!("{receipt}"),
        Err(error) => {
            eprintln!("{error}");
            std::process::exit(2);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn signed_passage_keeps_euclidean_residue_and_whole_winding() {
        let mut clock = ClockFace::new(vec![3u8.into(), 5u8.into()]).unwrap();
        let (_, first, carry) = clock.advance(&BigInt::from(14)).unwrap();
        assert_eq!(
            (first.residue, first.winding, carry),
            (14u8.into(), 0.into(), 0.into())
        );
        let (_, second, carry) = clock.advance(&BigInt::from(2)).unwrap();
        assert_eq!(
            (second.residue, second.winding, carry),
            (1u8.into(), 1.into(), 1.into())
        );
        let (_, last, carry) = clock.advance(&BigInt::from(-18)).unwrap();
        assert_eq!(
            (last.residue, last.winding, last.lift, carry),
            (13u8.into(), (-1).into(), (-2).into(), (-2).into())
        );
        assert_eq!(last.digits, vec![1u8.into(), 4u8.into()]);
    }

    #[test]
    fn split_signed_passage_matches_one_composed_shared_advance() {
        let periods = vec![2u8.into(), 4u8.into(), 3u8.into()];
        let mut split = ClockFace::new(periods.clone()).unwrap();
        let mut whole = ClockFace::new(periods).unwrap();
        let a = BigInt::from(10u8).pow(50) + 7;
        let b = -BigInt::from(10u8).pow(51) - 13;
        split.advance(&a).unwrap();
        split.advance(&b).unwrap();
        whole.advance(&(a + b)).unwrap();
        assert_eq!(split.face().unwrap(), whole.face().unwrap());
        assert_eq!(split.chart, whole.chart);
    }

    #[test]
    fn non_coprime_periods_use_owner_product_and_carry_matches_odometer() {
        let periods = vec![2u8.into(), 4u8.into()];
        let mut clock = ClockFace::new(periods.clone()).unwrap();
        let mut odometer = Odometer::new(periods).unwrap();
        assert_eq!(clock.modulus, BigUint::from(8u8));
        for input in [7u8, 2, 16] {
            let (_, face, _) = clock.advance(&BigInt::from(input)).unwrap();
            odometer.advance(&input.into());
            assert_eq!(face.digits, odometer.digits());
            assert_eq!(
                face.winding,
                BigInt::from(odometer.overflow_winding().clone())
            );
            assert_eq!(face.lift, BigInt::from(odometer.value()));
        }
    }
}
