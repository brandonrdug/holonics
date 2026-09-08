//! Exact cold rest for one temporal condition owner.
//!
//! The rest retains the initial rational point, its completed dyadic lift, and each complete
//! chronological native report.  It is a persistence chart for the same temporal owner; it is
//! not a waveform archive and remount never recomputes a centre or replays a native passage.

use super::*;
use crate::{
    dimensional_wave::ExactComplexWaveCurrent,
    native_ecology::constitutive_fibre::circulation::rest::{blob, expect, read_blob},
    native_ecology::constitutive_fibre::{ConstitutiveFibreError, NativeFieldCurrentBall},
    resident_section::ResidentSectionRest,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use num_traits::{One, Signed, Zero};
use serde::{Deserialize, Serialize};
use std::io::{Read, Write};
use std::rc::Rc;

const MAGIC: &[u8] = b"HNA-TEMPORAL-CONDITION-REST\x01";
const END: &[u8] = b"HNA-TEMPORAL-CONDITION-END\x01";
type Error = ConstitutiveFibreError;

fn invalid(detail: impl std::fmt::Display) -> Error {
    Error::Rest(format!("temporal condition rest: {detail}"))
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ContactHeader {
    cut: u64,
    at: usize,
    lineage: PhaseCurrentLineageId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    chart: TemporalResponseChart,
    metric: ConditionContactMetric,
    grain: u32,
    initial_lineage: PhaseCurrentLineageId,
    contacts: Vec<ContactHeader>,
}

/// Exact persistence of one continuing temporal condition owner.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidentTemporalConditionRest {
    header: Header,
    initial: ResidentSectionRest,
    initial_ball: ResidentSectionRest,
    reports: Vec<ResidentSectionRest>,
}

impl ResidentTemporalConditionRest {
    pub fn chart(&self) -> &TemporalResponseChart {
        &self.header.chart
    }

    pub fn grain(&self) -> u32 {
        self.header.grain
    }

    pub fn contacts(&self) -> u64 {
        self.header.contacts.len() as u64
    }

    pub fn metric(&self) -> ConditionContactMetric {
        self.header.metric
    }

    /// Saved exterior lineage of an actual completed cut; zero names the initial response.
    pub fn lineage_at(&self, cut: u64) -> Option<PhaseCurrentLineageId> {
        if cut == 0 {
            return Some(self.header.initial_lineage);
        }
        self.header
            .contacts
            .get(usize::try_from(cut - 1).ok()?)
            .map(|c| c.lineage)
    }

    pub fn validate(&self) -> Result<(), Error> {
        validate_rest(self)
    }

    pub fn write(&self, out: &mut impl Write) -> Result<(), Error> {
        self.validate()?;
        out.write_all(MAGIC).map_err(invalid)?;
        blob(out, &serde_json::to_vec(&self.header).map_err(invalid)?)?;
        blob(out, &self.initial.canonical_bytes().map_err(invalid)?)?;
        blob(out, &self.initial_ball.canonical_bytes().map_err(invalid)?)?;
        for report in &self.reports {
            blob(out, &report.canonical_bytes().map_err(invalid)?)?;
        }
        out.write_all(END).map_err(invalid)
    }

    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, Error> {
        let mut input = input.take(octets);
        expect(&mut input, MAGIC)?;
        let header: Header = serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        let initial = ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid)?;
        let initial_ball = ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid)?;
        let mut reports = Vec::with_capacity(header.contacts.len());
        for _ in &header.contacts {
            reports.push(ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid)?);
        }
        expect(&mut input, END)?;
        if input.limit() != 0 {
            return Err(invalid("trailing temporal condition rest bytes"));
        }
        let rest = Self {
            header,
            initial,
            initial_ball,
            reports,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub(super) fn from_current(
        current: &ResidentTemporalConditionCurrent<'_>,
    ) -> Result<Self, Error> {
        let mut reports = Vec::new();
        let mut root = &current.current.standing;
        let initial = loop {
            match &root.construction {
                TemporalConstruction::Initial(section) => break section,
                TemporalConstruction::Contact(prior) => {
                    reports.push(root);
                    root = prior;
                }
            }
        };
        reports.reverse();
        let initial = current.surface.detach_section(initial, 64)?;
        let initial_ball = current.surface.detach_section(&root.section, 64)?;
        let contacts = reports
            .iter()
            .map(|standing| ContactHeader {
                cut: standing.cut,
                at: standing.at,
                lineage: standing.lineage,
            })
            .collect();
        let reports = reports
            .into_iter()
            .map(|standing| current.surface.detach_section(&standing.section, 64))
            .collect::<Result<Vec<_>, _>>()?;
        let rest = Self {
            header: Header {
                chart: current.current.chart.clone(),
                metric: current.metric,
                grain: current.current.grain,
                initial_lineage: root.lineage,
                contacts,
            },
            initial,
            initial_ball,
            reports,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub(super) fn remount<'c>(
        self,
        surface: &'c ResidentSurface<'c>,
    ) -> Result<ResidentTemporalConditionCurrent<'c>, Error> {
        self.validate()?;
        let initial = surface.mount_section_rest(&self.initial)?;
        let initial_ball = surface.mount_section_rest(&self.initial_ball)?;
        let mut standing = Rc::new(TemporalStanding {
            section: initial_ball,
            at: 0,
            cut: 0,
            lineage: self.header.initial_lineage,
            construction: TemporalConstruction::Initial(initial),
        });
        for (metadata, report) in self.header.contacts.iter().zip(self.reports) {
            let section = surface.mount_section_rest(&report)?;
            standing = Rc::new(TemporalStanding {
                section,
                at: metadata.at,
                cut: metadata.cut,
                lineage: metadata.lineage,
                construction: TemporalConstruction::Contact(Rc::clone(&standing)),
            });
        }
        Ok(ResidentTemporalConditionCurrent {
            surface,
            current: ResidentTemporalConditionSnapshot {
                standing,
                owner: Rc::new(()),
                chart: self.header.chart,
                grain: self.header.grain,
            },
            metric: self.header.metric,
        })
    }
}

fn words(rest: &ResidentSectionRest) -> Result<&[(i64, i64)], Error> {
    rest.validate().map_err(invalid)?;
    if rest.rows != 1 || rest.grain != ResidentGrain(0) || rest.bound_octaves != 64 {
        return Err(invalid("temporal section shape or aperture"));
    }
    Ok(&rest.intervals)
}

fn signed_wide_words(words: &[(i64, i64)], at: usize) -> Result<i128, Error> {
    let low = words
        .get(
            at.checked_mul(2)
                .ok_or_else(|| invalid("wide index overflow"))?,
        )
        .ok_or_else(|| invalid("wide low word"))?;
    let high = words
        .get(
            at.checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or_else(|| invalid("wide index overflow"))?,
        )
        .ok_or_else(|| invalid("wide high word"))?;
    if low.0 != low.1 || high.0 != high.1 {
        return Err(invalid("wide endpoint is not point-valued"));
    }
    Ok((((high.0 as u64 as u128) << 64) | low.0 as u64 as u128) as i128)
}

fn integer(value: i128) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn initial_values(
    rest: &ResidentSectionRest,
    chart: &TemporalResponseChart,
) -> Result<Vec<ExactComplexWaveCurrent>, Error> {
    let words = words(rest)?;
    let coordinates = chart
        .raw_extent
        .checked_mul(2)
        .ok_or_else(|| invalid("initial extent overflow"))?;
    if words.len() <= coordinates
        || (words.len() - 1) % 2 != 0
        || words.len() != rest.width
        || words.iter().any(|(value, upper)| value != upper)
        || words[coordinates..words.len() - 1]
            .iter()
            .any(|(value, _)| *value != 0)
    {
        return Err(invalid("initial point shape"));
    }
    let denominator = words
        .last()
        .ok_or_else(|| invalid("initial denominator"))?
        .0;
    if denominator <= 0 {
        return Err(invalid("initial denominator"));
    }
    let denominator = BigInt::from(denominator);
    Ok((0..chart.raw_extent)
        .map(|index| {
            ExactComplexWaveCurrent::new(
                Rat::new(words[2 * index].0.into(), denominator.clone()),
                Rat::new(words[2 * index + 1].0.into(), denominator.clone()),
            )
        })
        .collect())
}

fn ball(
    rest: &ResidentSectionRest,
    at: usize,
    extent: usize,
    grain: u32,
) -> Result<NativeFieldCurrentBall, Error> {
    let words = words(rest)?;
    let values = extent
        .checked_mul(2)
        .and_then(|n| n.checked_add(1))
        .ok_or_else(|| invalid("ball extent overflow"))?;
    let end = at
        .checked_add(values)
        .ok_or_else(|| invalid("ball index overflow"))?;
    if end > rest.width / 2 || !(1..=120).contains(&grain) {
        return Err(invalid("ball shape or grain"));
    }
    let scale = BigInt::one() << grain;
    let numerator = |index: usize| signed_wide_words(words, at + index);
    let center = (0..extent)
        .map(|index| {
            Ok(ExactComplexWaveCurrent::new(
                Rat::new(numerator(2 * index)?.into(), scale.clone()),
                Rat::new(numerator(2 * index + 1)?.into(), scale.clone()),
            ))
        })
        .collect::<Result<Vec<_>, Error>>()?;
    let radius = numerator(2 * extent)?;
    if radius < 0 {
        return Err(invalid("ball radius is negative"));
    }
    Ok(NativeFieldCurrentBall {
        center,
        radius: Rat::new(radius.into(), scale),
    })
}

fn realify(values: &[ExactComplexWaveCurrent]) -> Vec<Rat> {
    values
        .iter()
        .flat_map(|value| [value.real.clone(), value.imaginary.clone()])
        .collect()
}

fn complexify(values: &[Rat]) -> Vec<ExactComplexWaveCurrent> {
    values
        .chunks_exact(2)
        .map(|pair| ExactComplexWaveCurrent::new(pair[0].clone(), pair[1].clone()))
        .collect()
}

fn gram_psd(gram: &[Vec<Rat>], raw: &[Rat]) -> Result<(), Error> {
    let n = gram.len();
    if n == 0
        || gram.iter().any(|row| row.len() != n)
        || (0..n).any(|i| (0..n).any(|j| gram[i][j] != gram[j][i]))
    {
        return Err(invalid("Gram symmetry"));
    }
    let mut reduced = gram.to_vec();
    let mut rhs = raw.to_vec();
    for k in 0..n {
        let pivot = reduced[k][k].clone();
        if pivot.is_negative() {
            return Err(invalid("Gram is not positive semidefinite"));
        }
        if pivot.is_zero() {
            if !rhs[k].is_zero() || (k + 1..n).any(|j| !reduced[k][j].is_zero()) {
                return Err(invalid("zero Gram pivot has a nonzero cross term"));
            }
            continue;
        }
        for i in k + 1..n {
            let removed_rhs = &reduced[i][k] * &rhs[k] / &pivot;
            rhs[i] -= removed_rhs;
            for j in k + 1..n {
                let removed = &reduced[i][k] * &reduced[k][j] / &pivot;
                reduced[i][j] -= removed;
            }
        }
    }
    Ok(())
}

fn report_tail(
    rest: &ResidentSectionRest,
    chart: &TemporalResponseChart,
    grain: u32,
) -> Result<(Vec<Vec<Rat>>, Vec<ExactComplexWaveCurrent>, Rat, Rat, Rat), Error> {
    let section_words = words(rest)?;
    let dimension = chart
        .raw_extent
        .checked_mul(2)
        .ok_or_else(|| invalid("report dimension overflow"))?;
    let stride = dimension + 1;
    let matrix_count = dimension
        .checked_mul(dimension)
        .ok_or_else(|| invalid("report matrix overflow"))?;
    let tail = 8usize
        .checked_mul(stride)
        .ok_or_else(|| invalid("report tail overflow"))?;
    let total = tail
        .checked_add(matrix_count)
        .and_then(|n| n.checked_add(dimension))
        .and_then(|n| n.checked_add(3))
        .ok_or_else(|| invalid("report extent overflow"))?;
    if rest.width
        != total
            .checked_mul(2)
            .ok_or_else(|| invalid("report width overflow"))?
    {
        return Err(invalid("report width"));
    }
    let gram = (0..dimension)
        .map(|row| {
            (0..dimension)
                .map(|column| {
                    Ok(integer(signed_wide_words(
                        section_words,
                        tail + row * dimension + column,
                    )?))
                })
                .collect::<Result<Vec<_>, Error>>()
        })
        .collect::<Result<Vec<_>, Error>>()?;
    let raw = (0..dimension)
        .map(|index| {
            Ok(integer(signed_wide_words(
                section_words,
                tail + matrix_count + index,
            )?))
        })
        .collect::<Result<Vec<_>, Error>>()?;
    let raw_xy = complexify(&raw);
    let px = integer(signed_wide_words(
        section_words,
        tail + matrix_count + dimension,
    )?);
    let py = integer(signed_wide_words(
        section_words,
        tail + matrix_count + dimension + 1,
    )?);
    let cden = integer(signed_wide_words(
        section_words,
        tail + matrix_count + dimension + 2,
    )?);
    if !px.is_positive() || !py.is_positive() || !cden.is_positive() || grain == 0 {
        return Err(invalid("report scalar admission"));
    }
    gram_psd(&gram, &raw)?;
    // A complex-linear X has this realification. This checks the saved algebra, not the
    // provenance of X in a particular recording (that remains an exterior source-qualified check).
    for i in (0..dimension).step_by(2) {
        for j in (0..dimension).step_by(2) {
            if gram[i][j] != gram[i + 1][j + 1] || gram[i][j + 1] != -&gram[i + 1][j] {
                return Err(invalid("Gram complex realification"));
            }
        }
    }
    let xd_squared = u128::try_from(cden.to_integer()).map_err(invalid)?;
    let xd = BigInt::from(xd_squared.isqrt());
    let ratio = Rat::new(px.to_integer(), py.to_integer());
    if &xd * &xd != cden.to_integer()
        || &xd % px.numer() != BigInt::zero()
        || ratio.numer() != px.numer()
        || ratio.denom() != py.numer()
        || xd > BigInt::from(i64::MAX)
        || (&xd / px.numer()) * py.numer() > BigInt::from(i64::MAX)
    {
        return Err(invalid("source/observation denominator reduction"));
    }
    Ok((gram, raw_xy, px, py, cden))
}

fn validate_rest(rest: &ResidentTemporalConditionRest) -> Result<(), Error> {
    let chart = &rest.header.chart;
    if chart.raw_extent == 0
        || chart.phase_extent == 0
        || !chart.sample_step.is_positive()
        || !(1..=120).contains(&rest.header.grain)
        || rest.header.contacts.len() != rest.reports.len()
    {
        return Err(invalid("temporal chart or contact census"));
    }
    let initial = initial_values(&rest.initial, chart)?;
    let dimension = chart
        .raw_extent
        .checked_mul(2)
        .ok_or_else(|| invalid("temporal dimension overflow"))?;
    let ball_width = dimension
        .checked_add(1)
        .and_then(|n| n.checked_mul(2))
        .ok_or_else(|| invalid("initial ball width overflow"))?;
    if rest.initial_ball.width != ball_width {
        return Err(invalid("initial ball width"));
    }
    let initial_ball = ball(&rest.initial_ball, 0, chart.raw_extent, rest.header.grain)?;
    if !initial_ball.contains(&initial) {
        return Err(invalid("initial lift does not contain its exact point"));
    }
    let scale = BigInt::one() << rest.header.grain;
    let expected_center: Vec<_> = initial
        .iter()
        .map(|v| {
            ExactComplexWaveCurrent::new(
                Rat::new(
                    (&v.real * Rat::from_integer(scale.clone())).to_integer(),
                    scale.clone(),
                ),
                Rat::new(
                    (&v.imaginary * Rat::from_integer(scale.clone())).to_integer(),
                    scale.clone(),
                ),
            )
        })
        .collect();
    let rounded = realify(&initial)
        .iter()
        .filter(|v| !(*v * Rat::from_integer(scale.clone())).is_integer())
        .count();
    if initial_ball.center != expected_center
        || initial_ball.radius != Rat::new(rounded.into(), scale.clone())
    {
        return Err(invalid("initial dyadic lift certificate"));
    }
    let stride = dimension + 1;
    let expected_at = 3usize
        .checked_mul(stride)
        .ok_or_else(|| invalid("standing offset overflow"))?;
    let mut prior = initial_ball;
    let mut exact_prior = initial;
    for (index, (metadata, report)) in rest.header.contacts.iter().zip(&rest.reports).enumerate() {
        if metadata.cut != (index + 1) as u64 || metadata.at != expected_at {
            return Err(invalid("contact chronology or standing offset"));
        }
        let report_words = words(report)?;
        let matrix_count = dimension
            .checked_mul(dimension)
            .ok_or_else(|| invalid("report matrix overflow"))?;
        let total = stride
            .checked_mul(8)
            .and_then(|n| n.checked_add(matrix_count))
            .and_then(|n| n.checked_add(dimension))
            .and_then(|n| n.checked_add(3))
            .ok_or_else(|| invalid("report extent overflow"))?;
        if report.width
            != total
                .checked_mul(2)
                .ok_or_else(|| invalid("report width overflow"))?
            || report_words.iter().any(|(lo, hi)| lo != hi)
        {
            return Err(invalid("contact report shape"));
        }
        let blocks = (0..6)
            .map(|block| ball(report, block * stride, chart.raw_extent, rest.header.grain))
            .collect::<Result<Vec<_>, Error>>()?;
        if blocks[0] != prior {
            return Err(invalid("contact prior ball does not continue"));
        }
        for component in 0..dimension {
            let component_value = |block: usize| {
                if component % 2 == 0 {
                    blocks[block].center[component / 2].real.clone()
                } else {
                    blocks[block].center[component / 2].imaginary.clone()
                }
            };
            if component_value(1) + component_value(2) != component_value(3) {
                return Err(invalid("contact h = u + v"));
            }
            if component_value(0) - component_value(1) != component_value(4) {
                return Err(invalid("contact returned normal"));
            }
            if component_value(3) - component_value(0) != component_value(5) {
                return Err(invalid("contact difference"));
            }
        }
        if blocks[3].radius != blocks[1].radius.clone() + blocks[2].radius.clone()
            || blocks[4].radius != blocks[0].radius.clone() + blocks[1].radius.clone()
            || blocks[5].radius != blocks[3].radius.clone() + blocks[0].radius.clone()
        {
            return Err(invalid("contact radius algebra"));
        }
        let (gram, raw_xy, px, py, cden) = report_tail(report, chart, rest.header.grain)?;
        let prior_real = realify(&exact_prior);
        let raw_real = realify(&raw_xy);
        let mut matrix = gram.clone();
        let mut rhs_u = Vec::with_capacity(dimension);
        let mut rhs_v = Vec::with_capacity(dimension);
        for (row, values) in matrix.iter_mut().enumerate() {
            values[row] += &cden;
            rhs_u.push((&px / &py) * &raw_real[row]);
            rhs_v.push(&cden * &prior_real[row]);
        }
        let u = super::inspect::solve_exact(matrix.clone(), rhs_u)?;
        let v = super::inspect::solve_exact(matrix, rhs_v)?;
        let exact = complexify(&u.iter().zip(&v).map(|(u, v)| u + v).collect::<Vec<_>>());
        if !blocks[3].contains(&exact) {
            return Err(invalid("successor ball does not contain exact response"));
        }
        let w = |at| signed_wide_words(report_words, at).map(BigInt::from);
        let den_u = &py.to_integer() * cden.to_integer();
        let den_v = cden.to_integer();
        if w(6 * stride + dimension)? != den_u || w(7 * stride + dimension)? != den_v {
            return Err(invalid("residual denominators"));
        }
        let mut sum_u = BigInt::zero();
        let mut sum_v = BigInt::zero();
        for row in 0..dimension {
            let mut au = BigInt::zero();
            let mut av = BigInt::zero();
            for column in 0..dimension {
                let mut a = gram[row][column].to_integer();
                if row == column {
                    a += &den_v;
                }
                au += &a * w(2 * stride + column)?;
                av += &a * w(stride + column)?;
            }
            let ru = py.to_integer() * au - px.to_integer() * raw_real[row].to_integer() * &scale;
            let rv = av - &den_v * w(row)?;
            if w(6 * stride + row)? != ru || w(7 * stride + row)? != rv {
                return Err(invalid("resident residual certificate"));
            }
            sum_u += ru.abs();
            sum_v += rv.abs();
        }
        let ceil = |n: BigInt, d: &BigInt| (&n + d - BigInt::one()) / d;
        if w(2 * stride + dimension)? != ceil(sum_u, &den_u)
            || w(stride + dimension)? != w(dimension)? + ceil(sum_v, &den_v)
        {
            return Err(invalid("directed residual radius certificate"));
        }
        // Full exact response membership is a cold consistency check. It never replaces the
        // installed dyadic section or claims the recording-relative preimage is a singleton.
        if !blocks[1].contains(&complexify(&v)) || !blocks[2].contains(&complexify(&u)) {
            return Err(invalid("normal response ball containment"));
        }
        prior = blocks[3].clone();
        exact_prior = exact;
    }
    Ok(())
}

#[cfg(test)]
mod tests;
