use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::point_section;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::Zero;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(in super::super::super) struct OperativeSourceOverlapFrame {
    pub source: usize,
    pub count: usize,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(in super::super::super) struct OperativeMapProgramFrame {
    pub at_cut: usize,
    pub return_count: usize,
    pub contact_count: usize,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(in super::super::super) struct OperativeFactorProgramFrame {
    pub rows: usize,
    pub boundary_components: usize,
    pub rank: usize,
    pub nonzeros: usize,
    /// Presence marks the bounded current-amplitude family extension.  Old frames omit it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub group_width: Option<usize>,
}
#[derive(Debug, PartialEq, Eq)]
pub(in super::super::super) struct OperativeMapProgramRest {
    pub map: ResidentSectionRest,
    pub births: Vec<ResidentSectionRest>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(in super::super::super) struct OperativeReturnFrame {
    pub at_cut: usize,
    pub contact_count: usize,
    /// Omitted legacy frames store both factors over the complete contact population.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub factor_count: Option<usize>,
    /// First factor is the source passage's interior difference; payload stores only ell.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub current_difference_source: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_overlap: Option<OperativeSourceOverlapFrame>,
    /// Explicit zero generator; its wire payload is the canonical one-word zero marker.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub zero_internal_delta: bool,
    #[serde(default)]
    pub realization: NativeContactRealization,
    #[serde(default, skip_serializing_if = "is_default_bound_kind")]
    pub bound_kind: NativeOperativeBoundKind,
}
fn is_default_bound_kind(kind: &NativeOperativeBoundKind) -> bool {
    *kind == NativeOperativeBoundKind::MatrixAndInternal
}
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(in super::super::super) struct OperativeWire {
    pub activated_at: usize,
    pub births: Vec<NativeOperativeContactBirth>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub declared_origins: Vec<NativeFieldContactOrigin>,
    /// Legacy wire packets omitted this field and always carried dense covariance sections.
    #[serde(default = "legacy_dense_covariance")]
    pub dense_covariance: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub factor_program: Option<OperativeFactorProgramFrame>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub initial_factor_program: Option<OperativeFactorProgramFrame>,
    pub returns: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub return_frames: Vec<OperativeReturnFrame>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub map_program: Option<OperativeMapProgramFrame>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub propagate_from: Option<usize>,
}
fn legacy_dense_covariance() -> bool {
    true
}

/// Cold validation for the bounded positive pair family.  This deliberately reads only detached
/// words; it is also used by outstanding source witnesses, whose producing CSR remains fixed.
pub(super) fn validate_amplitude_family_sections(
    frame: &OperativeFactorProgramFrame,
    family: &[ResidentSectionRest; 4],
    factor: &[ResidentSectionRest; 9],
    current_bounds: &ResidentSectionRest,
    grain: u32,
    rows: usize,
    boundary_components: usize,
) -> Result<(), Error> {
    let group_width = frame
        .group_width
        .ok_or_else(|| invalid("amplitude family metadata"))?;
    if !(1..=120).contains(&grain)
        || group_width == 0
        || rows == 0
        || rows % group_width != 0
        || frame.rank != 0
        || frame.boundary_components != boundary_components
    {
        return Err(invalid("amplitude family grouping/rank"));
    }
    let nnz = frame.nonzeros;
    if boundary_components == 0 || boundary_components % 2 != 0 || frame.rows != rows {
        return Err(invalid("amplitude family dimensions"));
    }
    let sparse = nnz.max(1).checked_mul(2).ok_or(Error::Shape)?;
    let coefficients = sparse.checked_mul(2).ok_or(Error::Shape)?;
    point_section(
        &factor[0],
        1,
        rows.checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or(Error::Shape)?,
    )?;
    point_section(&factor[1], 1, sparse)?;
    point_section(&factor[2], 1, coefficients)?;
    point_section(
        &factor[3],
        1,
        (boundary_components / 2)
            .checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or(Error::Shape)?,
    )?;
    point_section(&factor[4], 1, sparse)?;
    point_section(&factor[5], 1, coefficients)?;
    point_section(&family[0], 1, coefficients)?;
    point_section(&family[1], 1, coefficients)?;
    point_section(&family[2], 1, 4)?;
    point_section(&family[3], rows / group_width, 6)?;
    point_section(current_bounds, 1, 4)?;
    let rho = wides(&family[3].intervals)?;
    for row in rho.chunks_exact(3) {
        if row[0] <= 0 || row[1] != 0 || row[2] != 0 {
            return Err(invalid("amplitude point row"));
        }
    }
    let template_bound = wides(&family[2].intervals)?;
    let current_bound = wides(&current_bounds.intervals)?;
    if template_bound.iter().any(|x| *x < 0) || current_bound.iter().any(|x| *x < 0) {
        return Err(invalid("amplitude template/current radius"));
    }
    let offsets = wides(&factor[0].intervals)?;
    let columns = wides(&factor[1].intervals)?;
    let template = wides(&family[0].intervals)?;
    let current = wides(&factor[2].intervals)?;
    let toffsets = wides(&factor[3].intervals)?;
    let trows = wides(&factor[4].intervals)?;
    let ttemplate = wides(&family[1].intervals)?;
    let tcurrent = wides(&factor[5].intervals)?;
    if nnz == 0
        && columns
            .iter()
            .chain(&template)
            .chain(&current)
            .chain(&trows)
            .chain(&ttemplate)
            .chain(&tcurrent)
            .any(|v| *v != 0)
    {
        return Err(invalid("empty amplitude template packet"));
    }
    if offsets.first().copied() != Some(0) || toffsets.first().copied() != Some(0) {
        return Err(invalid("amplitude CSR origin"));
    }
    if offsets.len() != rows + 1
        || columns.len() != nnz.max(1)
        || template.len() != 2 * nnz.max(1)
        || current.len() != 2 * nnz.max(1)
        || toffsets.len() != boundary_components / 2 + 1
        || trows.len() != nnz.max(1)
        || ttemplate.len() != 2 * nnz.max(1)
        || offsets.windows(2).any(|w| w[0] < 0 || w[1] < w[0])
        || offsets.last().copied() != Some(nnz as i128)
        || toffsets.windows(2).any(|w| w[0] < 0 || w[1] < w[0])
        || toffsets.last().copied() != Some(nnz as i128)
    {
        return Err(invalid("amplitude CSR extent"));
    }
    let scale = BigInt::from(1) << grain;
    let mut transpose: BTreeMap<(usize, usize), Vec<(i128, i128)>> = BTreeMap::new();
    let mut direct: BTreeMap<(usize, usize), Vec<(i128, i128)>> = BTreeMap::new();
    let mut max_rho = BigInt::from(0);
    let mut inexact = 0i128;
    for row in 0..rows {
        let lo = usize::try_from(offsets[row]).map_err(|_| invalid("amplitude CSR offset"))?;
        let hi = usize::try_from(offsets[row + 1]).map_err(|_| invalid("amplitude CSR offset"))?;
        if hi > nnz {
            return Err(invalid("amplitude CSR offset"));
        }
        let r = BigInt::from(rho[3 * (row / group_width)]);
        if r > max_rho {
            max_rho = r.clone();
        }
        for j in lo..hi {
            let c = usize::try_from(columns[j]).map_err(|_| invalid("amplitude CSR column"))?;
            if c % 2 != 0 || c >= boundary_components {
                return Err(invalid("amplitude CSR column address"));
            }
            let pair = (template[2 * j], template[2 * j + 1]);
            direct.entry((row, c / 2)).or_default().push(pair);
            let mut expected = [0i128; 2];
            for axis in 0..2 {
                let product = &r * BigInt::from(if axis == 0 { pair.0 } else { pair.1 });
                let q = product.div_floor(&scale);
                let rem = &product - (&q * &scale);
                if !rem.is_zero() {
                    inexact = inexact.checked_add(1).ok_or(Error::Shape)?;
                }
                expected[axis] =
                    i128::try_from(q).map_err(|_| invalid("amplitude coefficient overflow"))?;
                if current[2 * j + axis] != expected[axis] {
                    return Err(invalid("amplitude current/template mismatch"));
                }
            }
        }
    }
    for component in 0..boundary_components / 2 {
        let lo = usize::try_from(toffsets[component])
            .map_err(|_| invalid("amplitude transpose offset"))?;
        let hi = usize::try_from(toffsets[component + 1])
            .map_err(|_| invalid("amplitude transpose offset"))?;
        if hi > nnz {
            return Err(invalid("amplitude transpose offset"));
        }
        for j in lo..hi {
            let row = usize::try_from(trows[j]).map_err(|_| invalid("amplitude transpose row"))?;
            if row >= rows {
                return Err(invalid("amplitude transpose row"));
            }
            let r = BigInt::from(rho[3 * (row / group_width)]);
            for axis in 0..2 {
                let expected = (&r * BigInt::from(ttemplate[2 * j + axis])).div_floor(&scale);
                if expected != BigInt::from(tcurrent[2 * j + axis]) {
                    return Err(invalid("amplitude transpose current/template mismatch"));
                }
            }
            transpose
                .entry((row, component))
                .or_default()
                .push((ttemplate[2 * j], ttemplate[2 * j + 1]));
        }
    }
    for values in direct.values_mut() {
        values.sort_unstable();
    }
    for values in transpose.values_mut() {
        values.sort_unstable();
    }
    if direct != transpose {
        return Err(invalid("amplitude CSR/transpose template mismatch"));
    }
    let expected_radius =
        (&max_rho * BigInt::from(template_bound[0])).div_ceil(&scale) + BigInt::from(inexact);
    if BigInt::from(current_bound[0]) < expected_radius {
        return Err(invalid("amplitude current bound"));
    }
    Ok(())
}
#[derive(Debug, PartialEq, Eq)]
pub(in super::super::super) struct OperativeRest {
    pub current: [ResidentSectionRest; 5],
    pub initial: [ResidentSectionRest; 5],
    pub covariance: [Option<ResidentSectionRest>; 2],
    pub factor_program: [Option<[ResidentSectionRest; 9]>; 2],
    /// Fixed templates plus the current positive amplitudes; no update history is retained.
    pub amplitude_family: [Option<[ResidentSectionRest; 4]>; 2],
    pub returns: Vec<[ResidentSectionRest; 4]>,
    pub source_overlaps: Vec<Option<[ResidentSectionRest; 2]>>,
    pub program: Option<OperativeMapProgramRest>,
}
#[derive(Debug, PartialEq, Eq)]
pub(in super::super::super) struct OperativeHistoryRest {
    pub count: usize,
    pub b: ResidentSectionRest,
    pub bounds: ResidentSectionRest,
    pub trace: ResidentSectionRest,
    pub propagation_input_bounds: Option<ResidentSectionRest>,
}
impl OperativeWire {
    fn contact_count_at(&self, cut: usize) -> usize {
        if self.declared_origins.is_empty() {
            self.births
                .iter()
                .filter(|birth| birth.receiving < cut)
                .count()
        } else {
            self.births.len()
        }
    }
    fn frame(&self, i: usize) -> OperativeReturnFrame {
        self.return_frames
            .get(i)
            .cloned()
            .unwrap_or_else(|| OperativeReturnFrame {
                at_cut: self.activated_at,
                factor_count: None,
                current_difference_source: None,
                source_overlap: None,
                zero_internal_delta: false,
                realization: NativeContactRealization::EnclosedFlow,
                bound_kind: NativeOperativeBoundKind::MatrixAndInternal,
                contact_count: self.contact_count_at(self.activated_at),
            })
    }
}
impl OperativeHistoryRest {
    pub fn write(
        &self,
        section: &mut impl FnMut(&ResidentSectionRest) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let count = i64::try_from(self.count).map_err(invalid)?;
        let mut header = vec![(count, count)];
        if self.propagation_input_bounds.is_some() {
            header.push((1, 1));
        }
        section(
            &ResidentSectionRest::found(1, header.len(), ResidentGrain(0), 64, header)
                .map_err(invalid)?,
        )?;
        for s in [&self.b, &self.bounds, &self.trace] {
            section(s)?;
        }
        if let Some(bounds) = &self.propagation_input_bounds {
            section(bounds)?;
        }
        Ok(())
    }
    pub fn read(
        section: &mut impl FnMut() -> Result<ResidentSectionRest, Error>,
    ) -> Result<Self, Error> {
        let count = section()?;
        if !matches!(count.width, 1 | 2) {
            return Err(invalid("historical propagation header"));
        }
        point_section(&count, 1, count.width)?;
        let propagated = count.width == 2;
        if propagated && count.intervals[1] != (1, 1) {
            return Err(invalid("historical propagation flag"));
        }
        let count = usize::try_from(count.intervals[0].0).map_err(invalid)?;
        Ok(Self {
            count,
            b: section()?,
            bounds: section()?,
            trace: section()?,
            propagation_input_bounds: propagated.then(|| section()).transpose()?,
        })
    }
    pub fn validate(&self, d: usize, expected: usize) -> Result<(), Error> {
        if self.count != expected {
            return Err(invalid("historical contact population"));
        }
        point_section(&self.b, expected.max(1), 4)?;
        point_section(&self.bounds, 1, 4)?;
        point_section(&self.trace, 1, 18 * d + 12)?;
        if let Some(bounds) = &self.propagation_input_bounds {
            point_section(bounds, 1, 4)?;
            if wides(&bounds.intervals)?.iter().any(|v| *v < 0) {
                return Err(invalid("propagation input radius"));
            }
        }
        if wides(&self.bounds.intervals)?.iter().any(|v| *v < 0) {
            return Err(invalid("historical map/current radius"));
        }
        for w in self.trace.intervals[..18 * d].chunks_exact(18) {
            if ![0, 1].contains(&w[17].0)
                || (w[17].0 == 1 && w[..17].iter().all(|v| v.0 == 0))
                || w[..17].iter().any(|v| v.0 < 0 || v.0 > u32::MAX as i64)
            {
                return Err(invalid("historical residual limb"));
            }
        }
        if wides(&self.trace.intervals[18 * d..])?
            .iter()
            .any(|v| *v < 0)
        {
            return Err(invalid("historical residual bound"));
        }
        Ok(())
    }
}
impl OperativeRest {
    pub fn read(
        wire: &OperativeWire,
        section: &mut impl FnMut() -> Result<ResidentSectionRest, Error>,
    ) -> Result<Self, Error> {
        let mut dense_six = || -> Result<([ResidentSectionRest; 5], ResidentSectionRest), Error> {
            let map = section()?;
            let b = section()?;
            let bounds = section()?;
            let covariance = section()?;
            let aggregate = section()?;
            let moment_bounds = section()?;
            Ok(([map, b, bounds, aggregate, moment_bounds], covariance))
        };
        let (current, current_covariance, initial, initial_covariance) = if wire.dense_covariance {
            let (current, covariance) = dense_six()?;
            let (initial, initial_covariance) = dense_six()?;
            (current, Some(covariance), initial, Some(initial_covariance))
        } else {
            let mut five = || -> Result<[ResidentSectionRest; 5], Error> {
                Ok([section()?, section()?, section()?, section()?, section()?])
            };
            (five()?, None, five()?, None)
        };
        let factor_program = wire
            .factor_program
            .as_ref()
            .map(|_| {
                Ok::<_, Error>([
                    section()?,
                    section()?,
                    section()?,
                    section()?,
                    section()?,
                    section()?,
                    section()?,
                    section()?,
                    section()?,
                ])
            })
            .transpose()?;
        let initial_factor_program = wire
            .initial_factor_program
            .as_ref()
            .map(|_| {
                Ok::<_, Error>([
                    section()?,
                    section()?,
                    section()?,
                    section()?,
                    section()?,
                    section()?,
                    section()?,
                    section()?,
                    section()?,
                ])
            })
            .transpose()?;
        let mut read_family = |frame: Option<&OperativeFactorProgramFrame>| {
            frame
                .and_then(|f| f.group_width.map(|_| ()))
                .map(|_| Ok::<_, Error>([section()?, section()?, section()?, section()?]))
                .transpose()
        };
        let amplitude_family = [
            read_family(wire.factor_program.as_ref())?,
            read_family(wire.initial_factor_program.as_ref())?,
        ];
        let program = wire
            .map_program
            .as_ref()
            .map(|p| {
                let count = wire
                    .births
                    .len()
                    .checked_sub(p.contact_count)
                    .ok_or_else(|| invalid("program birth domain"))?;
                Ok::<_, Error>(OperativeMapProgramRest {
                    map: section()?,
                    births: (0..count).map(|_| section()).collect::<Result<_, _>>()?,
                })
            })
            .transpose()?;
        let mut returns = Vec::new();
        let mut source_overlaps = Vec::new();
        for i in 0..wire.returns {
            returns.push([section()?, section()?, section()?, section()?]);
            source_overlaps.push(
                wire.frame(i)
                    .source_overlap
                    .is_some()
                    .then(|| Ok::<_, Error>([section()?, section()?]))
                    .transpose()?,
            );
        }
        Ok(Self {
            current,
            initial,
            covariance: [current_covariance, initial_covariance],
            factor_program: [factor_program, initial_factor_program],
            amplitude_family,
            returns,
            source_overlaps,
            program,
        })
    }
    pub fn write(
        &self,
        section: &mut impl FnMut(&ResidentSectionRest) -> Result<(), Error>,
    ) -> Result<(), Error> {
        if let [Some(current_covariance), Some(initial_covariance)] = &self.covariance {
            for s in &self.current[..3] {
                section(s)?;
            }
            section(current_covariance)?;
            for s in &self.current[3..] {
                section(s)?;
            }
            for s in &self.initial[..3] {
                section(s)?;
            }
            section(initial_covariance)?;
            for s in &self.initial[3..] {
                section(s)?;
            }
        } else {
            for s in self.current.iter().chain(&self.initial) {
                section(s)?;
            }
        }
        for factor_program in &self.factor_program {
            if let Some(factor_program) = factor_program {
                for value in factor_program {
                    section(value)?;
                }
            }
        }
        for family in &self.amplitude_family {
            if let Some(family) = family {
                for value in family {
                    section(value)?;
                }
            }
        }
        if let Some(program) = &self.program {
            section(&program.map)?;
            for birth in &program.births {
                section(birth)?;
            }
        }
        for (r, h) in self.returns.iter().zip(&self.source_overlaps) {
            for s in r {
                section(s)?;
            }
            if let Some(h) = h {
                for s in h {
                    section(s)?;
                }
            }
        }
        Ok(())
    }
    pub fn validate(&self, wire: &OperativeWire, n: usize) -> Result<(), Error> {
        let d = 6 * n;
        let m = d / 2;
        let k = wire.births.len();
        let initial = if wire.declared_origins.is_empty() {
            wire.births
                .iter()
                .filter(|b| b.receiving < wire.activated_at)
                .count()
        } else {
            wire.births.len()
        };
        let validate = |s: &[ResidentSectionRest; 5],
                        covariance: &Option<ResidentSectionRest>,
                        k: usize,
                        factored: bool|
         -> Result<(), Error> {
            for (s, r, w) in [
                (&s[0], if factored { 1 } else { k.max(1) }, 2 * d),
                (&s[1], k.max(1), 4),
                (&s[2], 1, 4),
                (&s[3], 1, 2 * d),
                (&s[4], 1, 8),
            ] {
                point_section(s, r, w)?;
            }
            if let Some(covariance) = covariance {
                point_section(covariance, 1, 4 * m * m)?;
            }
            if wides(&s[2].intervals)?
                .iter()
                .chain(wides(&s[4].intervals)?.iter())
                .any(|v| *v < 0)
            {
                return Err(invalid("map/current or moment radius"));
            }
            Ok(())
        };
        validate(
            &self.current,
            &self.covariance[0],
            k,
            wire.factor_program.is_some(),
        )?;
        validate(
            &self.initial,
            &self.covariance[1],
            initial,
            wire.initial_factor_program.is_some(),
        )?;
        let validate_factor = |frame: &OperativeFactorProgramFrame,
                               values: &[ResidentSectionRest; 9],
                               expected_rows: usize|
         -> Result<(), Error> {
            if frame.rows != expected_rows || frame.boundary_components != d {
                return Err(invalid("factor program extent"));
            }
            point_section(&values[0], 1, 2 * (expected_rows + 1))?;
            point_section(&values[1], 1, 2 * frame.nonzeros.max(1))?;
            point_section(&values[2], 1, 4 * frame.nonzeros.max(1))?;
            point_section(&values[3], 1, 2 * (d / 2 + 1))?;
            point_section(&values[4], 1, 2 * frame.nonzeros.max(1))?;
            point_section(&values[5], 1, 4 * frame.nonzeros.max(1))?;
            point_section(&values[6], frame.rank.max(1), 2 * d)?;
            point_section(&values[7], frame.rank.max(1), 4 * expected_rows)?;
            point_section(&values[8], frame.rank.max(1), 2)?;
            Ok(())
        };
        match (&wire.factor_program, &self.factor_program[0]) {
            (Some(frame), Some(values)) => validate_factor(frame, values, k)?,
            (None, None) => {}
            _ => return Err(invalid("factor program presence")),
        }
        let validate_family_shape = |frame: &OperativeFactorProgramFrame,
                                     values: &[ResidentSectionRest; 4],
                                     expected_rows: usize|
         -> Result<(), Error> {
            let group_width = frame
                .group_width
                .ok_or_else(|| invalid("amplitude family metadata"))?;
            if group_width == 0
                || expected_rows == 0
                || expected_rows % group_width != 0
                || frame.rank != 0
            {
                return Err(invalid("amplitude family grouping/rank"));
            }
            point_section(&values[0], 1, 4 * frame.nonzeros.max(1))?;
            point_section(&values[1], 1, 4 * frame.nonzeros.max(1))?;
            point_section(&values[2], 1, 4)?;
            point_section(&values[3], expected_rows / group_width, 6)?;
            let a = wides(&values[3].intervals)?;
            if a.chunks_exact(3)
                .any(|r| r[0] <= 0 || r[1] != 0 || r[2] != 0)
                || wides(&values[2].intervals)?.iter().any(|v| *v < 0)
            {
                return Err(invalid("amplitude family point/bound"));
            }
            Ok(())
        };
        for (frame, family, rows) in [
            (&wire.factor_program, &self.amplitude_family[0], k),
            (
                &wire.initial_factor_program,
                &self.amplitude_family[1],
                initial,
            ),
        ] {
            match (frame, family) {
                (Some(frame), Some(values)) => validate_family_shape(frame, values, rows)?,
                (Some(frame), None) if frame.group_width.is_none() => {}
                (None, None) => {}
                _ => return Err(invalid("amplitude family presence")),
            }
        }
        match (&wire.initial_factor_program, &self.factor_program[1]) {
            (Some(frame), Some(values)) => validate_factor(frame, values, initial)?,
            (None, None) => {}
            _ => return Err(invalid("initial factor program presence")),
        }
        if self.returns.len() != wire.returns || self.source_overlaps.len() != wire.returns {
            return Err(invalid("operative return chronology"));
        }
        match (&wire.map_program, &self.program) {
            (Some(p), Some(rest)) => {
                if p.at_cut < wire.activated_at
                    || p.return_count > wire.returns
                    || p.contact_count != wire.contact_count_at(p.at_cut)
                    || rest.births.len() != wire.births.len() - p.contact_count
                {
                    return Err(invalid("map program anchor"));
                }
                point_section(&rest.map, p.contact_count.max(1), 2 * d)?;
                for birth in &rest.births {
                    point_section(birth, 1, 2 * d)?;
                }
                for i in 0..wire.returns {
                    let frame = wire.frame(i);
                    if (i < p.return_count
                        && (frame.at_cut > p.at_cut || frame.source_overlap.is_some()))
                        || (i >= p.return_count && frame.at_cut < p.at_cut)
                    {
                        return Err(invalid("map program return cut"));
                    }
                }
            }
            (None, None) => {}
            _ => return Err(invalid("map program presence")),
        }
        if !wire.return_frames.is_empty() && wire.return_frames.len() != wire.returns {
            return Err(invalid("operative return frames"));
        }
        let mut cut = wire.activated_at;
        for (i, r) in self.returns.iter().enumerate() {
            let frame = wire.frame(i);
            if frame.at_cut < cut || frame.contact_count != wire.contact_count_at(frame.at_cut) {
                return Err(invalid("operative return population or order"));
            }
            cut = frame.at_cut;
            let initial = frame.contact_count;
            let factors = frame.factor_count.unwrap_or(initial);
            if factors > initial {
                return Err(invalid("return factor domain"));
            }
            if frame.bound_kind == NativeOperativeBoundKind::FactorBalls
                && (initial == 0
                    || frame.realization != NativeContactRealization::DyadicDeposit
                    || frame.factor_count != Some(initial)
                    || !frame.zero_internal_delta
                    || wire.factor_program.is_none()
                    || frame.source_overlap.is_some()
                    || frame.current_difference_source.is_some())
            {
                return Err(invalid("factor-ball bound interpretation"));
            }
            for (s, rows, w) in [
                (&r[0], 2, 2 * d),
                (
                    &r[1],
                    if frame.current_difference_source.is_some() {
                        1
                    } else {
                        2
                    },
                    4 * factors.max(1),
                ),
                (&r[3], 1, 4),
            ] {
                point_section(s, rows, w)?;
            }
            if frame.zero_internal_delta {
                point_section(&r[2], 1, 1)?;
                if r[2].intervals != [(0, 0)] {
                    return Err(invalid("nonzero implicit internal delta"));
                }
            } else {
                point_section(&r[2], initial.max(1), 4)?;
            }
            if wides(&r[3].intervals)?.iter().any(|v| *v < 0) {
                return Err(invalid("returned radius"));
            }
            match (&frame.source_overlap, &self.source_overlaps[i]) {
                (Some(h), Some(values)) => {
                    if wire.map_program.is_none()
                        || h.source < wire.activated_at
                        || h.source.checked_add(1).is_none_or(|s| s >= frame.at_cut)
                        || h.count > factors
                        || h.count > wire.births.partition_point(|b| b.receiving <= h.source)
                    {
                        return Err(invalid("source overlap domain"));
                    }
                    point_section(&values[0], h.count.max(1), 4)?;
                    point_section(&values[1], h.count.max(1), 2)?;
                    if wides(&values[1].intervals)?.iter().any(|v| *v < 0) {
                        return Err(invalid("source overlap radius"));
                    }
                }
                (None, None) => {}
                _ => return Err(invalid("source overlap presence")),
            }
        }
        Ok(())
    }
}
impl<'c> OperativeState<'c> {
    pub(in super::super::super) fn wire(&self) -> OperativeWire {
        OperativeWire {
            activated_at: self.activated_at,
            propagate_from: self.propagate_from,
            births: self.births.clone(),
            declared_origins: self.declared_origins.clone(),
            dense_covariance: false,
            factor_program: self.sections.factor_program.as_ref().map(|program| {
                OperativeFactorProgramFrame {
                    rows: program.rows,
                    boundary_components: program.boundary_components,
                    rank: program.rank,
                    nonzeros: program.nonzeros,
                    group_width: program.amplitude_family.as_ref().map(|f| f.group_width),
                }
            }),
            initial_factor_program: self.initial.factor_program.as_ref().map(|program| {
                OperativeFactorProgramFrame {
                    rows: program.rows,
                    boundary_components: program.boundary_components,
                    rank: program.rank,
                    nonzeros: program.nonzeros,
                    group_width: program.amplitude_family.as_ref().map(|f| f.group_width),
                }
            }),
            returns: self.returns.len(),
            map_program: self.program.as_ref().map(|p| OperativeMapProgramFrame {
                at_cut: p.at_cut,
                return_count: p.return_count,
                contact_count: p.contact_count,
            }),
            return_frames: self
                .returns
                .iter()
                .map(|r| OperativeReturnFrame {
                    at_cut: r.at_cut,
                    contact_count: r.contact_count,
                    factor_count: (r.bound_kind() == NativeOperativeBoundKind::FactorBalls
                        || r.factor_count != r.contact_count)
                        .then_some(r.factor_count),
                    current_difference_source: r.current_difference_source,
                    source_overlap: r.source_overlap.as_ref().map(|h| {
                        OperativeSourceOverlapFrame {
                            source: h.source,
                            count: h.count,
                        }
                    }),
                    zero_internal_delta: r.b.is_none(),
                    realization: r.realization,
                    bound_kind: r.bound_kind(),
                })
                .collect(),
        }
    }
    pub(in super::super::super) fn rest(
        &self,
        surface: &ResidentSurface<'c>,
    ) -> Result<OperativeRest, Error> {
        let read = |s: &ResidentSection<'c>| surface.detach_section(s, 64).map_err(Error::from);
        let sections = |s: &OperativeSections<'c>| -> Result<
            ([ResidentSectionRest; 5], Option<ResidentSectionRest>),
            Error,
        > {
            Ok((
                [
                    read(&s.map)?,
                    read(&s.b)?,
                    read(&s.bounds)?,
                    read(&s.aggregate)?,
                    read(&s.moment_bounds)?,
                ],
                None,
            ))
        };
        let (current, _) = sections(&self.sections)?;
        let (initial, _) = sections(&self.initial)?;
        let factor_program = self
            .sections
            .factor_program
            .as_ref()
            .map(|program| {
                Ok::<_, Error>([
                    read(&program.row_offsets)?,
                    read(&program.columns)?,
                    read(&program.values)?,
                    read(&program.transpose_offsets)?,
                    read(&program.transpose_rows)?,
                    read(&program.transpose_values)?,
                    read(&program.left)?,
                    read(&program.right)?,
                    read(&program.defects)?,
                ])
            })
            .transpose()?;
        let initial_factor_program = self
            .initial
            .factor_program
            .as_ref()
            .map(|program| {
                Ok::<_, Error>([
                    read(&program.row_offsets)?,
                    read(&program.columns)?,
                    read(&program.values)?,
                    read(&program.transpose_offsets)?,
                    read(&program.transpose_rows)?,
                    read(&program.transpose_values)?,
                    read(&program.left)?,
                    read(&program.right)?,
                    read(&program.defects)?,
                ])
            })
            .transpose()?;
        let family = |program: Option<&Rc<OperativeFactorProgram<'c>>>| {
            program
                .and_then(|p| p.amplitude_family.as_ref())
                .map(|f| {
                    Ok::<_, Error>([
                        read(&f.template_values)?,
                        read(&f.template_transpose_values)?,
                        read(&f.template_bounds)?,
                        read(&f.amplitudes)?,
                    ])
                })
                .transpose()
        };
        Ok(OperativeRest {
            program: self
                .program
                .as_ref()
                .map(|p| {
                    Ok::<_, Error>(OperativeMapProgramRest {
                        map: read(&p.map)?,
                        births: p.births.iter().map(|b| read(b)).collect::<Result<_, _>>()?,
                    })
                })
                .transpose()?,
            source_overlaps: self
                .returns
                .iter()
                .map(|r| {
                    r.source_overlap
                        .as_ref()
                        .map(|h| Ok::<_, Error>([read(&h.coefficients)?, read(&h.errors)?]))
                        .transpose()
                })
                .collect::<Result<_, _>>()?,
            current,
            initial,
            covariance: [None, None],
            factor_program: [factor_program, initial_factor_program],
            amplitude_family: [
                family(self.sections.factor_program.as_ref())?,
                family(self.initial.factor_program.as_ref())?,
            ],
            returns: self
                .returns
                .iter()
                .map(|r| {
                    Ok([
                        read(&r.ports)?,
                        read(&r.currents)?,
                        match &r.b {
                            Some(b) => read(b)?,
                            None => {
                                ResidentSectionRest::found(1, 1, ResidentGrain(0), 64, vec![(0, 0)])
                                    .map_err(invalid)?
                            }
                        },
                        read(&r.bounds)?,
                    ])
                })
                .collect::<Result<_, Error>>()?,
        })
    }
    pub(in super::super::super) fn remount(
        surface: &'c ResidentSurface<'c>,
        wire: OperativeWire,
        rest: OperativeRest,
        grain: u32,
    ) -> Result<Self, Error> {
        let mount = |s: ResidentSectionRest| surface.mount_section_rest(&s).map_err(Error::from);
        let OperativeRest {
            current,
            initial,
            covariance: [current_covariance, initial_covariance],
            returns: rest_returns,
            source_overlaps: rest_source_overlaps,
            program: rest_program,
            factor_program: [rest_current_factor, rest_initial_factor],
            amplitude_family: [rest_current_family, rest_initial_family],
        } = rest;
        if let (Some(frame), Some(family)) =
            (wire.factor_program.as_ref(), rest_current_family.as_ref())
        {
            if frame.group_width.is_some() {
                validate_amplitude_family_sections(
                    frame,
                    family,
                    rest_current_factor
                        .as_ref()
                        .ok_or_else(|| invalid("factor family"))?,
                    &current[2],
                    grain,
                    frame.rows,
                    frame.boundary_components,
                )?;
            }
        }
        if let (Some(frame), Some(family)) = (
            wire.initial_factor_program.as_ref(),
            rest_initial_family.as_ref(),
        ) {
            if frame.group_width.is_some() {
                validate_amplitude_family_sections(
                    frame,
                    family,
                    rest_initial_factor
                        .as_ref()
                        .ok_or_else(|| invalid("initial factor family"))?,
                    &initial[2],
                    grain,
                    frame.rows,
                    frame.boundary_components,
                )?;
            }
        }
        let sections = |s: [ResidentSectionRest; 5],
                        covariance: Option<ResidentSectionRest>|
         -> Result<Rc<OperativeSections<'c>>, Error> {
            let [map, b, bounds, aggregate, moment_bounds] = s;
            Ok(Rc::new(OperativeSections {
                map: Rc::new(mount(map)?),
                b: Rc::new(mount(b)?),
                bounds: Rc::new(mount(bounds)?),
                covariance: {
                    let cell = std::cell::OnceCell::new();
                    if let Some(covariance) = covariance {
                        cell.set(DenseCovariance {
                            matrix: mount(covariance)?,
                            bound: surface.fresh_section(1, 8, ResidentGrain(0))?,
                        })
                        .map_err(|_| Error::Uncertain)?;
                    }
                    cell
                },
                aggregate: mount(aggregate)?,
                moment_bounds: mount(moment_bounds)?,
                factor_program: None,
            }))
        };
        let program = match (wire.map_program.as_ref(), rest_program) {
            (Some(p), Some(rest)) => Some(OperativeMapProgram {
                at_cut: p.at_cut,
                return_count: p.return_count,
                contact_count: p.contact_count,
                map: Rc::new(mount(rest.map)?),
                births: rest
                    .births
                    .into_iter()
                    .map(|b| mount(b).map(Rc::new))
                    .collect::<Result<_, _>>()?,
            }),
            (None, None) => None,
            _ => return Err(invalid("map program presence")),
        };
        let current_family = match (
            wire.factor_program.as_ref().and_then(|f| f.group_width),
            rest_current_family,
        ) {
            (
                Some(group_width),
                Some(
                    [
                        template_values,
                        template_transpose_values,
                        template_bounds,
                        amplitudes,
                    ],
                ),
            ) => Some(Rc::new(DeclaredAmplitudeFamily {
                group_width,
                template_values: Rc::new(mount(template_values)?),
                template_transpose_values: Rc::new(mount(template_transpose_values)?),
                template_bounds: Rc::new(mount(template_bounds)?),
                amplitudes: Rc::new(mount(amplitudes)?),
            })),
            (None, None) => None,
            _ => return Err(invalid("amplitude family presence")),
        };
        let initial_family = match (
            wire.initial_factor_program
                .as_ref()
                .and_then(|f| f.group_width),
            rest_initial_family,
        ) {
            (
                Some(group_width),
                Some(
                    [
                        template_values,
                        template_transpose_values,
                        template_bounds,
                        amplitudes,
                    ],
                ),
            ) => Some(Rc::new(DeclaredAmplitudeFamily {
                group_width,
                template_values: Rc::new(mount(template_values)?),
                template_transpose_values: Rc::new(mount(template_transpose_values)?),
                template_bounds: Rc::new(mount(template_bounds)?),
                amplitudes: Rc::new(mount(amplitudes)?),
            })),
            (None, None) => None,
            _ => return Err(invalid("initial amplitude family presence")),
        };
        let factor_program = match (wire.factor_program.clone(), rest_current_factor) {
            (
                Some(frame),
                Some(
                    [
                        row_offsets,
                        columns,
                        values,
                        transpose_offsets,
                        transpose_rows,
                        transpose_values,
                        left,
                        right,
                        defects,
                    ],
                ),
            ) => Some(Rc::new(OperativeFactorProgram {
                row_offsets: Rc::new(mount(row_offsets)?),
                columns: Rc::new(mount(columns)?),
                values: Rc::new(mount(values)?),
                transpose_offsets: Rc::new(mount(transpose_offsets)?),
                transpose_rows: Rc::new(mount(transpose_rows)?),
                transpose_values: Rc::new(mount(transpose_values)?),
                left: Rc::new(mount(left)?),
                right: Rc::new(mount(right)?),
                defects: Rc::new(mount(defects)?),
                rows: frame.rows,
                boundary_components: frame.boundary_components,
                rank: frame.rank,
                nonzeros: frame.nonzeros,
                amplitude_family: current_family,
            })),
            (None, None) => None,
            _ => return Err(invalid("factor program presence")),
        };
        let initial_factor_program =
            match (wire.initial_factor_program.clone(), rest_initial_factor) {
                (Some(frame), Some(values)) => Some(Rc::new(OperativeFactorProgram {
                    row_offsets: Rc::new(mount(values[0].clone())?),
                    columns: Rc::new(mount(values[1].clone())?),
                    values: Rc::new(mount(values[2].clone())?),
                    transpose_offsets: Rc::new(mount(values[3].clone())?),
                    transpose_rows: Rc::new(mount(values[4].clone())?),
                    transpose_values: Rc::new(mount(values[5].clone())?),
                    left: Rc::new(mount(values[6].clone())?),
                    right: Rc::new(mount(values[7].clone())?),
                    defects: Rc::new(mount(values[8].clone())?),
                    rows: frame.rows,
                    boundary_components: frame.boundary_components,
                    rank: frame.rank,
                    nonzeros: frame.nonzeros,
                    amplitude_family: initial_family,
                })),
                (None, None) => None,
                _ => return Err(invalid("initial factor program presence")),
            };
        let mut current_sections = sections(current, current_covariance)?;
        Rc::get_mut(&mut current_sections)
            .ok_or(Error::Uncertain)?
            .factor_program = factor_program.clone();
        let mut initial_sections = sections(initial, initial_covariance)?;
        Rc::get_mut(&mut initial_sections)
            .ok_or(Error::Uncertain)?
            .factor_program = initial_factor_program;
        if current_sections.factor_program.is_some() {
            current_sections.refresh_factor_aggregate(surface, grain)?;
        }
        if initial_sections.factor_program.is_some() {
            initial_sections.refresh_factor_aggregate(surface, grain)?;
        }
        let returns = rest_returns
            .into_iter()
            .zip(rest_source_overlaps)
            .enumerate()
            .map(|(i, (r, h))| {
                let frame = wire.frame(i);
                let [ports, currents, b, bounds] = r;
                // Cold-wire inspection is a representation check. It changes no current,
                // coefficient, error bound or chronology, and never reads hot semantic state.
                let b = if frame.zero_internal_delta || b.intervals.iter().all(|v| *v == (0, 0)) {
                    None
                } else {
                    Some(Rc::new(mount(b)?))
                };
                Ok(Rc::new(OperativeReturn {
                    source_overlap: match (frame.source_overlap, h) {
                        (Some(h), Some([coefficients, errors])) => Some(OperativeSourceOverlap {
                            source: h.source,
                            count: h.count,
                            coefficients: Rc::new(mount(coefficients)?),
                            errors: Rc::new(mount(errors)?),
                        }),
                        (None, None) => None,
                        _ => return Err(invalid("source overlap presence")),
                    },
                    at_cut: frame.at_cut,
                    contact_count: frame.contact_count,
                    factor_count: frame.factor_count.unwrap_or(frame.contact_count),
                    current_difference_source: frame.current_difference_source,
                    realization: frame.realization,
                    bound_kind: frame.bound_kind,
                    origin: Rc::new(()),
                    ports: Rc::new(mount(ports)?),
                    currents: Rc::new(mount(currents)?),
                    b,
                    bounds: Rc::new(mount(bounds)?),
                }))
            })
            .collect::<Result<Vec<_>, Error>>()?;
        Ok(Self {
            recent_producers: Default::default(),
            recent_propagations: Default::default(),
            propagate_from: wire.propagate_from,
            sections: current_sections,
            initial: initial_sections,
            activated_at: wire.activated_at,
            grain,
            births: wire.births,
            declared_origins: wire.declared_origins,
            origin: Rc::new(()),
            returns,
            program,
        })
    }
}

impl<'c> HeldOperative<'c> {
    pub(in super::super::super) fn rest(
        &self,
        surface: &ResidentSurface<'c>,
    ) -> Result<OperativeHistoryRest, Error> {
        Ok(OperativeHistoryRest {
            count: self.count,
            b: surface.detach_section(&self.b, 64)?,
            bounds: surface.detach_section(&self.bounds, 64)?,
            trace: surface.detach_section(&self.trace, 64)?,
            propagation_input_bounds: self
                .propagation_input_bounds
                .as_ref()
                .map(|b| surface.detach_section(b, 64))
                .transpose()?,
        })
    }
    pub(in super::super::super) fn mount(
        surface: &'c ResidentSurface<'c>,
        rest: OperativeHistoryRest,
    ) -> Result<Self, Error> {
        Ok(Self {
            count: rest.count,
            b: Rc::new(surface.mount_section_rest(&rest.b)?),
            bounds: Rc::new(surface.mount_section_rest(&rest.bounds)?),
            trace: Rc::new(surface.mount_section_rest(&rest.trace)?),
            propagation_input_bounds: rest
                .propagation_input_bounds
                .map(|b| surface.mount_section_rest(&b).map(Rc::new))
                .transpose()?,
        })
    }
}
