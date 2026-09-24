use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{
    blob, point_bytes, point_section, read_blob, read_point,
};
use std::io::{Read, Write};
const MAGIC: &[u8] = b"HNA-FIELD-CURRENT-SOURCE-REST\x01";
fn invalid(s: impl std::fmt::Display) -> Error {
    Error::Rest(format!("field current source: {s}"))
}

/// Immutable producing sections for an outstanding comparison, without a second live field.
#[derive(Debug, PartialEq, Eq)]
pub struct NativeFieldCurrentSourceRest {
    cut: usize,
    grain: u32,
    width: usize,
    births: Vec<NativeOperativeContactBirth>,
    declared_origins: Vec<NativeFieldContactOrigin>,
    dense_covariance: Option<ResidentSectionRest>,
    factor_program: Option<[ResidentSectionRest; 9]>,
    factor_rows: Option<usize>,
    factor_rank: Option<usize>,
    factor_nonzeros: Option<usize>,
    amplitude_group_width: Option<usize>,
    amplitude_family: Option<[ResidentSectionRest; 4]>,
    packed: ResidentSectionRest,
    report: ResidentSectionRest,
    producing: [ResidentSectionRest; 5],
}
impl NativeFieldCurrentSourceRest {
    fn validate(&self) -> Result<(), Error> {
        let k = self.births.len();
        let d = self.width.checked_sub(2 * k).ok_or(Error::Shape)?;
        if d == 0
            || d % 6 != 0
            || !(1..=120).contains(&self.grain)
            || (self.declared_origins.is_empty()
                && self
                    .births
                    .iter()
                    .any(|b| b.source >= b.receiving || b.receiving >= self.cut))
        {
            return Err(invalid("source extent/grain/births"));
        }
        if (!self.declared_origins.is_empty() && self.declared_origins.len() != k)
            || self
                .declared_origins
                .iter()
                .enumerate()
                .any(|(column, origin)| {
                    !origin.is_declared() || origin.column() != column || origin.column() >= k
                })
        {
            return Err(invalid("declared contact origins"));
        }
        point_section(&self.packed, 1, 2 * (self.width + 1))?;
        point_section(&self.report, 1, 12 * (d + 1))?;
        for (v, (rows, width)) in self.producing.iter().zip([
            (
                if self.factor_program.is_some() {
                    1
                } else {
                    k.max(1)
                },
                2 * d,
            ),
            (k.max(1), 4),
            (1, 4),
            (1, 2 * d),
            (1, 8),
        ]) {
            point_section(v, rows, width)?;
        }
        let q = wides(&self.packed.intervals)?;
        let report = wides(&self.report.intervals)?;
        let b = wides(&self.producing[1].intervals)?;
        if q[self.width] < 0
            || q[..d] != report[d + 1..2 * d + 1]
            || q[d..self.width] != b[..2 * k]
            || (0..5).any(|j| report[j * (d + 1) + d] < 0)
            || report[6 * (d + 1) - 1] <= 0
            || wides(&self.producing[2].intervals)?.iter().any(|v| *v < 0)
            || wides(&self.producing[4].intervals)?.iter().any(|v| *v < 0)
        {
            return Err(invalid("source/report/internal bounds"));
        }
        if let Some(covariance) = &self.dense_covariance {
            point_section(covariance, 1, d * d)?;
        }
        if let Some(
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
        ) = &self.factor_program
        {
            if self.factor_rows.is_none()
                || self.factor_rank.is_none()
                || self.factor_nonzeros.is_none()
            {
                return Err(invalid("factor metadata is required"));
            }
            let rows = self.factor_rows.unwrap_or(k);
            if rows != k {
                return Err(invalid("factor contact population"));
            }
            let rank = self.factor_rank.unwrap_or(left.rows);
            let nnz = self.factor_nonzeros.unwrap_or(columns.intervals.len() / 2);
            point_section(row_offsets, 1, 2 * (rows + 1))?;
            point_section(columns, 1, 2 * nnz.max(1))?;
            point_section(values, 1, 4 * nnz.max(1))?;
            point_section(transpose_offsets, 1, 2 * (d / 2 + 1))?;
            point_section(transpose_rows, 1, 2 * nnz.max(1))?;
            point_section(transpose_values, 1, 4 * nnz.max(1))?;
            point_section(left, rank.max(1), 2 * d)?;
            point_section(right, rank.max(1), 4 * rows)?;
            point_section(defects, rank.max(1), 2)?;
            if let Some(group_width) = self.amplitude_group_width {
                if group_width == 0 || k == 0 || k % group_width != 0 || rank != 0 {
                    return Err(invalid("amplitude family grouping/rank"));
                }
                let family = self
                    .amplitude_family
                    .as_ref()
                    .ok_or_else(|| invalid("amplitude family"))?;
                point_section(&family[0], 1, 4 * nnz.max(1))?;
                point_section(&family[1], 1, 4 * nnz.max(1))?;
                point_section(&family[2], 1, 4)?;
                point_section(&family[3], k / group_width, 6)?;
                if wides(&family[2].intervals)?.iter().any(|v| *v < 0) {
                    return Err(invalid("amplitude template radius"));
                }
                for row in wides(&family[3].intervals)?.chunks_exact(3) {
                    if row[0] <= 0 || row[1] != 0 || row[2] != 0 {
                        return Err(invalid("amplitude point row"));
                    }
                }
                let frame = super::super::rest::OperativeFactorProgramFrame {
                    rows,
                    boundary_components: d,
                    rank,
                    nonzeros: nnz,
                    group_width: Some(group_width),
                };
                super::super::rest::validate_amplitude_family_sections(
                    &frame,
                    family,
                    &[
                        row_offsets.clone(),
                        columns.clone(),
                        values.clone(),
                        transpose_offsets.clone(),
                        transpose_rows.clone(),
                        transpose_values.clone(),
                        left.clone(),
                        right.clone(),
                        defects.clone(),
                    ],
                    &self.producing[2],
                    self.grain,
                    k,
                    d,
                )?;
            } else if self.amplitude_family.is_some() {
                return Err(invalid("amplitude family metadata"));
            }
        }
        if self.factor_program.is_none()
            && (self.amplitude_group_width.is_some() || self.amplitude_family.is_some())
        {
            return Err(invalid("amplitude family without factor program"));
        }
        Ok(())
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), Error> {
        self.validate()?;
        out.write_all(MAGIC).map_err(invalid)?;
        blob(
            out,
            &serde_json::to_vec(&(
                self.cut,
                self.grain,
                self.width,
                &self.births,
                &self.declared_origins,
                self.dense_covariance.is_some(),
                self.factor_program.is_some(),
                self.factor_rows,
                self.factor_rank,
                self.factor_nonzeros,
                self.amplitude_group_width,
            ))
            .map_err(invalid)?,
        )?;
        for s in std::iter::once(&self.packed)
            .chain(std::iter::once(&self.report))
            .chain(&self.producing)
        {
            blob(out, &point_bytes(s)?)?;
        }
        if let Some(covariance) = &self.dense_covariance {
            blob(out, &point_bytes(covariance)?)?;
        }
        if let Some(factor_program) = &self.factor_program {
            for value in factor_program {
                blob(out, &point_bytes(value)?)?;
            }
        }
        if let Some(family) = &self.amplitude_family {
            for value in family {
                blob(out, &point_bytes(value)?)?;
            }
        }
        Ok(())
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, Error> {
        let mut input = input.take(octets);
        let mut magic = vec![0; MAGIC.len()];
        input.read_exact(&mut magic).map_err(invalid)?;
        if magic != MAGIC {
            return Err(invalid("source witness version"));
        }
        let metadata = read_blob(&mut input)?;
        let values: Vec<serde_json::Value> = serde_json::from_slice(&metadata).map_err(invalid)?;
        if values.len() < 4 || values.len() > 11 {
            return Err(invalid("source witness metadata"));
        }
        let cut = serde_json::from_value(values[0].clone()).map_err(invalid)?;
        let grain = serde_json::from_value(values[1].clone()).map_err(invalid)?;
        let width = serde_json::from_value(values[2].clone()).map_err(invalid)?;
        let births = serde_json::from_value(values[3].clone()).map_err(invalid)?;
        let declared_origins = if values.len() >= 5 {
            serde_json::from_value(values[4].clone()).map_err(invalid)?
        } else {
            Vec::new()
        };
        let legacy_dense = values.len() < 6;
        let dense_covariance = if values.len() >= 6 {
            serde_json::from_value(values[5].clone()).map_err(invalid)?
        } else {
            true
        };
        let factor_program = if values.len() >= 7 {
            serde_json::from_value(values[6].clone()).map_err(invalid)?
        } else {
            false
        };
        let factor_rows: Option<usize> = if values.len() >= 8 {
            serde_json::from_value(values[7].clone()).map_err(invalid)?
        } else {
            None
        };
        let factor_rank: Option<usize> = if values.len() >= 9 {
            serde_json::from_value(values[8].clone()).map_err(invalid)?
        } else {
            None
        };
        let factor_nonzeros: Option<usize> = if values.len() >= 10 {
            serde_json::from_value(values[9].clone()).map_err(invalid)?
        } else {
            None
        };
        let amplitude_group_width: Option<usize> = if values.len() >= 11 {
            serde_json::from_value(values[10].clone()).map_err(invalid)?
        } else {
            None
        };
        let mut sections = Vec::new();
        let base_sections = if legacy_dense || dense_covariance {
            8
        } else {
            7
        };
        for _ in 0..(base_sections
            + usize::from(factor_program) * 9
            + usize::from(amplitude_group_width.is_some()) * 4)
        {
            sections.push(read_point(&read_blob(&mut input)?)?);
        }
        if input.limit() != 0 {
            return Err(invalid("trailing source witness bytes"));
        }
        let packed = sections[0].clone();
        let report = sections[1].clone();
        let (producing, dense_covariance) = if legacy_dense {
            (
                [
                    sections[2].clone(),
                    sections[3].clone(),
                    sections[4].clone(),
                    sections[6].clone(),
                    sections[7].clone(),
                ],
                Some(sections[5].clone()),
            )
        } else {
            (
                [
                    sections[2].clone(),
                    sections[3].clone(),
                    sections[4].clone(),
                    sections[5].clone(),
                    sections[6].clone(),
                ],
                if dense_covariance {
                    Some(sections[7].clone())
                } else {
                    None
                },
            )
        };
        let factor_program = if factor_program {
            Some([
                sections[base_sections].clone(),
                sections[base_sections + 1].clone(),
                sections[base_sections + 2].clone(),
                sections[base_sections + 3].clone(),
                sections[base_sections + 4].clone(),
                sections[base_sections + 5].clone(),
                sections[base_sections + 6].clone(),
                sections[base_sections + 7].clone(),
                sections[base_sections + 8].clone(),
            ])
        } else {
            None
        };
        let family_base = base_sections + usize::from(factor_program.is_some()) * 9;
        let amplitude_family = amplitude_group_width.map(|_| {
            [
                sections[family_base].clone(),
                sections[family_base + 1].clone(),
                sections[family_base + 2].clone(),
                sections[family_base + 3].clone(),
            ]
        });
        let rest = Self {
            cut,
            grain,
            width,
            births,
            declared_origins,
            dense_covariance,
            factor_program,
            factor_rows,
            factor_rank,
            factor_nonzeros,
            amplitude_group_width,
            amplitude_family,
            packed,
            report,
            producing,
        };
        rest.validate()?;
        Ok(rest)
    }
}
impl NativeFieldCurrentSource<'_> {
    pub fn rest(&self) -> Result<NativeFieldCurrentSourceRest, Error> {
        let p = &self._producing;
        let section =
            |s: &ResidentSection<'_>| self.surface.detach_section(s, 64).map_err(Error::from);
        let dense_covariance = None;
        let factor_program = p
            .factor_program
            .as_ref()
            .map(|program| {
                Ok::<_, Error>([
                    self.surface.detach_section(&program.row_offsets, 64)?,
                    self.surface.detach_section(&program.columns, 64)?,
                    self.surface.detach_section(&program.values, 64)?,
                    self.surface
                        .detach_section(&program.transpose_offsets, 64)?,
                    self.surface.detach_section(&program.transpose_rows, 64)?,
                    self.surface.detach_section(&program.transpose_values, 64)?,
                    self.surface.detach_section(&program.left, 64)?,
                    self.surface.detach_section(&program.right, 64)?,
                    self.surface.detach_section(&program.defects, 64)?,
                ])
            })
            .transpose()?;
        let amplitude_group_width = p
            .factor_program
            .as_ref()
            .and_then(|program| program.amplitude_family.as_ref().map(|f| f.group_width));
        let amplitude_family = p
            .factor_program
            .as_ref()
            .and_then(|program| program.amplitude_family.as_ref())
            .map(|f| {
                Ok::<_, Error>([
                    self.surface.detach_section(&f.template_values, 64)?,
                    self.surface
                        .detach_section(&f.template_transpose_values, 64)?,
                    self.surface.detach_section(&f.template_bounds, 64)?,
                    self.surface.detach_section(&f.amplitudes, 64)?,
                ])
            })
            .transpose()?;
        let rest = NativeFieldCurrentSourceRest {
            cut: self.cut,
            grain: self.grain,
            width: self.width,
            births: self.births.clone(),
            declared_origins: self.declared_origins.clone(),
            packed: section(&self.packed)?,
            report: section(&self.report)?,
            producing: [
                section(&p.map)?,
                section(&p.b)?,
                section(&p.bounds)?,
                section(&p.aggregate)?,
                section(&p.moment_bounds)?,
            ],
            dense_covariance,
            factor_program,
            factor_rows: p.factor_program.as_ref().map(|program| program.rows),
            factor_rank: p.factor_program.as_ref().map(|program| program.rank),
            factor_nonzeros: p.factor_program.as_ref().map(|program| program.nonzeros),
            amplitude_group_width,
            amplitude_family,
        };
        rest.validate()?;
        Ok(rest)
    }
}
impl<'c> NativeConstitutiveField<'c> {
    /// Bind the immutable producing witness to the remounted move owner. Its D and current
    /// may precede the contemporary material; replacing them would corrupt delayed gradients.
    pub fn remount_current_source(
        &mut self,
        rest: NativeFieldCurrentSourceRest,
    ) -> Result<NativeFieldCurrentSource<'c>, Error> {
        rest.validate()?;
        let op = self
            .junction
            .as_ref()
            .and_then(|j| j.operative.as_ref())
            .ok_or(Error::Shape)?;
        if rest.cut > self.history.len()
            || rest.grain != op.grain
            || op.births.get(..rest.births.len()) != Some(rest.births.as_slice())
            || rest.width != 6 * self.nodes() + 2 * rest.births.len()
            || (!rest.declared_origins.is_empty()
                && op.declared_origins.get(..rest.declared_origins.len())
                    != Some(rest.declared_origins.as_slice()))
        {
            return Err(invalid("source field/incidence domain"));
        }
        let s = self.relation.surface;
        let mount = |x: &ResidentSectionRest| s.mount_section_rest(x).map_err(Error::from);
        let [map, b, bounds, aggregate, moment_bounds] = &rest.producing;
        let covariance = rest.dense_covariance;
        let factor_program = rest.factor_program;
        let amplitude_family = rest.amplitude_family;
        let contact_count = rest.births.len();
        let producing = Rc::new(OperativeSections {
            map: Rc::new(mount(map)?),
            b: Rc::new(mount(b)?),
            bounds: Rc::new(mount(bounds)?),
            covariance: {
                let cell = std::cell::OnceCell::new();
                if let Some(covariance) = covariance {
                    cell.set(DenseCovariance {
                        matrix: mount(&covariance)?,
                        bound: s.fresh_section(1, 8, ResidentGrain(0))?,
                    })
                    .map_err(|_| Error::Uncertain)?;
                }
                cell
            },
            aggregate: mount(aggregate)?,
            moment_bounds: mount(moment_bounds)?,
            factor_program: factor_program
                .map(
                    |[
                        row_offsets,
                        columns,
                        values,
                        transpose_offsets,
                        transpose_rows,
                        transpose_values,
                        left,
                        right,
                        defects,
                    ]| {
                        Ok::<_, Error>(Rc::new(OperativeFactorProgram {
                            row_offsets: Rc::new(mount(&row_offsets)?),
                            columns: Rc::new(mount(&columns)?),
                            values: Rc::new(mount(&values)?),
                            transpose_offsets: Rc::new(mount(&transpose_offsets)?),
                            transpose_rows: Rc::new(mount(&transpose_rows)?),
                            transpose_values: Rc::new(mount(&transpose_values)?),
                            left: Rc::new(mount(&left)?),
                            right: Rc::new(mount(&right)?),
                            defects: Rc::new(mount(&defects)?),
                            amplitude_family: amplitude_family
                                .map(
                                    |[
                                        template_values,
                                        template_transpose_values,
                                        template_bounds,
                                        amplitudes,
                                    ]| {
                                        Ok::<_, Error>(Rc::new(DeclaredAmplitudeFamily {
                                            group_width: rest.amplitude_group_width.unwrap_or(1),
                                            template_values: Rc::new(mount(&template_values)?),
                                            template_transpose_values: Rc::new(mount(
                                                &template_transpose_values,
                                            )?),
                                            template_bounds: Rc::new(mount(&template_bounds)?),
                                            amplitudes: Rc::new(mount(&amplitudes)?),
                                        }))
                                    },
                                )
                                .transpose()?,
                            rows: rest.factor_rows.unwrap_or(contact_count),
                            boundary_components: 6 * self.nodes(),
                            rank: rest.factor_rank.unwrap_or(left.rows),
                            nonzeros: rest.factor_nonzeros.unwrap_or(columns.intervals.len() / 2),
                        }))
                    },
                )
                .transpose()?,
        });
        if producing.factor_program.is_some() {
            producing.refresh_factor_aggregate(s, rest.grain)?;
        }
        Ok(NativeFieldCurrentSource {
            surface: s,
            owner: Rc::clone(&self.owner),
            cut: rest.cut,
            grain: rest.grain,
            width: rest.width,
            births: rest.births,
            declared_origins: rest.declared_origins,
            packed: Rc::new(mount(&rest.packed)?),
            report: Rc::new(mount(&rest.report)?),
            material: std::cell::OnceCell::new(),
            reflection: std::cell::OnceCell::new(),
            _producing: producing,
        })
    }
}
