//! Complete local normal material at rest. The legacy wave codec retains its meaning;
//! arbitrary feature charts carry their actual extent. Validation does not replay observations.
use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{
    blob, expect, point_bytes, read_blob, read_point,
};
use std::io::{Read, Write};
const MAGIC: &[u8] = b"HOLONIC-NORMAL-MATERIAL";
#[derive(Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    source_chart: NormalSourceChart,
    targets: usize,
    grain: u32,
    observations: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    prior: Option<NativeNormalPrior>,
}
// Version-one wire chart only; the live/rest owner stores one source declaration.
#[derive(serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct WaveHeader {
    roots: usize,
    targets: usize,
    grain: u32,
    observations: u64,
}
#[derive(Debug, PartialEq, Eq)]
pub struct NormalMaterialRest {
    header: Header,
    state: ResidentSectionRest,
}
impl NormalMaterialRest {
    /// Wave roots are absent (zero) for a general feature chart.
    pub fn roots(&self) -> usize {
        self.header.source_chart.wave_roots().unwrap_or(0)
    }
    pub fn source_chart(&self) -> NormalSourceChart {
        self.header.source_chart
    }
    pub fn targets(&self) -> usize {
        self.header.targets
    }
    pub fn grain(&self) -> ResidentGrain {
        ResidentGrain(self.header.grain)
    }
    pub fn observations(&self) -> u64 {
        self.header.observations
    }
    pub fn prior(&self) -> Option<&NativeNormalPrior> {
        self.header.prior.as_ref()
    }
    pub fn state(&self) -> &ResidentSectionRest {
        &self.state
    }
    /// Legacy three-port ingress; the mathematical checks do not authenticate observation origin.
    pub fn from_state_data(
        roots: usize,
        targets: usize,
        grain: ResidentGrain,
        observations: u64,
        state: ResidentSectionRest,
    ) -> Result<Self, ConstitutiveFibreError> {
        Self::from_chart_state_data(
            NormalSourceChart::Wave { roots },
            targets,
            grain,
            observations,
            state,
        )
    }
    pub fn from_chart_state_data(
        source_chart: NormalSourceChart,
        targets: usize,
        grain: ResidentGrain,
        observations: u64,
        state: ResidentSectionRest,
    ) -> Result<Self, ConstitutiveFibreError> {
        source_chart.layout(targets)?;
        if !(1..=120).contains(&grain.0) {
            return Err(ConstitutiveFibreError::Shape);
        }
        Self::from_chart_state_data_with_prior(
            source_chart,
            targets,
            grain,
            observations,
            state,
            None,
        )
    }
    fn from_chart_state_data_with_prior(
        source_chart: NormalSourceChart,
        targets: usize,
        grain: ResidentGrain,
        observations: u64,
        state: ResidentSectionRest,
        prior: Option<NativeNormalPrior>,
    ) -> Result<Self, ConstitutiveFibreError> {
        source_chart.layout(targets)?;
        if !(1..=120).contains(&grain.0) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let value = Self {
            header: Header {
                source_chart,
                targets,
                grain: grain.0,
                observations,
                prior,
            },
            state,
        };
        value.validate()?;
        Ok(value)
    }
    /// Snapshot an admitted wave cut without solving its mathematical domain again.
    pub(super) fn from_native_state(
        roots: usize,
        targets: usize,
        grain: ResidentGrain,
        observations: u64,
        state: ResidentSectionRest,
    ) -> Result<Self, ConstitutiveFibreError> {
        Self::from_native_chart(
            NormalSourceChart::Wave { roots },
            targets,
            grain,
            observations,
            state,
        )
    }
    fn from_native_chart(
        source_chart: NormalSourceChart,
        targets: usize,
        grain: ResidentGrain,
        observations: u64,
        state: ResidentSectionRest,
    ) -> Result<Self, ConstitutiveFibreError> {
        Self::from_native_chart_with_prior(source_chart, targets, grain, observations, state, None)
    }
    fn from_native_chart_with_prior(
        source_chart: NormalSourceChart,
        targets: usize,
        grain: ResidentGrain,
        observations: u64,
        state: ResidentSectionRest,
        prior: Option<NativeNormalPrior>,
    ) -> Result<Self, ConstitutiveFibreError> {
        point_section(&state, 1, source_chart.layout(targets)?.state_words)?;
        Ok(Self {
            header: Header {
                source_chart,
                targets,
                grain: grain.0,
                observations,
                prior,
            },
            state,
        })
    }
    pub fn validate(&self) -> Result<(), ConstitutiveFibreError> {
        let h = &self.header;
        let value = decode_state_layout(
            &self.state,
            h.source_chart.layout(h.targets)?,
            h.targets,
            h.grain,
        )?;
        if let Some(prior) = &h.prior {
            let mut data = value.clone();
            let prior_energy: Rat = prior
                .cross_source
                .iter()
                .flatten()
                .map(ExactComplexWaveCurrent::norm_square)
                .sum();
            if prior_energy != prior.target_energy || data.target_energy < prior.target_energy {
                return Err(invalid(
                    "normal prior energy does not match its coefficient seed",
                ));
            }
            if data.cross_source.len() != prior.cross_source.len()
                || data
                    .cross_source
                    .iter()
                    .any(|row| row.len() != prior.source_complex())
            {
                return Err(ConstitutiveFibreError::Shape);
            }
            for (row, p) in data.cross_source.iter_mut().zip(&prior.cross_source) {
                for (b, b0) in row.iter_mut().zip(p) {
                    *b = b.subtract(b0);
                }
            }
            // The resident scalar is Q_data+C₀ for the kernel's augmented
            // reference bound; the cold geometry validator consumes Q_data.
            data.target_energy -= &prior.target_energy;
            validate_geometry(&data, h.observations)?;
        } else {
            validate_geometry(&value, h.observations)?;
        }
        // Geometry uses observed increments after subtracting B0/C0. The numerical
        // witness uses the COMPLETE H/B and augmented energy Q_data+C0, exactly as
        // the native coefficient solve does, including for an unobserved nonzero prior.
        let layout = h.source_chart.layout(h.targets)?;
        let numeric = wides(&self.state.intervals[..layout.matrix_words])?;
        let error = numeric[layout.cross_values];
        let moments = (0..layout.gram_values + layout.cross_values + STATISTIC_SCALARS)
            .map(|i| {
                let start = layout.matrix_words + MomentWire::WORDS * i;
                integer(&self.state.intervals[start..start + MomentWire::WORDS])
            })
            .collect::<Result<Vec<_>, _>>()?;
        validate_numerical_witness_layout(&self.state, layout, h.targets, h.grain, error, &moments)
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        out.write_all(MAGIC).map_err(invalid)?;
        if let NormalSourceChart::Wave { roots } = self.header.source_chart {
            out.write_all(&[1]).map_err(invalid)?;
            let h = WaveHeader {
                roots,
                targets: self.targets(),
                grain: self.header.grain,
                observations: self.observations(),
            };
            blob(out, &serde_json::to_vec(&h).map_err(invalid)?)?;
        } else {
            out.write_all(&[2]).map_err(invalid)?;
            blob(out, &serde_json::to_vec(&self.header).map_err(invalid)?)?;
        }
        blob(out, &point_bytes(&self.state)?)
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut input = input.take(octets);
        expect(&mut input, MAGIC)?;
        let mut version = [0u8];
        input.read_exact(&mut version).map_err(invalid)?;
        let header = match version[0] {
            1 => {
                let h: WaveHeader =
                    serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
                Header {
                    source_chart: NormalSourceChart::Wave { roots: h.roots },
                    targets: h.targets,
                    grain: h.grain,
                    observations: h.observations,
                    prior: None,
                }
            }
            2 => serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?,
            _ => return Err(invalid("unsupported normal source chart version")),
        };
        let state = read_point(&read_blob(&mut input)?)?;
        if input.limit() != 0 {
            return Err(invalid("trailing normal material bytes"));
        }
        Self::from_chart_state_data_with_prior(
            header.source_chart,
            header.targets,
            ResidentGrain(header.grain),
            header.observations,
            state,
            header.prior,
        )
    }
    pub fn remount<'c>(
        self,
        surface: &'c ResidentSurface<'c>,
    ) -> Result<ResidentNormalMaterial<'c>, ConstitutiveFibreError> {
        let state = surface.mount_section_rest(&self.state)?;
        Ok(ResidentNormalMaterial {
            surface,
            state: Rc::new(state),
            source_chart: self.header.source_chart,
            targets: self.header.targets,
            grain: ResidentGrain(self.header.grain),
            observations: self.header.observations,
            prior: self.header.prior.clone(),
        })
    }
}
impl ResidentNormalMaterial<'_> {
    pub fn rest(&self) -> Result<NormalMaterialRest, ConstitutiveFibreError> {
        NormalMaterialRest::from_native_chart_with_prior(
            self.source_chart,
            self.targets,
            self.grain,
            self.observations,
            self.state_wire()?,
            self.prior.clone(),
        )
    }
}

/// G=H-I must be a source Gram, B must annihilate its null space, and C must pay the
/// minimal compatible target energy. Real charts avoid a redundant realification.
fn validate_geometry(
    value: &NativeNormalMaterialState,
    observations: u64,
) -> Result<(), ConstitutiveFibreError> {
    use crate::inertia::{SymmetricForm, positive_source_energy};
    let m = value.source_normal.len();
    if m == 0 || value.source_normal.iter().any(|row| row.len()!=m)
        || value.cross_source.iter().any(|row| row.len()!=m) {
        return Err(invalid("normal geometry dimensions"));
    }
    if [
        &value.source_normal_error,
        &value.cross_source_error,
        &value.target_energy,
        &value.target_energy_error,
    ]
    .iter()
    .any(|v| v.is_negative())
    {
        return Err(invalid("negative normal moment bound"));
    }
    if observations == 0 {
        // No data increments means the supplied geometry is exactly H0=I, B_data=0,
        // Q_data=0. This establishes the same full null-fibre condition without forming
        // an expanded zero Schur problem. The applied coefficient witness is checked
        // separately by validate_numerical_witness_layout, including nonzero priors.
        if value.source_normal.iter().enumerate().any(|(i, row)| {
            row.len() != m
                || row.iter().enumerate().any(|(j, z)| {
                    !z.imaginary.is_zero()
                        || z.real != if i == j { Rat::one() } else { Rat::zero() }
                })
        }) || value.cross_source.iter().flatten().any(|z| !z.is_zero())
            || !value.target_energy.is_zero()
            || !value.source_normal_error.is_zero()
            || !value.cross_source_error.is_zero()
            || !value.target_energy_error.is_zero()
        {
            return Err(invalid(
                "unobserved normal geometry differs from its declared prior",
            ));
        }
        return Ok(());
    }
    let mut g = value.source_normal.clone();
    for i in 0..m {
        for j in 0..m {
            if g[i][j] != g[j][i].conjugate() {
                return Err(invalid("non-Hermitian source Gram"));
            }
        }
    }
    for i in 0..m {
        g[i][i].real -= Rat::one();
    }
    let real = g.iter().flatten().all(|v| v.imaginary.is_zero());
    let width = if real { m } else { 2 * m };
    let matrix: Vec<Vec<Rat>> = (0..width)
        .map(|i| {
            (0..width)
                .map(|j| {
                    if real {
                        g[i][j].real.clone()
                    } else {
                        let z = &g[i / 2][j / 2];
                        match (i % 2, j % 2) {
                            (0, 0) | (1, 1) => z.real.clone(),
                            (0, 1) => -z.imaginary.clone(),
                            _ => z.imaginary.clone(),
                        }
                    }
                })
                .collect()
        })
        .collect();
    let mut rhs = Vec::new();
    for row in &value.cross_source {
        if real {
            for imaginary in [false, true] {
                let r: Vec<Rat> = row
                    .iter()
                    .map(|v| {
                        if imaginary {
                            v.imaginary.clone()
                        } else {
                            v.real.clone()
                        }
                    })
                    .collect();
                if r.iter().any(|v| !v.is_zero()) {
                    rhs.push(r);
                }
            }
        } else {
            let r: Vec<Rat> = row
                .iter()
                .flat_map(|v| [v.real.clone(), -v.imaginary.clone()])
                .collect();
            if r.iter().any(|v| !v.is_zero()) {
                rhs.push(r);
            }
        }
    }
    let form = SymmetricForm::from_rows(matrix).map_err(invalid)?;
    let compatibility =
        positive_source_energy(&form, &rhs, &value.target_energy).map_err(invalid)?;
    let rank = if real {
        compatibility.source_rank
    } else {
        compatibility.source_rank / 2
    };
    if rank as u64 > observations {
        return Err(invalid("source rank exceeds observation population"));
    }
    let extra = compatibility.remaining_target_energy;
    if extra.is_negative() || (extra > Rat::zero() && observations <= rank as u64) {
        return Err(invalid(
            "target energy is incompatible with source geometry",
        ));
    }
    if observations == 0
        && [
            &value.source_normal_error,
            &value.cross_source_error,
            &value.target_energy_error,
        ]
        .iter()
        .any(|v| !v.is_zero())
    {
        return Err(invalid("unobserved normal family has accumulated errors"));
    }
    Ok(())
}

#[cfg(test)]
mod tests;
