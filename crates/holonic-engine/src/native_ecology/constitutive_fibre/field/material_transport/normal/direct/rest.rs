//! Complete local normal material at rest. Read-time validation uses the existing exact
//! inertia/source-energy owner; it does not replay observations or refit coefficients.
use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{
    blob, expect, point_bytes, read_blob, read_point,
};
use std::io::{Read, Write};

const MAGIC: &[u8] = b"HOLONIC-NORMAL-MATERIAL\x01";
#[derive(Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    roots: usize,
    targets: usize,
    grain: u32,
    observations: u64,
}
/// Its private fields have passed the mathematical-domain and numerical-witness checks.
#[derive(Debug, PartialEq, Eq)]
pub struct NormalMaterialRest {
    header: Header,
    state: ResidentSectionRest,
}

impl NormalMaterialRest {
    pub fn roots(&self) -> usize {
        self.header.roots
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
    pub fn state(&self) -> &ResidentSectionRest {
        &self.state
    }
    /// Import a declared normal chart. This checks its compatible moment domain and actual
    /// stored operator residual; it cannot authenticate the exterior origin of observations.
    pub fn from_state_data(
        roots: usize,
        targets: usize,
        grain: ResidentGrain,
        observations: u64,
        state: ResidentSectionRest,
    ) -> Result<Self, ConstitutiveFibreError> {
        if roots == 0 || targets == 0 || !(1..=120).contains(&grain.0) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let result = Self {
            header: Header {
                roots,
                targets,
                grain: grain.0,
                observations,
            },
            state,
        };
        result.validate()?;
        Ok(result)
    }
    /// Snapshot an already admitted native material cut. Cold wire ingress still uses
    /// `from_state_data` and validates its mathematical domain; a retained producing cut need
    /// not solve that domain again merely to be written at rest.
    pub(super) fn from_native_state(
        roots: usize,
        targets: usize,
        grain: ResidentGrain,
        observations: u64,
        state: ResidentSectionRest,
    ) -> Result<Self, ConstitutiveFibreError> {
        point_section(&state, 1, state_words(roots, targets).ok_or(ConstitutiveFibreError::Shape)?)?;
        Ok(Self {
            header: Header { roots, targets, grain: grain.0, observations },
            state,
        })
    }
    pub fn validate(&self) -> Result<(), ConstitutiveFibreError> {
        let h = &self.header;
        let value = decode_state(&self.state, h.roots, h.targets, h.grain)?;
        validate_geometry(&value, h.observations)?;
        let layout = NormalLayout::new(h.roots, h.targets).ok_or(ConstitutiveFibreError::Shape)?;
        let numeric = wides(&self.state.intervals[..layout.matrix_words])?;
        let values = layout.gram_values + layout.cross_values + STATISTIC_SCALARS;
        let moments = (0..values)
            .map(|i| {
                let start = layout.matrix_words + MomentWire::WORDS * i;
                integer(&self.state.intervals[start..start + MomentWire::WORDS])
            })
            .collect::<Result<Vec<_>, _>>()?;
        validate_numerical_witness(
            &self.state,
            h.roots,
            h.targets,
            h.grain,
            numeric[layout.cross_values],
            &moments,
        )
    }

    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        out.write_all(MAGIC).map_err(invalid)?;
        blob(out, &serde_json::to_vec(&self.header).map_err(invalid)?)?;
        blob(out, &point_bytes(&self.state)?)
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut input = input.take(octets);
        expect(&mut input, MAGIC)?;
        let header: Header = serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        let state = read_point(&read_blob(&mut input)?)?;
        if input.limit() != 0 {
            return Err(invalid("trailing normal material bytes"));
        }
        Self::from_state_data(
            header.roots,
            header.targets,
            ResidentGrain(header.grain),
            header.observations,
            state,
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
            roots: self.header.roots,
            targets: self.header.targets,
            grain: ResidentGrain(self.header.grain),
            observations: self.header.observations,
        })
    }
}
impl ResidentNormalMaterial<'_> {
    pub fn rest(&self) -> Result<NormalMaterialRest, ConstitutiveFibreError> {
        // Native construction and validated remount are the only ways to obtain this owner.
        // Cold ingress validates the mathematical domain; ordinary persistence need not solve
        // that same domain again. Its private rest cannot be mutated after construction.
        let state = self.state_wire()?;
        point_section(
            &state,
            1,
            state_words(self.roots, self.targets).ok_or(ConstitutiveFibreError::Shape)?,
        )?;
        Ok(NormalMaterialRest {
            header: Header {
                roots: self.roots,
                targets: self.targets,
                grain: self.grain.0,
                observations: self.observations,
            },
            state,
        })
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
