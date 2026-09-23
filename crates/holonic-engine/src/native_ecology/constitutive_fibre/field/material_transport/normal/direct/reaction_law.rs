//! The power-neutral reaction law on a learned normal material.
//!
//! [definition; agent-inferred] A reaction material `W` (targets × features) read on the
//! realified feature chart `Φ(s,c) = s ⊕ c ⊕ (c_r s)_r` (`ResidentNormalEnclosureSection::
//! realified_bilinear_enclosed_features`, `r` over the REAL coordinates of `c`) decomposes into
//!
//! - `W_s` (targets × `n`): the linear self-relation on the current `s`;
//! - `W_c` (targets × `k/2`): the contrast port coupling;
//! - `A_r` (targets × `n`, one per real contrast coordinate): the modulated slices, so the
//!   bilinear block is `J(c) s = Σ_r c_r A_r s`.
//!
//! After each normal-law solve (a deposit), [`ResidentNormalMaterial::project_power_neutral_reaction`]
//! holds every `A_r` exactly skew-Hermitian at the grain (`holonic_core::reaction::
//! skew_hermitian_at_grain`; `Holon/Reaction.lean::skewReaction_workless`: `Re⟨s, J(c)s⟩ = 0` for
//! every admitted `c`), and `W_s` passive by the minimal certified scalar shift
//! (`holonic_core::reaction::passive_shift_at_grain`: `W_s − τI`, `τ` the least grain value with
//! `herm W_s − τI ⪯ 0`; its Hermitian part, the resistive element, is `⪯ 0` and its power is
//! `−dissipation`). [agent-inferred; measured] Not the certified congruence clip
//! (`passive_complex_at_grain`, `project_passive`): on learned native blocks that clip removed a
//! part ~10⁴ times the block, leaving a large dissipative `W_s` that the explicit incident word
//! amplified into a runaway; the shift removes at most `λ_max(herm W_s)₊ + 1` grain unit. The joint linear
//! relation on the port pair `(s, c)` is `[[W_s, W_c], [−W_cᴴ, 0]]` with the contrast port's skew
//! return declared (the gyrator completion of the Dirac interconnection); its Hermitian part is
//! `diag(herm W_s, 0)`, so the certified passive projection of the JOINT linear relation acts on
//! `W_s` alone and keeps `W_c` exactly. The implemented word reads `c` from the current and does
//! not enact that return, so the coupling's power `Re⟨s, W_c c⟩` is port power exchanged with the
//! contrast port: its size `‖W_c‖₁` is recorded, not projected.
//!
//! The executed coefficients are replaced; the accumulated normal statistics `H`, `B` are not.
//! The stored numerical witnesses are recomputed for the projected map exactly as the normal-fit
//! kernel and the rest decoder define them: the normal residual `⌈‖W'H − B‖/S²⌉` against the exact
//! `H`, `B`; the coefficient norm `‖W'‖₁`; and the coefficient radius, the certified bound on
//! `‖W' − P‖` (`P` the exact normal solution), `min(⌈(‖W'H−B‖ + ‖W'‖₁ e_H + S e_B)/S²⌉,
//! ‖W'‖₁ + ⌈√(C + e_C)⌉)`. Both bounds hold for any stored `W`, so the projected map keeps a
//! certified distance to the normal solution (the removed parts are part of that distance).
use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::point_section;
use holonic_core::reaction::{
    GridComplex, frobenius_square, l1, passive_shift_at_grain, skew_hermitian_at_grain,
};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{Signed, ToPrimitive, Zero};

/// [definition] One deposit's projection receipt. Every quantity is exact; grain-unit integers
/// are reported as rationals at the material grain. It is a reading, not a gate.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct NormalReactionProjection {
    pub source_complex: usize,
    pub condition_real: usize,
    /// `Σ_r ‖A_r − skew(A_r)‖_F²`: the Hermitian (work-doing) parts removed from the slices.
    pub bilinear_removed_square: Rat,
    /// `Σ_r ‖skew(A_r)‖_F²` retained.
    pub bilinear_retained_square: Rat,
    /// `n₊` of `herm W_s` before projection: the active directions removed.
    pub linear_removed_rank: usize,
    /// `tr(removed) = n τ` of the linear projection (≥ 0).
    pub linear_removed_trace: Rat,
    /// The certified shift `τ` (the least grain value with `herm W_s − τI ⪯ 0`).
    pub linear_shift: Rat,
    /// `−tr(herm W_s')` after projection (≥ 0): the resistive element's dissipation trace.
    pub resistive_trace: Rat,
    /// `‖W_c‖₁`, the contrast port coupling kept under the declared skew return.
    pub port_coupling_l1: Rat,
    /// `‖removed‖₁` over all blocks.
    pub removed_l1: Rat,
    /// The certified coefficient radius `‖W − P‖` before and after the projection.
    pub coefficient_radius_before: Rat,
    pub coefficient_radius_after: Rat,
    pub normal_residual_before: Rat,
    pub normal_residual_after: Rat,
}

/// [definition] **The host certificate of a power-neutral reaction material cut**: every modulated
/// slice `A_r` exactly skew-Hermitian and the linear self-relation `W_s` passive (`herm W_s ⪯ 0`
/// by exact inertia of its realification), bound to the resident state it was read from (the
/// same `Rc`). It is the premise of the Cayley step's certified radius: with it,
/// `herm K(c) ⪯ 0` for every real contrast `c`, so `‖(I − K/2)⁻¹‖ ≤ 1` and the Cayley map is a
/// contraction (`Holon/Cayley.lean::cayley_isometry` on the skew part,
/// `Holon/Cayley.lean::midpoint_reaction_balance` with `R = −herm W_s`). The kernel re-checks
/// slice skewness itself; passivity is read only from this certificate.
#[derive(Clone)]
pub struct PowerNeutralCertificate<'c> {
    pub(crate) state: Rc<ResidentSection<'c>>,
    /// Complex targets `n` (the row's current) and real contrast coordinates `k`.
    pub n: usize,
    pub k: usize,
    /// Inertia of `sym(realify W_s)`: `positive == 0`.
    pub linear_inertia: holonic_core::inertia::Inertia,
    /// The exact executed coefficients (`n × F`, integers at `2^-grain`), for exterior readings
    /// such as the incident energy balance. Never an operand of the resident step.
    pub coefficients: Vec<Vec<GridComplex>>,
    pub grain: u32,
}
impl std::fmt::Debug for PowerNeutralCertificate<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PowerNeutralCertificate")
            .field("n", &self.n)
            .field("k", &self.k)
            .field("linear_inertia", &self.linear_inertia)
            .finish()
    }
}
impl<'c> PowerNeutralCertificate<'c> {
    /// Whether this certificate was read from exactly `view`'s resident state.
    pub fn certifies(&self, view: &ResidentNormalMaterialView<'c>) -> bool {
        Rc::ptr_eq(&self.state, &view.state)
    }
    fn from_words(
        state: Rc<ResidentSection<'c>>,
        numeric: &[i128],
        n: usize,
        k: usize,
        grain: u32,
    ) -> Result<Self, ConstitutiveFibreError> {
        let features = power_neutral_features(n, k)?;
        let block = |columns: std::ops::Range<usize>| -> Vec<Vec<GridComplex>> {
            (0..n)
                .map(|t| {
                    columns
                        .clone()
                        .map(|j| grid(numeric, t, j, features))
                        .collect()
                })
                .collect()
        };
        for r in 0..k {
            let start = n + k / 2 + r * n;
            if !holonic_core::reaction::is_skew_hermitian(&block(start..start + n)) {
                return Err(invalid("power-neutral slice is not exactly skew-Hermitian"));
            }
        }
        let linear_inertia = holonic_core::inertia::inertia(
            &holonic_core::scalar::symmetric_part(
                &holonic_core::reaction::realify(&block(0..n)).map_err(invalid)?,
            )
            .map_err(invalid)?,
        );
        if linear_inertia.positive != 0 {
            return Err(invalid("power-neutral linear self-relation is not passive"));
        }
        Ok(Self {
            state,
            n,
            k,
            linear_inertia,
            coefficients: block(0..features),
            grain,
        })
    }
}

fn power_neutral_features(n: usize, k: usize) -> Result<usize, ConstitutiveFibreError> {
    n.checked_mul(k)
        .and_then(|v| v.checked_add(n)?.checked_add(k / 2))
        .filter(|_| n > 0 && k % 2 == 0)
        .ok_or(ConstitutiveFibreError::Shape)
}

impl<'c> ResidentNormalMaterialView<'c> {
    /// Certify this material cut for the Cayley reaction step (see [`PowerNeutralCertificate`]):
    /// one explicit detachment of the resident state and an exact inertia. Refuses a cut whose
    /// slices are not exactly skew-Hermitian or whose linear block is active.
    pub fn certify_power_neutral_reaction(
        &self,
        n: usize,
        k: usize,
    ) -> Result<PowerNeutralCertificate<'c>, ConstitutiveFibreError> {
        let features = power_neutral_features(n, k)?;
        if self.targets != n
            || self.source_chart
                != (NormalSourceChart::Features {
                    source_complex: features,
                })
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let layout = self.source_chart.layout(self.targets)?;
        let rest = self.surface.detach_section(&self.state, i64::BITS)?;
        point_section(&rest, 1, layout.state_words)?;
        let numeric = wides(&rest.intervals[..layout.matrix_words])?;
        PowerNeutralCertificate::from_words(Rc::clone(&self.state), &numeric, n, k, self.grain.0)
    }
}

fn grid(numeric: &[i128], row: usize, column: usize, features: usize) -> GridComplex {
    let at = 2 * (row * features + column);
    (BigInt::from(numeric[at]), BigInt::from(numeric[at + 1]))
}

impl<'c> ResidentNormalMaterial<'c> {
    /// Project the learned reaction onto the power-neutral law (see the module header). The
    /// material's feature chart must be `n + k/2 + n·k` complex sources with `n` targets.
    pub fn project_power_neutral_reaction(
        &self,
        source_complex: usize,
        condition_real: usize,
    ) -> Result<(Self, NormalReactionProjection), ConstitutiveFibreError> {
        self.project_power_neutral_reaction_certified(source_complex, condition_real)
            .map(|(material, receipt, _)| (material, receipt))
    }

    /// [`Self::project_power_neutral_reaction`] with the certificate of the projected cut, read
    /// from the same exact words the projection wrote (no second detachment).
    pub fn project_power_neutral_reaction_certified(
        &self,
        source_complex: usize,
        condition_real: usize,
    ) -> Result<(Self, NormalReactionProjection, PowerNeutralCertificate<'c>), ConstitutiveFibreError>
    {
        let n = source_complex;
        let k = condition_real;
        let features = n
            .checked_mul(k)
            .and_then(|v| v.checked_add(n)?.checked_add(k / 2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if n == 0
            || k % 2 != 0
            || self.targets != n
            || self.source_chart
                != (NormalSourceChart::Features {
                    source_complex: features,
                })
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let layout = self.source_chart.layout(self.targets)?;
        let mut rest = self.surface.detach_section(&self.state, i64::BITS)?;
        point_section(&rest, 1, layout.state_words)?;
        let numeric = wides(&rest.intervals[..layout.matrix_words])?;
        let grain = self.grain.0;
        let unit = BigInt::from(1) << grain;
        let at_grain = |v: BigInt| Rat::new(v, unit.clone());
        let block = |columns: std::ops::Range<usize>| -> Vec<Vec<GridComplex>> {
            (0..n)
                .map(|t| {
                    columns
                        .clone()
                        .map(|j| grid(&numeric, t, j, features))
                        .collect()
                })
                .collect()
        };
        let mut next = numeric.clone();
        let mut write =
            |t: usize, j: usize, value: &GridComplex| -> Result<(), ConstitutiveFibreError> {
                let at = 2 * (t * features + j);
                next[at] = value.0.to_i128().ok_or(ConstitutiveFibreError::Uncertain)?;
                next[at + 1] = value.1.to_i128().ok_or(ConstitutiveFibreError::Uncertain)?;
                Ok(())
            };
        let mut removed_l1 = BigInt::zero();
        // Linear self-relation.
        let linear = passive_shift_at_grain(&block(0..n)).map_err(invalid)?;
        for (t, row) in linear.projected.iter().enumerate() {
            for (j, value) in row.iter().enumerate() {
                write(t, j, value)?;
            }
        }
        removed_l1 += l1(&linear.removed);
        let linear_removed_trace: BigInt = (0..n).map(|a| linear.removed[a][a].0.clone()).sum();
        let resistive_trace: BigInt = (0..n).map(|a| -&linear.projected[a][a].0).sum();
        // Modulated slices.
        let mut bilinear_removed = BigInt::zero();
        let mut bilinear_retained = BigInt::zero();
        for r in 0..k {
            let start = n + k / 2 + r * n;
            let slice = skew_hermitian_at_grain(&block(start..start + n)).map_err(invalid)?;
            for (t, row) in slice.projected.iter().enumerate() {
                for (j, value) in row.iter().enumerate() {
                    write(t, start + j, value)?;
                }
            }
            removed_l1 += l1(&slice.removed);
            bilinear_removed += frobenius_square(&slice.removed);
            bilinear_retained += frobenius_square(&slice.projected);
        }
        let port = l1(&block(n..n + k / 2));
        // Numerical witnesses: radius, exact residual, norm.
        let cv = layout.cross_values;
        let radius_before = BigInt::from(numeric[cv]);
        let residual_before = BigInt::from(numeric[cv + 1]);
        let norm: BigInt = next[..cv].iter().map(|v| BigInt::from(*v).abs()).sum();
        let (residual_after, radius) = self.normal_witness(&rest, &next, &layout, &norm)?;
        next[cv] = radius.to_i128().ok_or(ConstitutiveFibreError::Uncertain)?;
        next[cv + 1] = residual_after
            .to_i128()
            .ok_or(ConstitutiveFibreError::Uncertain)?;
        next[cv + 2] = norm.to_i128().ok_or(ConstitutiveFibreError::Uncertain)?;
        for (w, value) in next.iter().enumerate() {
            let lo = *value as u128 as u64 as i64;
            let hi = ((*value as u128) >> 64) as u64 as i64;
            rest.intervals[2 * w] = (lo, lo);
            rest.intervals[2 * w + 1] = (hi, hi);
        }
        let state = Rc::new(self.surface.mount_section_rest(&rest)?);
        let certificate =
            PowerNeutralCertificate::from_words(Rc::clone(&state), &next, n, k, grain)?;
        let square = |v: BigInt| Rat::new(v, &unit * &unit);
        Ok((
            Self {
                surface: self.surface,
                state,
                source_chart: self.source_chart,
                targets: self.targets,
                grain: self.grain,
                observations: self.observations,
                prior: self.prior.clone(),
            },
            NormalReactionProjection {
                source_complex: n,
                condition_real: k,
                bilinear_removed_square: square(bilinear_removed),
                bilinear_retained_square: square(bilinear_retained),
                linear_removed_rank: linear.removed_rank,
                linear_removed_trace: at_grain(linear_removed_trace),
                linear_shift: at_grain(linear.shift.clone()),
                resistive_trace: at_grain(resistive_trace),
                port_coupling_l1: at_grain(port),
                removed_l1: at_grain(removed_l1),
                coefficient_radius_before: at_grain(radius_before),
                coefficient_radius_after: at_grain(radius),
                normal_residual_before: at_grain(residual_before),
                normal_residual_after: at_grain(residual_after),
            },
            certificate,
        ))
    }

    /// Diagnostic restriction: the same material with the declared complex coefficient columns
    /// set to zero, its witnesses recomputed as for a projection. Used to attribute a word's
    /// activity to reaction blocks; it is not a learning law.
    pub fn with_coefficient_columns_zeroed(
        &self,
        columns: &[std::ops::Range<usize>],
    ) -> Result<Self, ConstitutiveFibreError> {
        let layout = self.source_chart.layout(self.targets)?;
        let features = layout.sources;
        if columns.iter().any(|r| r.end > features) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let mut rest = self.surface.detach_section(&self.state, i64::BITS)?;
        point_section(&rest, 1, layout.state_words)?;
        let mut next = wides(&rest.intervals[..layout.matrix_words])?;
        for t in 0..self.targets {
            for range in columns {
                for j in range.clone() {
                    next[2 * (t * features + j)] = 0;
                    next[2 * (t * features + j) + 1] = 0;
                }
            }
        }
        let cv = layout.cross_values;
        let norm: BigInt = next[..cv].iter().map(|v| BigInt::from(*v).abs()).sum();
        let (residual, radius) = self.normal_witness(&rest, &next, &layout, &norm)?;
        next[cv] = radius.to_i128().ok_or(ConstitutiveFibreError::Uncertain)?;
        next[cv + 1] = residual
            .to_i128()
            .ok_or(ConstitutiveFibreError::Uncertain)?;
        next[cv + 2] = norm.to_i128().ok_or(ConstitutiveFibreError::Uncertain)?;
        for (w, value) in next.iter().enumerate() {
            let lo = *value as u128 as u64 as i64;
            let hi = ((*value as u128) >> 64) as u64 as i64;
            rest.intervals[2 * w] = (lo, lo);
            rest.intervals[2 * w + 1] = (hi, hi);
        }
        Ok(Self {
            surface: self.surface,
            state: Rc::new(self.surface.mount_section_rest(&rest)?),
            source_chart: self.source_chart,
            targets: self.targets,
            grain: self.grain,
            observations: self.observations,
            prior: self.prior.clone(),
        })
    }

    /// The stored residual word and coefficient radius of `coefficients` against the exact
    /// `H`, `B` and statistics of `rest`, exactly as the normal-fit kernel writes them and the
    /// rest decoder checks them (`W` at `S`; `H`, `B`, `e_H`, `e_B`, `C`, `e_C` at `S²`):
    /// residual `⌈R/S²⌉` with `R = Σ_row Σ_j |Re|+|Im| of (W H − S B)_(row,j)`, radius
    /// `min(⌈(R + ‖W‖₁ e_H + S e_B)/S²⌉, ‖W‖₁ + ⌈√(C + e_C)⌉)`.
    fn normal_witness(
        &self,
        rest: &ResidentSectionRest,
        coefficients: &[i128],
        layout: &NormalLayout,
        norm: &BigInt,
    ) -> Result<(BigInt, BigInt), ConstitutiveFibreError> {
        let m = layout.sources;
        let words = MomentWire::WORDS;
        let complex = MomentWire::COMPLEX_WORDS;
        let read = |at: usize| integer(&rest.intervals[at..at + words]);
        let h0 = layout.matrix_words;
        let b0 = layout.cross_words_at();
        let e0 = layout.scalar_words_at();
        let scale = BigInt::from(1) << self.grain.0;
        let square = &scale * &scale;
        // Only nonzero coefficients contribute; zero H entries are skipped.
        let mut residual = BigInt::zero();
        for row in 0..self.targets {
            let contributing: Vec<(usize, BigInt, BigInt)> = (0..m)
                .filter_map(|k| {
                    let (re, im) = (
                        coefficients[2 * (row * m + k)],
                        coefficients[2 * (row * m + k) + 1],
                    );
                    (re != 0 || im != 0).then(|| (k, BigInt::from(re), BigInt::from(im)))
                })
                .collect();
            let mut sums = vec![(BigInt::zero(), BigInt::zero()); m];
            for (k, ar, ai) in &contributing {
                for (j, sum) in sums.iter_mut().enumerate() {
                    let at = h0 + complex * (k * m + j);
                    let hr = read(at)?;
                    let hi = read(at + words)?;
                    if hr.is_zero() && hi.is_zero() {
                        continue;
                    }
                    sum.0 += ar * &hr - ai * &hi;
                    sum.1 += ar * &hi + ai * &hr;
                }
            }
            for (j, (re, im)) in sums.into_iter().enumerate() {
                let at = b0 + complex * (row * m + j);
                let re = re - &scale * read(at)?;
                let im = im - &scale * read(at + words)?;
                residual += re.abs() + im.abs();
            }
        }
        let (eh, eb) = (read(e0)?, read(e0 + words)?);
        let energy = read(e0 + 2 * words)? + read(e0 + 3 * words)?;
        if eh.is_negative() || eb.is_negative() || energy.is_negative() {
            return Err(invalid("negative normal statistic"));
        }
        let residual_word = Integer::div_ceil(&residual, &square);
        let residual_bound = Integer::div_ceil(&(&residual + norm * &eh + &scale * &eb), &square);
        let root = energy.sqrt();
        let root = if &root * &root == energy {
            root
        } else {
            root + 1
        };
        let energy_bound = norm + root;
        Ok((residual_word, residual_bound.min(energy_bound)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::embedding_fiber::ResidentReadout;
    use holonic_core::inertia::inertia;
    use holonic_core::reaction::{hermitian_power, is_skew_hermitian, realify};
    use holonic_core::scalar::symmetric_part;
    use num_traits::One;

    /// Point rows at `grain`: real words interleaved `(re, im)`, integer values.
    fn points<'c>(
        surface: &'c ResidentSurface<'c>,
        rows: &[Vec<i64>],
        grain: ResidentGrain,
    ) -> ResidentNormalEnclosureSection<'c> {
        let width = rows[0].len();
        let scale = 1i128 << grain.0;
        let values = rows
            .iter()
            .flat_map(|row| {
                row.iter()
                    .map(|v| i128::from(*v) * scale)
                    .chain([0i128])
                    .flat_map(|word| [word as i64, (word >> 64) as i64])
                    .map(|word| (word, word))
                    .collect::<Vec<_>>()
            })
            .collect();
        let section = surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    rows.len(),
                    2 * (width + 1),
                    ResidentGrain(0),
                    64,
                    values,
                )
                .unwrap(),
            )
            .unwrap();
        ResidentNormalEnclosureSection::from_resident(surface, section, rows.len(), width, grain)
            .unwrap()
    }

    fn lcg(seed: &mut u64, span: i64) -> i64 {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((*seed >> 33) as i64).rem_euclid(2 * span + 1) - span
    }

    fn real(ball: &NativeFieldCurrentBall) -> Vec<Rat> {
        ball.center
            .iter()
            .flat_map(|z| [z.real.clone(), z.imaginary.clone()])
            .collect()
    }

    /// The realified chart `s ⊕ c ⊕ (c_r s)_r` and its adjoint, exactly: forward values, and
    /// `⟨Dφ[δs,δc], g⟩ = ⟨δs, g_s⟩ + ⟨δc, g_c⟩` in the real pairing (zero adjoint residual).
    #[test]
    #[ignore = "requires CUDA; realified bilinear features and their adjoint pair exactly with the differential"]
    fn realified_features_and_adjoint_pair_with_the_differential() {
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let grain = ResidentGrain(12);
        let (d, k) = (4usize, 4usize); // two complex current, two complex contrast coordinates
        let f = d + k + d * k;
        let mut seed = 5;
        let s_rows: Vec<Vec<i64>> = (0..3)
            .map(|_| (0..d).map(|_| lcg(&mut seed, 5)).collect())
            .collect();
        let c_rows: Vec<Vec<i64>> = (0..3)
            .map(|_| (0..k).map(|_| lcg(&mut seed, 5)).collect())
            .collect();
        let g_rows: Vec<Vec<i64>> = (0..3)
            .map(|_| (0..f).map(|_| lcg(&mut seed, 5)).collect())
            .collect();
        let (ds, dc): (Vec<i64>, Vec<i64>) = (
            (0..d).map(|_| lcg(&mut seed, 3)).collect(),
            (0..k).map(|_| lcg(&mut seed, 3)).collect(),
        );
        let source = points(&surface, &s_rows, grain);
        let condition = points(&surface, &c_rows, grain);
        let covector = points(&surface, &g_rows, grain);
        let features = source
            .realified_bilinear_enclosed_features(&condition)
            .unwrap();
        assert_eq!(features.components(), f);
        let (gs, gc) = source
            .realified_bilinear_enclosed_pullback(&condition, &covector)
            .unwrap();
        let int = |v: i64| Rat::from_integer(v.into());
        for row in 0..3 {
            let (s, c, g) = (&s_rows[row], &c_rows[row], &g_rows[row]);
            let ball = features.row(row).unwrap().inspect().unwrap();
            assert!(ball.radius.is_zero());
            let y = real(&ball);
            let mut want: Vec<Rat> = s.iter().chain(c).map(|v| int(*v)).collect();
            for r in 0..k {
                want.extend(s.iter().map(|v| int(v * c[r])));
            }
            assert_eq!(y, want);
            // Differential of φ at (s,c) in the direction (δs,δc), paired with g.
            let mut dphi: Vec<i64> = ds.iter().chain(&dc).copied().collect();
            for r in 0..k {
                dphi.extend((0..d).map(|i| dc[r] * s[i] + c[r] * ds[i]));
            }
            let lhs: i64 = dphi.iter().zip(g).map(|(a, b)| a * b).sum();
            let gs_ball = gs.row(row).unwrap().inspect().unwrap();
            let gc_ball = gc.row(row).unwrap().inspect().unwrap();
            assert!(gs_ball.radius.is_zero() && gc_ball.radius.is_zero());
            let rhs: Rat = real(&gs_ball)
                .iter()
                .zip(&ds)
                .map(|(a, b)| a * int(*b))
                .sum::<Rat>()
                + real(&gc_ball)
                    .iter()
                    .zip(&dc)
                    .map(|(a, b)| a * int(*b))
                    .sum::<Rat>();
            assert_eq!(int(lhs), rhs, "adjoint pairing residual at row {row}");
        }
        // The legacy chart is unchanged by the flag: its width stays d + k + d·k/2.
        let legacy = source.bilinear_enclosed_features(&condition).unwrap();
        assert_eq!(legacy.components(), d + k + d * k / 2);
    }

    /// A trained material projected onto the power-neutral law: every modulated slice exactly
    /// skew-Hermitian, so `Re⟨s, J(c)s⟩ = 0` exactly for random admitted `c`; the linear block
    /// passive (certified); the contrast coupling unchanged; the executed device read agrees with
    /// the exact projected map within its enclosure; projecting again changes nothing.
    #[test]
    #[ignore = "requires CUDA; the power-neutral deposit projection on a trained resident material"]
    fn a_trained_material_projects_onto_the_power_neutral_law() {
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let grain = ResidentGrain(20);
        let n = 2usize;
        let k = 4usize;
        let features = n + k / 2 + n * k;
        let mut seed = 17;
        let material =
            ResidentNormalMaterial::found_features(&surface, features, n, grain).unwrap();
        // Train on random realified features and random targets.
        let rows = 12;
        let s_rows: Vec<Vec<i64>> = (0..rows)
            .map(|_| (0..2 * n).map(|_| lcg(&mut seed, 4)).collect())
            .collect();
        let c_rows: Vec<Vec<i64>> = (0..rows)
            .map(|_| (0..k).map(|_| lcg(&mut seed, 4)).collect())
            .collect();
        let t_rows: Vec<Vec<i64>> = (0..rows)
            .map(|_| (0..2 * n).map(|_| lcg(&mut seed, 6)).collect())
            .collect();
        let phi = points(&surface, &s_rows, grain)
            .realified_bilinear_enclosed_features(&points(&surface, &c_rows, grain))
            .unwrap();
        let material = material
            .stage_receive_enclosed_section(&phi, &points(&surface, &t_rows, grain))
            .unwrap();
        let before = material.inspect().unwrap().material.coefficients;
        let (projected, receipt) = material.project_power_neutral_reaction(n, k).unwrap();
        let after = projected.inspect().unwrap().material.coefficients;
        let unit = BigInt::one() << grain.0;
        let grid = |m: &Vec<Vec<crate::ExactComplexWaveCurrent>>,
                    cols: std::ops::Range<usize>|
         -> Vec<Vec<GridComplex>> {
            m.iter()
                .map(|row| {
                    cols.clone()
                        .map(|j| {
                            let z = &row[j];
                            let at = |v: &Rat| (v * Rat::from_integer(unit.clone())).to_integer();
                            (at(&z.real), at(&z.imaginary))
                        })
                        .collect()
                })
                .collect()
        };
        // Slices.
        let slices: Vec<_> = (0..k)
            .map(|r| grid(&after, n + k / 2 + r * n..n + k / 2 + (r + 1) * n))
            .collect();
        assert!(slices.iter().all(|a| is_skew_hermitian(a)));
        for _ in 0..16 {
            let c: Vec<BigInt> = (0..k).map(|_| BigInt::from(lcg(&mut seed, 1000))).collect();
            let j: Vec<Vec<GridComplex>> = (0..n)
                .map(|a| {
                    (0..n)
                        .map(|b| {
                            let mut z = (BigInt::zero(), BigInt::zero());
                            for (r, slice) in slices.iter().enumerate() {
                                z.0 += &c[r] * &slice[a][b].0;
                                z.1 += &c[r] * &slice[a][b].1;
                            }
                            z
                        })
                        .collect()
                })
                .collect();
            let s: Vec<(Rat, Rat)> = (0..n)
                .map(|_| {
                    (
                        Rat::from_integer(lcg(&mut seed, 99).into()),
                        Rat::from_integer(lcg(&mut seed, 99).into()),
                    )
                })
                .collect();
            assert!(hermitian_power(&j, &s).is_zero());
        }
        // Linear block passive, certified.
        let linear = grid(&after, 0..n);
        assert_eq!(
            inertia(&symmetric_part(&realify(&linear).unwrap()).unwrap()).positive,
            0
        );
        // Contrast coupling unchanged.
        assert_eq!(grid(&before, n..n + k / 2), grid(&after, n..n + k / 2));
        assert!(receipt.bilinear_removed_square > Rat::zero());
        // The executed read of the projected map on fresh features agrees with the exact map.
        let s_rows: Vec<Vec<i64>> = (0..3)
            .map(|_| (0..2 * n).map(|_| lcg(&mut seed, 4)).collect())
            .collect();
        let c_rows: Vec<Vec<i64>> = (0..3)
            .map(|_| (0..k).map(|_| lcg(&mut seed, 4)).collect())
            .collect();
        let phi = points(&surface, &s_rows, grain)
            .realified_bilinear_enclosed_features(&points(&surface, &c_rows, grain))
            .unwrap();
        let read = projected
            .retained_view()
            .read_applied_enclosed_section(&phi)
            .unwrap();
        for row in 0..3 {
            let f = real(&phi.row(row).unwrap().inspect().unwrap());
            let y = read.row(row).unwrap().inspect().unwrap();
            for t in 0..n {
                let (mut re, mut im) = (Rat::zero(), Rat::zero());
                for j in 0..features {
                    let z = &after[t][j];
                    re += &z.real * &f[2 * j] - &z.imaginary * &f[2 * j + 1];
                    im += &z.real * &f[2 * j + 1] + &z.imaginary * &f[2 * j];
                }
                let e = (&y.center[t].real - re).abs() + (&y.center[t].imaginary - im).abs();
                assert!(
                    e <= &y.radius * Rat::from_integer(2.into()),
                    "read outside its enclosure"
                );
            }
        }
        // The projected material's recomputed witnesses satisfy the rest decoder exactly.
        let wire = projected.rest().unwrap();
        let mut bytes = Vec::new();
        wire.write(&mut bytes).unwrap();
        let reopened = NormalMaterialRest::read(&mut bytes.as_slice(), bytes.len() as u64)
            .unwrap()
            .remount(&surface)
            .unwrap();
        assert_eq!(reopened.inspect().unwrap().material.coefficients, after);
        // Idempotent: a projected material is fixed.
        let (again, second) = projected.project_power_neutral_reaction(n, k).unwrap();
        assert_eq!(again.inspect().unwrap().material.coefficients, after);
        assert!(second.bilinear_removed_square.is_zero());
        assert_eq!(second.linear_removed_rank, 0);
        assert_eq!(second.normal_residual_after, receipt.normal_residual_after);
    }

    /// Rows at `grain` with a declared nonzero radius (grain units).
    fn balls<'c>(
        surface: &'c ResidentSurface<'c>,
        rows: &[Vec<i64>],
        grain: ResidentGrain,
        radius: i128,
    ) -> ResidentNormalEnclosureSection<'c> {
        let width = rows[0].len();
        let scale = 1i128 << grain.0;
        let values = rows
            .iter()
            .flat_map(|row| {
                row.iter()
                    .map(|v| i128::from(*v) * scale)
                    .chain([radius])
                    .flat_map(|word| [word as i64, (word >> 64) as i64])
                    .map(|word| (word, word))
                    .collect::<Vec<_>>()
            })
            .collect();
        let section = surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    rows.len(),
                    2 * (width + 1),
                    ResidentGrain(0),
                    64,
                    values,
                )
                .unwrap(),
            )
            .unwrap();
        ResidentNormalEnclosureSection::from_resident(surface, section, rows.len(), width, grain)
            .unwrap()
    }

    /// The exact Cayley step `(I − K/2) y = (I + K/2) p + W_c c` (and, with `adjoint`, the solve
    /// `(I − K/2)ᴴ u = g`) over ℚ on the interleaved real chart, from the certificate's coefficients.
    fn exact_cayley(
        certificate: &PowerNeutralCertificate<'_>,
        p: &[Rat],
        c: &[Rat],
        adjoint: bool,
    ) -> Vec<Rat> {
        let (n, k) = (certificate.n, certificate.k);
        let unit = Rat::from_integer(BigInt::one() << certificate.grain);
        let w = |a: usize, j: usize| {
            let (x, y) = &certificate.coefficients[a][j];
            (
                Rat::from_integer(x.clone()) / &unit,
                Rat::from_integer(y.clone()) / &unit,
            )
        };
        let kc = |a: usize, b: usize| {
            let (mut x, mut y) = w(a, b);
            for r in 0..k {
                let (sx, sy) = w(a, n + k / 2 + r * n + b);
                x += &c[r] * sx;
                y += &c[r] * sy;
            }
            (x, y)
        };
        let half = Rat::new(1.into(), 2.into());
        // Real 2n × 2n of K (or Kᴴ).
        let mut kr = vec![vec![Rat::zero(); 2 * n]; 2 * n];
        for a in 0..n {
            for b in 0..n {
                let (x, y) = if adjoint {
                    let (x, y) = kc(b, a);
                    (x, -y)
                } else {
                    kc(a, b)
                };
                kr[2 * a][2 * b] = x.clone();
                kr[2 * a][2 * b + 1] = -y.clone();
                kr[2 * a + 1][2 * b] = y;
                kr[2 * a + 1][2 * b + 1] = x;
            }
        }
        let system: Vec<Vec<Rat>> = (0..2 * n)
            .map(|i| {
                (0..2 * n)
                    .map(|j| {
                        let id = if i == j { Rat::one() } else { Rat::zero() };
                        id - &half * &kr[i][j]
                    })
                    .collect()
            })
            .collect();
        let rhs: Vec<Rat> = if adjoint {
            p.to_vec()
        } else {
            (0..2 * n)
                .map(|i| {
                    let mut v = p[i].clone();
                    for j in 0..2 * n {
                        v += &half * &kr[i][j] * &p[j];
                    }
                    // W_c c: complex column m multiplies c_(2m) + i c_(2m+1).
                    let a = i / 2;
                    for m in 0..k / 2 {
                        let (x, y) = w(a, n + m);
                        let (cr, ci) = (&c[2 * m], &c[2 * m + 1]);
                        v += if i % 2 == 0 {
                            &x * cr - &y * ci
                        } else {
                            &x * ci + &y * cr
                        };
                    }
                    v
                })
                .collect()
        };
        let matrix =
            holonic_core::exact_linear::ExactRatMatrix::shaped(2 * n, 2 * n, system).unwrap();
        let (z, kernel) = matrix.preimage_fibre(&rhs).unwrap().unwrap();
        assert!(kernel.is_empty());
        z
    }

    fn inside(exact: &[Rat], ball: &NativeFieldCurrentBall) -> bool {
        let centre = real(ball);
        let square: Rat = exact
            .iter()
            .zip(&centre)
            .map(|(a, b)| (a - b) * (a - b))
            .sum();
        square <= &ball.radius * &ball.radius
    }

    /// **The Cayley step's certified enclosure.** On a trained, projected power-neutral material
    /// with large contrasts (so the explicit step would amplify by `1 + |Jx|²/|x|²`), the device
    /// step and its adjoint contain the exact rational solutions at the ball centres and at
    /// perturbed points inside the input balls; the step is contractive on the drive (`|y| ≤ |p|
    /// + |W_c c|`, `Holon/Cayley.lean::cayley_isometry` with the resistive part); a certificate of
    /// another material cut is refused.
    #[test]
    #[ignore = "requires CUDA; the Cayley reaction step and its adjoint contain the exact solution"]
    fn the_cayley_step_and_adjoint_contain_the_exact_solution() {
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let grain = ResidentGrain(20);
        let (n, k) = (3usize, 4usize);
        let features = n + k / 2 + n * k;
        let mut seed = 29;
        let material =
            ResidentNormalMaterial::found_features(&surface, features, n, grain).unwrap();
        let rows = 16;
        let s_rows: Vec<Vec<i64>> = (0..rows)
            .map(|_| (0..2 * n).map(|_| lcg(&mut seed, 4)).collect())
            .collect();
        let c_rows: Vec<Vec<i64>> = (0..rows)
            .map(|_| (0..k).map(|_| lcg(&mut seed, 4)).collect())
            .collect();
        let t_rows: Vec<Vec<i64>> = (0..rows)
            .map(|_| (0..2 * n).map(|_| lcg(&mut seed, 9)).collect())
            .collect();
        let phi = points(&surface, &s_rows, grain)
            .realified_bilinear_enclosed_features(&points(&surface, &c_rows, grain))
            .unwrap();
        let material = material
            .stage_receive_enclosed_section(&phi, &points(&surface, &t_rows, grain))
            .unwrap();
        let (projected, _, certificate) = material
            .project_power_neutral_reaction_certified(n, k)
            .unwrap();
        let view = projected.retained_view();
        // Large contrasts: |c| ~ 300, the regime in which the explicit step diverged.
        let p_rows: Vec<Vec<i64>> = (0..4)
            .map(|_| (0..2 * n).map(|_| lcg(&mut seed, 50)).collect())
            .collect();
        let c_rows: Vec<Vec<i64>> = (0..4)
            .map(|_| (0..k).map(|_| lcg(&mut seed, 300)).collect())
            .collect();
        let g_rows: Vec<Vec<i64>> = (0..4)
            .map(|_| (0..2 * n).map(|_| lcg(&mut seed, 20)).collect())
            .collect();
        let (rp, rc, rg) = (7i128, 5i128, 3i128);
        let p = balls(&surface, &p_rows, grain, rp);
        let c = balls(&surface, &c_rows, grain, rc);
        let g = balls(&surface, &g_rows, grain, rg);
        let (y, mid) = view
            .cayley_reaction_step(&certificate, &p, Some(&c))
            .unwrap();
        let (u, gp) = view
            .cayley_reaction_adjoint(&certificate, Some(&c), &g)
            .unwrap();
        let int = |v: i64| Rat::from_integer(v.into());
        let unit = Rat::from_integer(BigInt::one() << grain.0);
        for row in 0..4 {
            let yb = y.row(row).unwrap().inspect().unwrap();
            let mb = mid.row(row).unwrap().inspect().unwrap();
            let ub = u.row(row).unwrap().inspect().unwrap();
            let gpb = gp.row(row).unwrap().inspect().unwrap();
            // Centres and one perturbed corner inside each input ball.
            for corner in [0i64, 1] {
                let shift = |r: i128, len: usize, i: usize| -> Rat {
                    // Spread r/2 over the first coordinate and r/2 over the last: |δ|₂ ≤ r.
                    if corner == 0 || (i != 0 && i != len - 1) {
                        Rat::zero()
                    } else {
                        Rat::new(BigInt::from(r), BigInt::from(2)) / &unit
                    }
                };
                let p0: Vec<Rat> = p_rows[row]
                    .iter()
                    .enumerate()
                    .map(|(i, v)| int(*v) + shift(rp, 2 * n, i))
                    .collect();
                let c0: Vec<Rat> = c_rows[row]
                    .iter()
                    .enumerate()
                    .map(|(i, v)| int(*v) - shift(rc, k, i))
                    .collect();
                let g0: Vec<Rat> = g_rows[row]
                    .iter()
                    .enumerate()
                    .map(|(i, v)| int(*v) + shift(rg, 2 * n, i))
                    .collect();
                let y_exact = exact_cayley(&certificate, &p0, &c0, false);
                assert!(
                    inside(&y_exact, &yb),
                    "row {row} corner {corner}: y outside"
                );
                let m_exact: Vec<Rat> = p0
                    .iter()
                    .zip(&y_exact)
                    .map(|(a, b)| (a + b) / int(2))
                    .collect();
                assert!(inside(&m_exact, &mb), "row {row}: midpoint outside");
                let u_exact = exact_cayley(&certificate, &g0, &c0, true);
                assert!(inside(&u_exact, &ub), "row {row}: u outside");
                let gp_exact: Vec<Rat> = u_exact
                    .iter()
                    .zip(&g0)
                    .map(|(a, b)| int(2) * a - b)
                    .collect();
                assert!(inside(&gp_exact, &gpb), "row {row}: drive covector outside");
                if corner == 0 {
                    // Contraction on the drive: |y − A⁻¹W_c c| ≤ |p|, via |y| ≤ |p| + ‖A⁻¹W_c c‖.
                    let zero_p = vec![Rat::zero(); 2 * n];
                    let port = exact_cayley(&certificate, &zero_p, &c0, false);
                    let free: Rat = y_exact
                        .iter()
                        .zip(&port)
                        .map(|(a, b)| (a - b) * (a - b))
                        .sum();
                    let drive: Rat = p0.iter().map(|a| a * a).sum();
                    assert!(
                        free <= drive,
                        "row {row}: the Cayley map is not contractive"
                    );
                }
            }
            // The certified radius stays small: a few grain units above the input radius.
            assert!(yb.radius < int(1), "row {row}: radius {}", yb.radius);
        }
        // A certificate of another cut is refused.
        let other = ResidentNormalMaterial::found_features(&surface, features, n, grain)
            .unwrap()
            .retained_view();
        assert!(
            other
                .cayley_reaction_step(&certificate, &p, Some(&c))
                .is_err()
        );
    }
}
