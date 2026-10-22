//! Bounded realification of b27588d2's complex H/B normal owner. Its numerical
//! LDL proposal is dyadic; the residual is always read against the exact moments.
use super::*;
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

/// Transient completed-operation measurements. Never serialized in material/native state.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MaterialFitWork {
    pub stage_calls: u64,
    pub fit_calls: u64,
    pub scaled_integer_fits: u64,
    pub rational_grid_fits: u64,
    pub accumulation_and_bounds: std::time::Duration,
    pub initial_grid: std::time::Duration,
    pub factor: std::time::Duration,
    pub solve: std::time::Duration,
    pub true_residual_and_bounds: std::time::Duration,
    pub total_fit: std::time::Duration,
    pub context_seal_and_contract: std::time::Duration,
}
std::thread_local! {
    static MATERIAL_WORK: std::cell::Cell<MaterialFitWork> = std::cell::Cell::new(MaterialFitWork::default());
}
pub(crate) fn note_fit_work(f: impl FnOnce(&mut MaterialFitWork)) {
    MATERIAL_WORK.with(|c| {
        let mut w = c.get();
        f(&mut w);
        c.set(w);
    });
}
pub(crate) fn reset_fit_work() {
    MATERIAL_WORK.with(|c| c.set(MaterialFitWork::default()));
}
pub(crate) fn take_fit_work() -> MaterialFitWork {
    MATERIAL_WORK.with(|c| c.replace(MaterialFitWork::default()))
}

mod scaled;

pub type Complex = [Rat; 2];
fn zero() -> Complex {
    [Rat::zero(), Rat::zero()]
}
pub(super) fn plus(a: &Complex, b: &Complex) -> Complex {
    [&a[0] + &b[0], &a[1] + &b[1]]
}
pub(super) fn minus(a: &Complex, b: &Complex) -> Complex {
    [&a[0] - &b[0], &a[1] - &b[1]]
}
pub(super) fn product(a: &Complex, b: &Complex) -> Complex {
    [&a[0] * &b[0] - &a[1] * &b[1], &a[0] * &b[1] + &a[1] * &b[0]]
}
fn conjugate(a: &Complex) -> Complex {
    [a[0].clone(), -a[1].clone()]
}
pub(super) fn complex(v: &[Rat]) -> Result<Vec<Complex>, HnnError> {
    if v.is_empty() || v.len() % 2 != 0 {
        return Err(refusal("a complete declared complex wave chart"));
    }
    Ok(v.chunks_exact(2)
        .map(|x| [x[0].clone(), x[1].clone()])
        .collect())
}
pub(super) fn real(v: &[Complex]) -> Vec<Rat> {
    v.iter().flat_map(|x| x.clone()).collect()
}
pub(super) fn features(p: &[Complex], c: &[Complex], h: &[Complex]) -> Vec<Complex> {
    let mut a: Vec<_> = c.iter().zip(p).map(|(x, y)| minus(x, y)).collect();
    a.extend_from_slice(c);
    a.extend_from_slice(p);
    let mut f = a.clone();
    f.extend_from_slice(h);
    for x in h {
        for y in &a {
            f.push(product(x, y));
        }
    }
    f
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EmpiricalMaterial {
    pub(super) h: Vec<Vec<Complex>>,
    pub(super) b: Vec<Vec<Complex>>,
    pub(super) applied: Vec<Vec<Complex>>,
    pub(super) target_energy: Rat,
    pub(super) residual_upper: Rat,
    pub(super) observations: u64,
}
impl EmpiricalMaterial {
    pub(crate) fn found(sources: usize, targets: usize) -> Self {
        let mut h = vec![vec![zero(); sources]; sources];
        for (i, r) in h.iter_mut().enumerate() {
            r[i][0] = Rat::one();
        }
        Self {
            h,
            b: vec![vec![zero(); sources]; targets],
            applied: vec![vec![zero(); sources]; targets],
            target_energy: Rat::zero(),
            residual_upper: Rat::zero(),
            observations: 0,
        }
    }
    pub fn normal(&self) -> &[Vec<Complex>] {
        &self.h
    }
    pub fn cross(&self) -> &[Vec<Complex>] {
        &self.b
    }
    pub fn applied(&self) -> &[Vec<Complex>] {
        &self.applied
    }
    pub fn target_energy(&self) -> &Rat {
        &self.target_energy
    }
    /// Since H>=I, ||M-M_ideal||_F <= ||M H-B||_F <= this exact L1 bound.
    /// It does not change the applied operator into its ideal minimizer.
    pub fn coefficient_error_upper(&self) -> &Rat {
        &self.residual_upper
    }
    pub fn observations(&self) -> u64 {
        self.observations
    }
    pub fn contract(&self, f: &[Complex]) -> Result<Vec<Complex>, HnnError> {
        if self.applied.iter().any(|r| r.len() != f.len()) {
            return Err(refusal("the declared empirical feature chart"));
        }
        Ok(self
            .applied
            .iter()
            .map(|r| {
                r.iter()
                    .zip(f)
                    .fold(zero(), |s, (x, y)| plus(&s, &product(x, y)))
            })
            .collect())
    }
    pub(crate) fn stage(
        &self,
        f: &[Complex],
        eta: &[Complex],
        bounds: &ContextualBounds,
    ) -> Result<Self, HnnError> {
        let accumulation_start = std::time::Instant::now();
        if f.len() != self.h.len() || eta.len() != self.b.len() {
            return Err(refusal("the same empirical source and response chart"));
        }
        let mut next = self.clone();
        next.observations = next
            .observations
            .checked_add(1)
            .ok_or(HnnError::CountOverflow)?;
        for (i, x) in f.iter().enumerate() {
            for (j, y) in f.iter().enumerate() {
                next.h[i][j] = plus(&next.h[i][j], &product(x, &conjugate(y)));
            }
        }
        for (i, y) in eta.iter().enumerate() {
            next.target_energy += &y[0] * &y[0] + &y[1] * &y[1];
            for (j, x) in f.iter().enumerate() {
                next.b[i][j] = plus(&next.b[i][j], &product(y, &conjugate(x)));
            }
        }
        bounds.check(
            next.h
                .iter()
                .flatten()
                .chain(next.b.iter().flatten())
                .flat_map(|x| x.iter())
                .chain(std::iter::once(&next.target_energy)),
        )?;
        note_fit_work(|w| {
            w.stage_calls += 1;
            w.accumulation_and_bounds += accumulation_start.elapsed();
        });
        next.fit(bounds)?;
        Ok(next)
    }
    pub(super) fn fit(&mut self, bounds: &ContextualBounds) -> Result<(), HnnError> {
        self.fit_with_backend(bounds, true, true)
    }
    #[cfg(test)]
    fn fit_with_real_reuse(
        &mut self,
        bounds: &ContextualBounds,
        allow_real_reuse: bool,
    ) -> Result<(), HnnError> {
        self.fit_with_backend(bounds, allow_real_reuse, false)
    }
    /// All-real moments have two identical, uncoupled interleaved real blocks.
    /// Only exact-zero imaginary operands qualify; complex material keeps the
    /// original realification. This is arithmetic reuse, not a changed fit law.
    fn fit_with_backend(
        &mut self,
        bounds: &ContextualBounds,
        allow_real_reuse: bool,
        allow_scaled_integer: bool,
    ) -> Result<(), HnnError> {
        let fit_start = std::time::Instant::now();
        note_fit_work(|w| w.fit_calls += 1);
        let m = self.h.len();
        let full_dimension = 2 * m;
        let all_real = allow_real_reuse
            && self
                .h
                .iter()
                .chain(&self.b)
                .chain(&self.applied)
                .flatten()
                .all(|z| z[1].is_zero());
        let d = if all_real { m } else { full_dimension };
        #[cfg(test)]
        fit_work::begin(d, self.b.len(), all_real);
        if all_real && allow_scaled_integer {
            note_fit_work(|w| w.scaled_integer_fits += 1);
            scaled::propose(self, bounds)?;
        } else {
            note_fit_work(|w| w.rational_grid_fits += 1);
            let scale = Rat::from_integer(BigInt::one() << bounds.precision_bits);
            let grid = |v: Rat| {
                #[cfg(test)]
                fit_work::grid();
                let q = v * &scale;
                Rat::new(q.numer() / q.denom(), scale.numer().clone())
            };
            let grid_start = std::time::Instant::now();
            // Same real-block proposal and diagonal majorant as normal_fit_sources.
            let mut a = vec![vec![Rat::zero(); d]; d];
            for (i, r) in a.iter_mut().enumerate() {
                for (j, v) in r.iter_mut().enumerate() {
                    let z = if all_real {
                        &self.h[i][j]
                    } else {
                        &self.h[i / 2][j / 2]
                    };
                    *v = grid(if all_real || i % 2 == j % 2 {
                        z[0].clone()
                    } else if i % 2 == 0 {
                        -z[1].clone()
                    } else {
                        z[1].clone()
                    });
                    if i == j {
                        // Keep the ORIGINAL 2m/scale majorant. Using m here would
                        // change the rounded proposal, its residual and cold bytes.
                        *v += Rat::from_integer(BigInt::from(full_dimension)) / &scale;
                    }
                }
            }
            note_fit_work(|w| w.initial_grid += grid_start.elapsed());
            let factor_start = std::time::Instant::now();
            let mut diag = vec![Rat::zero(); d];
            // Port of enclosed_field_junction's bounded dyadic LDL, each product/division
            // rounded toward zero in the same order. This is a proposal, never the true H.
            for k in 0..d {
                let correction = (0..k)
                    .map(|j| grid(grid(&a[k][j] * &a[k][j]) * &diag[j]))
                    .sum::<Rat>();
                diag[k] = &a[k][k] - correction;
                if diag[k] <= Rat::zero() {
                    return Err(refusal("positive bounded dyadic normal LDL proposal"));
                }
                for i in k + 1..d {
                    let correction = (0..k)
                        .map(|j| grid(grid(&a[i][j] * &a[k][j]) * &diag[j]))
                        .sum::<Rat>();
                    a[i][k] = grid((&a[k][i] - correction) / &diag[k]);
                }
            }
            note_fit_work(|w| w.factor += factor_start.elapsed());
            let solve_start = std::time::Instant::now();
            for (row, b) in self.applied.iter_mut().zip(&self.b) {
                let mut rhs: Vec<_> = if all_real {
                    b.iter().map(|z| grid(z[0].clone())).collect()
                } else {
                    b.iter()
                        .flat_map(|z| [grid(z[0].clone()), grid(-z[1].clone())])
                        .collect()
                };
                for i in 0..d {
                    for j in 0..i {
                        let term = grid(&a[i][j] * &rhs[j]);
                        rhs[i] -= term;
                    }
                }
                let mut v: Vec<_> = rhs.iter().zip(&diag).map(|(x, y)| grid(x / y)).collect();
                for i in (0..d).rev() {
                    for j in i + 1..d {
                        let term = grid(&a[j][i] * &v[j]);
                        v[i] -= term;
                    }
                }
                for (j, z) in row.iter_mut().enumerate() {
                    *z = if all_real {
                        [v[j].clone(), Rat::zero()]
                    } else {
                        [v[2 * j].clone(), -v[2 * j + 1].clone()]
                    };
                }
            }
            note_fit_work(|w| w.solve += solve_start.elapsed());
        }
        let residual_start = std::time::Instant::now();
        let mut residual = Rat::zero();
        for (r, b) in self.applied.iter().zip(&self.b) {
            for (j, target) in b.iter().enumerate() {
                let got = r
                    .iter()
                    .enumerate()
                    .fold(zero(), |s, (k, v)| plus(&s, &product(v, &self.h[k][j])));
                let e = minus(&got, target);
                residual += e[0].abs() + e[1].abs();
            }
        }
        self.residual_upper = residual;
        bounds.check(
            self.applied
                .iter()
                .flatten()
                .flat_map(|x| x.iter())
                .chain(std::iter::once(&self.residual_upper)),
        )?;
        note_fit_work(|w| {
            w.true_residual_and_bounds += residual_start.elapsed();
            w.total_fit += fit_start.elapsed();
        });
        Ok(())
    }
}

/// Scoped test observations only; never part of material/codec/publication state.
#[cfg(test)]
mod fit_work {
    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    pub(super) struct Reading {
        pub dimension: usize,
        pub right_hand_sides: usize,
        pub real_reuse: bool,
        pub grid_calls: u64,
        pub integer_encode_calls: u64,
        pub integer_mul_calls: u64,
        pub integer_div_calls: u64,
        pub integer_decode_calls: u64,
    }
    std::thread_local! {
        static WORK: std::cell::Cell<Reading> = const { std::cell::Cell::new(Reading {
            dimension: 0, right_hand_sides: 0, real_reuse: false, grid_calls: 0, integer_encode_calls:0,integer_mul_calls:0,integer_div_calls:0,integer_decode_calls:0,
        }) };
    }
    pub(super) fn begin(dimension: usize, right_hand_sides: usize, real_reuse: bool) {
        WORK.with(|c| {
            c.set(Reading {
                dimension,
                right_hand_sides,
                real_reuse,
                grid_calls: 0,
                integer_encode_calls: 0,
                integer_mul_calls: 0,
                integer_div_calls: 0,
                integer_decode_calls: 0,
            })
        });
    }
    pub(super) fn grid() {
        WORK.with(|c| {
            let mut r = c.get();
            r.grid_calls += 1;
            c.set(r);
        });
    }
    pub(super) fn integer(kind: usize) {
        WORK.with(|c| {
            let mut r = c.get();
            match kind {
                0 => r.integer_encode_calls += 1,
                1 => r.integer_mul_calls += 1,
                2 => r.integer_div_calls += 1,
                _ => r.integer_decode_calls += 1,
            };
            c.set(r);
        });
    }
    pub(super) fn reading() -> Reading {
        WORK.with(|c| c.get())
    }
}

#[cfg(test)]
mod real_reuse_tests {
    use super::*;
    use std::time::Instant;

    fn bounds() -> ContextualBounds {
        ContextualBounds {
            branches: 1,
            pending: 8,
            precision_bits: 20,
            rational_bits: 1024,
            max_features: 32,
            max_scalar_work: 1_000_000,
        }
    }
    fn feature(arrival: i64) -> Vec<Complex> {
        (0..25)
            .map(|j| {
                [
                    Rat::new(
                        BigInt::from((j + 2 * arrival) % 9 - 4),
                        BigInt::one() << ((j + arrival) % 4) as usize,
                    ),
                    Rat::zero(),
                ]
            })
            .collect()
    }
    #[test]
    fn all_real_reuse_preserves_complete_material_cold_bytes_and_measured_work() {
        let bounds = bounds();
        let mut material = EmpiricalMaterial::found(25, 4);
        for n in 0..8 {
            let eta: Vec<_> = (0..4)
                .map(|j| {
                    [
                        Rat::new(BigInt::from(j - n + 1), BigInt::from(8)),
                        Rat::zero(),
                    ]
                })
                .collect();
            material = material.stage(&feature(n), &eta, &bounds).unwrap();
            let mut legacy = material.clone();
            legacy.fit_with_real_reuse(&bounds, false).unwrap();
            assert_eq!(
                material, legacy,
                "all original moments and applied fit at each arrival"
            );
            assert_eq!(material.checkpoint_text(), legacy.checkpoint_text());
        }
        let mut old_ns = Vec::new();
        let mut new_ns = Vec::new();
        let mut old_work = Vec::new();
        let mut new_work = Vec::new();
        for trial in 0..5 {
            // Alternate order at identical geometry; cloning is outside both timed fits.
            let mut old = material.clone();
            let mut new = material.clone();
            for fast in if trial % 2 == 0 {
                [false, true]
            } else {
                [true, false]
            } {
                let target = if fast { &mut new } else { &mut old };
                let at = Instant::now();
                target.fit_with_real_reuse(&bounds, fast).unwrap();
                let elapsed = at.elapsed().as_nanos();
                let work = fit_work::reading();
                if fast {
                    new_ns.push(elapsed);
                    new_work.push(work);
                } else {
                    old_ns.push(elapsed);
                    old_work.push(work);
                }
            }
            assert_eq!(old, new);
            assert_eq!(old.checkpoint_text(), new.checkpoint_text());
        }
        assert!(
            old_work
                .iter()
                .all(|r| r.dimension == 50 && !r.real_reuse && r.right_hand_sides == 4)
        );
        assert!(
            new_work
                .iter()
                .all(|r| r.dimension == 25 && r.real_reuse && r.right_hand_sides == 4)
        );
        assert!(
            old_work
                .iter()
                .zip(&new_work)
                .all(|(a, b)| a.grid_calls > b.grid_calls)
        );
        assert!(material.applied.iter().flatten().all(|z| z[1].is_zero()));
        let saved = material.checkpoint_text();
        let cold = EmpiricalMaterial::restored_text(&saved, 25, 4, &bounds).unwrap();
        assert_eq!(cold, material);
        assert_eq!(saved, cold.checkpoint_text());
        // Changed complex context must choose the unchanged generic algorithm.
        let mut f = feature(8);
        f[0][1] = Rat::new(1.into(), 8.into());
        let complex = material
            .stage(&f, &vec![[Rat::one(), Rat::zero()]; 4], &bounds)
            .unwrap();
        let mut fast = complex.clone();
        fast.fit_with_real_reuse(&bounds, true).unwrap();
        let complex_work = fit_work::reading();
        let mut old = complex.clone();
        old.fit_with_real_reuse(&bounds, false).unwrap();
        assert!(!complex_work.real_reuse);
        assert_eq!(complex_work, fit_work::reading());
        assert_eq!(fast, old);
        assert_eq!(fast.checkpoint_text(), old.checkpoint_text());
        let separated = new_ns.iter().max().unwrap() < old_ns.iter().min().unwrap();
        eprintln!(
            "REAL_MATERIAL_REUSE old_ns={old_ns:?} new_ns={new_ns:?} old_work={old_work:?} new_work={new_work:?} timing_ranges_separated={separated} changed_complex_fallback={complex_work:?} actual_observations={} cold_exact=true",
            material.observations
        );
    }
    #[test]
    fn scaled_integer_fit_matches_current25_production_cold_refusals_and_cost() {
        let bounds = bounds();
        let mut material = EmpiricalMaterial::found(25, 4);
        for n in 0..8 {
            let eta: Vec<_> = (0..4)
                .map(|j| [Rat::new(BigInt::from(j - n + 1), 8.into()), Rat::zero()])
                .collect();
            material = material.stage(&feature(n), &eta, &bounds).unwrap();
            let mut current = material.clone();
            current.fit_with_backend(&bounds, true, false).unwrap();
            assert_eq!(
                material, current,
                "same actual25dim moments,appliedM,residual and observation count"
            );
            assert_eq!(material.checkpoint_text(), current.checkpoint_text());
        }
        let mut old_ns = Vec::new();
        let mut new_ns = Vec::new();
        let mut old_work = Vec::new();
        let mut new_work = Vec::new();
        let mut old_phases = Vec::new();
        let mut new_phases = Vec::new();
        for trial in 0..5 {
            let mut old = material.clone();
            let mut new = material.clone();
            for scaled in if trial % 2 == 0 {
                [false, true]
            } else {
                [true, false]
            } {
                reset_fit_work();
                let t = Instant::now();
                let target = if scaled { &mut new } else { &mut old };
                target.fit_with_backend(&bounds, true, scaled).unwrap();
                let elapsed = t.elapsed().as_nanos();
                let work = fit_work::reading();
                let phases = take_fit_work();
                assert_eq!(work.dimension, 25);
                assert!(work.real_reuse);
                assert_eq!(work.right_hand_sides, 4);
                if scaled {
                    new_ns.push(elapsed);
                    new_work.push(work);
                    new_phases.push(phases);
                } else {
                    old_ns.push(elapsed);
                    old_work.push(work);
                    old_phases.push(phases);
                }
            }
            assert_eq!(old, new);
            assert_eq!(old.checkpoint_text(), new.checkpoint_text());
        }
        assert!(
            old_work
                .iter()
                .all(|w| w.grid_calls == 8725 && w.integer_mul_calls == 0)
        );
        assert!(new_work.iter().all(|w| w.grid_calls == 0
            && w.integer_encode_calls == 725
            && w.integer_decode_calls == 100
            && w.integer_mul_calls > 0
            && w.integer_div_calls > 0));
        let text = material.checkpoint_text();
        let cold = EmpiricalMaterial::restored_text(&text, 25, 4, &bounds).unwrap();
        assert_eq!(cold, material);
        assert_eq!(cold.checkpoint_text(), text);
        // Same declared precision, including toward-zero and fine-grain cases.
        for bits in [3, 8, 20, 30] {
            let mut b = bounds.clone();
            b.precision_bits = bits;
            let mut old = material.clone();
            let mut new = material.clone();
            let a = old.fit_with_backend(&b, true, false);
            let c = new.fit_with_backend(&b, true, true);
            assert_eq!(a, c);
            if a.is_ok() {
                assert_eq!(old, new);
            }
        }
        let mut complex = material.clone();
        complex.h[0][1][1] = Rat::new(1.into(), 8.into());
        complex.h[1][0][1] = Rat::new((-1).into(), 8.into());
        let mut fallback = complex.clone();
        complex.fit_with_backend(&bounds, true, true).unwrap();
        let work = fit_work::reading();
        fallback.fit_with_backend(&bounds, true, false).unwrap();
        assert_eq!(complex, fallback);
        assert!(!work.real_reuse);
        assert_eq!(work.integer_mul_calls, 0);
        let mut bad = material.clone();
        bad.h[0][0][0] = Rat::from_integer((-100).into());
        let mut bad_old = bad.clone();
        assert_eq!(
            bad.fit_with_backend(&bounds, true, true),
            bad_old.fit_with_backend(&bounds, true, false)
        );
        // Late residual range refusal stays atomic at the existing stage owner.
        let base = EmpiricalMaterial::found(3, 1);
        let mut tight = bounds.clone();
        tight.rational_bits = 64;
        let f = vec![
            [
                Rat::new(BigInt::one() << 23usize, (BigInt::one() << 25usize) + 1),
                Rat::zero(),
            ],
            zero(),
            zero(),
        ];
        let eta = vec![[Rat::one(), Rat::zero()]];
        let full = base.stage(&f, &eta, &bounds).unwrap();
        let mut a = full.clone();
        let mut b = full;
        assert_eq!(
            a.fit_with_backend(&tight, true, false),
            b.fit_with_backend(&tight, true, true)
        );
        let before = base.checkpoint_text();
        assert!(base.stage(&f, &eta, &tight).is_err());
        assert_eq!(base.checkpoint_text(), before);
        println!(
            "SCALED_INTEGER_CURRENT25 old_ns={old_ns:?} new_ns={new_ns:?} old_work={old_work:?} new_work={new_work:?} old_phases={old_phases:?} new_phases={new_phases:?} timing_ranges_separated={} same_full_H_B_C_M_error_cold=true complex_fallback=true precision_and_refusal_equal=true comparator=current25_not_old50",
            new_ns.iter().max() < old_ns.iter().min()
        );
    }
}

impl EmpiricalMaterial {
    pub(crate) fn checkpoint_text(&self) -> String {
        let mut out = format!(
            "{} {} {} {} {} ",
            self.h.len(),
            self.b.len(),
            self.observations,
            self.target_energy,
            self.residual_upper
        );
        use std::fmt::Write;
        for z in self.h.iter().chain(&self.b).chain(&self.applied).flatten() {
            write!(out, "{} {} ", z[0], z[1]).expect("string");
        }
        out
    }
    pub(crate) fn restored_text(
        text: &str,
        sources: usize,
        targets: usize,
        bounds: &ContextualBounds,
    ) -> Result<Self, HnnError> {
        let mut t = text.split_whitespace();
        fn get<T: std::str::FromStr>(t: &mut std::str::SplitWhitespace<'_>) -> Result<T, HnnError> {
            t.next()
                .and_then(|s| s.parse().ok())
                .ok_or(refusal("complete empirical material fields"))
        }
        if get::<usize>(&mut t)? != sources
            || get::<usize>(&mut t)? != targets
            || sources > bounds.max_features
        {
            return Err(refusal("declared empirical material dimensions"));
        }
        let observations = get(&mut t)?;
        let target_energy = get(&mut t)?;
        let residual_upper = get(&mut t)?;
        let mut matrix = |rows: usize| -> Result<Vec<Vec<Complex>>, HnnError> {
            (0..rows)
                .map(|_| {
                    (0..sources)
                        .map(|_| Ok([get(&mut t)?, get(&mut t)?]))
                        .collect()
                })
                .collect()
        };
        let h = matrix(sources)?;
        let b = matrix(targets)?;
        let applied = matrix(targets)?;
        if t.next().is_some() {
            return Err(refusal("no trailing empirical fields"));
        }
        let m = Self {
            h,
            b,
            applied,
            target_energy,
            residual_upper,
            observations,
        };
        bounds.check(
            m.h.iter()
                .chain(&m.b)
                .chain(&m.applied)
                .flatten()
                .flat_map(|z| z.iter())
                .chain([&m.target_energy, &m.residual_upper]),
        )?;
        let mut rows = vec![vec![Rat::zero(); 2 * sources]; 2 * sources];
        for i in 0..2 * sources {
            for j in 0..2 * sources {
                let z = &m.h[i / 2][j / 2];
                rows[i][j] = if i % 2 == j % 2 {
                    z[0].clone()
                } else if i % 2 == 0 {
                    -z[1].clone()
                } else {
                    z[1].clone()
                };
                if i == j {
                    rows[i][j] -= integer(1);
                }
            }
        }
        let form = crate::ratio::linear::inertia::SymmetricForm::from_rows(rows)
            .map_err(|_| refusal("Hermitian empirical source normal"))?;
        if crate::ratio::linear::inertia::inertia(&form).negative != 0
            || m.target_energy < Rat::zero()
        {
            return Err(refusal(
                "unit-prior empirical geometry H>=I and nonnegative targetenergy",
            ));
        }
        if observations == 0 {
            if m != Self::found(sources, targets) {
                return Err(refusal("founding empirical material"));
            }
        } else {
            let mut checked = m.clone();
            checked.fit(bounds)?;
            if checked.applied != m.applied || checked.residual_upper != m.residual_upper {
                return Err(refusal("exact applied material and fit realization bound"));
            }
        }
        Ok(m)
    }
}

#[cfg(test)]
mod native_context_pure_controls {
    use super::*;
    #[test]
    fn native_context_pure_ninety_features_fit_and_codec_preserve_exact_moments(){
        let bounds=ContextualBounds{branches:1,pending:64,precision_bits:20,rational_bits:1024,max_features:90,max_scalar_work:6_157_800};
        bounds.admit().unwrap();let mut invalid=bounds.clone();invalid.max_features=91;assert!(invalid.admit().is_err());
        let before=EmpiricalMaterial::found(90,4);let mut f=vec![zero();90];f[0]=[crate::ratio::rat(1,2),Rat::zero()];f[12]=[crate::ratio::rat(-1,4),Rat::zero()];f[89]=[crate::ratio::rat(1,8),Rat::zero()];
        let eta=vec![[Rat::one(),Rat::zero()],zero(),zero(),zero()];let started=std::time::Instant::now();
        let next=before.stage(&f,&eta,&bounds).unwrap();
        assert_eq!(next.h[0][0][0],crate::ratio::rat(5,4));assert_eq!(next.b[0][0][0],crate::ratio::rat(1,2));assert_eq!(next.observations(),1);
        let cold=EmpiricalMaterial::restored_text(&next.checkpoint_text(),90,4,&bounds).unwrap();assert_eq!(next,cold);assert_eq!(before.observations(),0);
        let mut too_large=f.clone();too_large[0][0]=Rat::from_integer(num_bigint::BigInt::one()<<1025usize);
        assert!(next.stage(&too_large,&eta,&bounds).is_err());assert_eq!(next,cold);
        println!("NATIVE_CONTEXT_PURE90 features=90 original_realification_majorant=180 H00=5/4 B00=1/2 cold_exact=true range_refusal=true fit_and_cold_ns={}",started.elapsed().as_nanos());
    }
}
