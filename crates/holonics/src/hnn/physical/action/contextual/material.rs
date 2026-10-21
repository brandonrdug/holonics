//! Bounded realification of b27588d2's complex H/B normal owner. Its numerical
//! LDL proposal is dyadic; the residual is always read against the exact moments.
use super::*;
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

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
    pub(super) fn found(sources: usize, targets: usize) -> Self {
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
    pub(super) fn stage(
        &self,
        f: &[Complex],
        eta: &[Complex],
        bounds: &ContextualBounds,
    ) -> Result<Self, HnnError> {
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
        next.fit(bounds)?;
        Ok(next)
    }
    pub(super) fn fit(&mut self, bounds: &ContextualBounds) -> Result<(), HnnError> {
        let m = self.h.len();
        let d = 2 * m;
        let scale = Rat::from_integer(BigInt::one() << bounds.precision_bits);
        let grid = |v: Rat| {
            let q = v * &scale;
            Rat::new(q.numer() / q.denom(), scale.numer().clone())
        };
        // Same real-block proposal and diagonal majorant as normal_fit_sources.
        let mut a = vec![vec![Rat::zero(); d]; d];
        for (i, r) in a.iter_mut().enumerate() {
            for (j, v) in r.iter_mut().enumerate() {
                let z = &self.h[i / 2][j / 2];
                *v = grid(if i % 2 == j % 2 {
                    z[0].clone()
                } else if i % 2 == 0 {
                    -z[1].clone()
                } else {
                    z[1].clone()
                });
                if i == j {
                    *v += Rat::from_integer(BigInt::from(d)) / &scale;
                }
            }
        }
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
        for (row, b) in self.applied.iter_mut().zip(&self.b) {
            let mut rhs: Vec<_> = b
                .iter()
                .flat_map(|z| [grid(z[0].clone()), grid(-z[1].clone())])
                .collect();
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
                *z = [v[2 * j].clone(), -v[2 * j + 1].clone()];
            }
        }
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
        Ok(())
    }
}
