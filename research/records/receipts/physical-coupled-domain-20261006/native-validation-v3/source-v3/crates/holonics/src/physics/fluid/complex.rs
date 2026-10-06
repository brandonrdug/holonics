//! **Complex fluid: the complex-bilinear law is not the Fourier chart of a real field** (battle
//! test 4).
//!
//! [definition] Two different objects carry complex numbers
//! ([fluid construction §8](../../../../../docs/HOLONIC_FLUID_CONSTRUCTION.md)):
//!
//! - the **complex-bilinear fluid law** acts on a pair of real fields `U = a + ib`, with advection
//!   `B(U,U) = (B(a,a) − B(b,b)) + i(B(a,b) + B(b,a))` ([`complex_advection`]): two physical
//!   fields, whose Hermitian energy `(|a|² + |b|²)/2` is exchanged at the rate `2⟨a, B(b,b)⟩`
//!   ([`energy_exchange`]), while MHD's opposite induction sign cancels it ([`mhd_advection`]);
//! - the **Fourier chart** of one real field has complex coefficients on the Hermitian slice
//!   `û(−k) = conj û(k)` ([`FourierChart`]); it introduces no second field.
//!
//! The bilinear product `Σ U·U` pairs `k` with `−k` in the chart and diagonalizes to the Hermitian
//! energy `N⁻¹ Σ |Û(k)|²` only on that slice: the imaginary state `U = i δ₀` has `Σ U·U = −1` against
//! `Σ |U|² = 1`.
//!
//! | Lean `Physics/Fluid/ComplexFluid` | Rust |
//! |---|---|
//! | `complexAdvection`, `mhdAdvection`, `complexAdvection_conj`; `Physics/ConductiveFluidReflection.complexRealProjection_retains_Bbb` | [`complex_advection`], [`mhd_advection`] |
//! | `SkewIn`, `energyExchange`, `complex_energy_exchange`, `mhd_energy_exchange` | [`energy_exchange`] |
//! | `skewAdvection`, `skewAdvection_skew`, `centred4`, `complex_exchange_witness` | [`SkewAdvection`] |
//! | `dft_conj`, `real_iff_hermitian`, `bilinear_plancherel`, `hermitian_diagonal`, `imaginary_state_witness` | [`FourierChart`], [`bilinear_product`], [`hermitian_energy`] |
//!
//! [definition; agent-inferred] The chart is exact only where its roots of unity are Gaussian
//! rationals: `ℤ/1`, `ℤ/2` and `ℤ/4`. Other orders are refused by name
//! ([`FluidError::NotAGaussianRoot`]) rather than approximated; Lean states the laws for every
//! `ℤ/N` over `ℂ`.

use num_traits::{One, Zero};

use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{at, dot, matrix};
use crate::ratio::{GaussianRat, Rat, integer, rat};

use super::FluidError;

/// [definition] **The skew-symmetrized advection** `B(u,w) = ½[u ⊙ Dw + D(u ⊙ w)]` of a carrier
/// `u` transporting `w`, with an antisymmetric difference `D` (Lean `skewAdvection`). It is skew in
/// its transported argument, `⟨z, B(u,w)⟩ = −⟨w, B(u,z)⟩` (Lean `skewAdvection_skew`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SkewAdvection {
    difference: ExactRatMatrix,
}

impl SkewAdvection {
    /// Admit `D` only when it is square and `Dᵀ = −D`.
    pub fn new(difference: ExactRatMatrix) -> Result<Self, FluidError> {
        if !difference.is_square() || difference.transpose()? != difference.scaled(&-Rat::one()) {
            return Err(FluidError::NotAntisymmetric);
        }
        Ok(Self { difference })
    }

    /// The periodic centred difference `(Dw)ₓ = (w_{x+1} − w_{x−1})/2` on `ℤ/N`, `N ≥ 3` (Lean
    /// `centred4` at `N = 4`).
    pub fn centred(extent: usize) -> Result<Self, FluidError> {
        if extent < 3 {
            return Err(FluidError::Shape {
                what: "periodic extent of a centred difference",
                expected: 3,
                found: extent,
            });
        }
        let half = rat(1, 2);
        Self::new(matrix(extent, extent, |x, y| {
            if y == (x + 1) % extent {
                half.clone()
            } else if (y + 1) % extent == x {
                -half.clone()
            } else {
                Rat::zero()
            }
        })?)
    }

    pub fn extent(&self) -> usize {
        self.difference.rows()
    }

    /// `B(u, w)`.
    pub fn advect(&self, carrier: &[Rat], transported: &[Rat]) -> Result<Vec<Rat>, FluidError> {
        let n = self.extent();
        if carrier.len() != n || transported.len() != n {
            return Err(FluidError::Shape {
                what: "field extent",
                expected: n,
                found: carrier.len().min(transported.len()),
            });
        }
        let dw = self.difference.apply(transported)?;
        let product: Vec<Rat> = carrier
            .iter()
            .zip(transported)
            .map(|(u, w)| u * w)
            .collect();
        let d_product = self.difference.apply(&product)?;
        let half = rat(1, 2);
        Ok((0..n)
            .map(|x| &half * (&carrier[x] * &dw[x] + &d_product[x]))
            .collect())
    }

    /// The entry `D_xy`.
    pub fn difference(&self, x: usize, y: usize) -> Rat {
        at(&self.difference, x, y)
    }
}

fn sub(a: &[Rat], b: &[Rat]) -> Vec<Rat> {
    a.iter().zip(b).map(|(x, y)| x - y).collect()
}

fn add(a: &[Rat], b: &[Rat]) -> Vec<Rat> {
    a.iter().zip(b).map(|(x, y)| x + y).collect()
}

/// [definition] **The complex-bilinear advection** `B(U,U)` of `U = a + ib`, as its real and
/// imaginary parts `(B(a,a) − B(b,b), B(a,b) + B(b,a))` (Lean `complexAdvection`). Its real part
/// retains `−B(b,b)` (Lean `Physics/ConductiveFluidReflection.complexRealProjection_retains_Bbb`)
/// and conjugation `b ↦ −b` negates only the imaginary part (Lean `complexAdvection_conj`).
pub fn complex_advection(
    law: &SkewAdvection,
    a: &[Rat],
    b: &[Rat],
) -> Result<(Vec<Rat>, Vec<Rat>), FluidError> {
    Ok((
        sub(&law.advect(a, a)?, &law.advect(b, b)?),
        add(&law.advect(a, b)?, &law.advect(b, a)?),
    ))
}

/// [definition] **The MHD advection**: the same real part, the opposite stretching sign in the
/// induction, `(B(a,a) − B(b,b), B(a,b) − B(b,a))` (Lean `mhdAdvection`).
pub fn mhd_advection(
    law: &SkewAdvection,
    a: &[Rat],
    b: &[Rat],
) -> Result<(Vec<Rat>, Vec<Rat>), FluidError> {
    Ok((
        sub(&law.advect(a, a)?, &law.advect(b, b)?),
        sub(&law.advect(a, b)?, &law.advect(b, a)?),
    ))
}

/// [proved-derived; implemented-exact] **The Hermitian energy exchange** `⟨a, ȧ⟩ + ⟨b, ḃ⟩` under
/// `(ȧ, ḃ) = −advection` (Lean `energyExchange`). For a skew advection it is `2⟨a, B(b,b)⟩` for the
/// complex law (Lean `complex_energy_exchange`) and `0` for MHD (Lean `mhd_energy_exchange`).
pub fn energy_exchange(a: &[Rat], b: &[Rat], advection: &(Vec<Rat>, Vec<Rat>)) -> Rat {
    -dot(a, &advection.0) - dot(b, &advection.1)
}

/// [definition] **The Fourier chart on `ℤ/N`** with the root `ω = e^{2πi/N}` (Mathlib `ZMod.dft`):
/// `𝓕Φ(k) = Σ_j ω^{−jk} Φ(j)`, exact for `N ∈ {1, 2, 4}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FourierChart {
    order: usize,
    root: GaussianRat,
}

impl FourierChart {
    /// The chart of order `N`, refused unless its roots of unity are Gaussian rationals.
    pub fn new(order: usize) -> Result<Self, FluidError> {
        let root = match order {
            1 => GaussianRat::one(),
            2 => GaussianRat::from_i64(-1, 0),
            4 => GaussianRat::i(),
            _ => return Err(FluidError::NotAGaussianRoot { order }),
        };
        Ok(Self { order, root })
    }

    pub fn order(&self) -> usize {
        self.order
    }

    /// `𝓕Φ`.
    pub fn transform(&self, field: &[GaussianRat]) -> Result<Vec<GaussianRat>, FluidError> {
        let n = self.order;
        if field.len() != n {
            return Err(FluidError::Shape {
                what: "field on ℤ/N",
                expected: n,
                found: field.len(),
            });
        }
        Ok((0..n)
            .map(|k| {
                (0..n).fold(GaussianRat::zero(), |sum, j| {
                    let exponent = (n - (j * k) % n) % n;
                    sum.add(&self.root.pow(exponent as u32).mul(&field[j]))
                })
            })
            .collect())
    }

    /// `k ↦ −k` on `ℤ/N`.
    pub fn negate(&self, k: usize) -> usize {
        (self.order - k % self.order) % self.order
    }

    /// [proved-derived; implemented-exact] **The Hermitian slice**: `𝓕(−k) = conj 𝓕(k)` for every
    /// `k`, which holds exactly for the transform of a real field (Lean `real_iff_hermitian`).
    pub fn is_hermitian(&self, transform: &[GaussianRat]) -> bool {
        (0..self.order).all(|k| transform[self.negate(k)] == transform[k].conj())
    }

    /// [proved-derived; implemented-exact] **The bilinear product in the chart**,
    /// `N⁻¹ Σ_k 𝓕Φ(k) 𝓕Ψ(−k)` (Lean `bilinear_plancherel`).
    pub fn paired(
        &self,
        left: &[GaussianRat],
        right: &[GaussianRat],
    ) -> Result<GaussianRat, FluidError> {
        let (fl, fr) = (self.transform(left)?, self.transform(right)?);
        let sum = (0..self.order).fold(GaussianRat::zero(), |sum, k| {
            sum.add(&fl[k].mul(&fr[self.negate(k)]))
        });
        Ok(sum.scale(&(Rat::one() / integer(self.order as i64))))
    }
}

/// Whether every value of a field is real.
pub fn is_real(field: &[GaussianRat]) -> bool {
    field.iter().all(GaussianRat::is_real)
}

/// The bilinear product `Σ Φ(j) Ψ(j)`: a different receiver from the energy, not a positive
/// quantity for a complex field.
pub fn bilinear_product(left: &[GaussianRat], right: &[GaussianRat]) -> GaussianRat {
    left.iter()
        .zip(right)
        .fold(GaussianRat::zero(), |sum, (x, y)| sum.add(&x.mul(y)))
}

/// The Hermitian energy `Σ |Φ(j)|²`.
pub fn hermitian_energy(field: &[GaussianRat]) -> Rat {
    field.iter().fold(Rat::zero(), |sum, x| sum + x.norm_sq())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ints(values: &[i64]) -> Vec<Rat> {
        values.iter().map(|v| integer(*v)).collect()
    }

    fn field(values: &[(i64, i64)]) -> Vec<GaussianRat> {
        values
            .iter()
            .map(|(re, im)| GaussianRat::from_i64(*re, *im))
            .collect()
    }

    /// Lean `skewAdvection_skew`: the skew-symmetrized advection is skew in its transported
    /// argument, and a non-antisymmetric difference is refused.
    #[test]
    fn the_skew_advection_is_skew_in_its_transported_argument() {
        for n in [4, 5] {
            let law = SkewAdvection::centred(n).unwrap();
            let u: Vec<Rat> = (0..n as i64).map(|x| rat(x * x - 2, x + 1)).collect();
            let v: Vec<Rat> = (0..n as i64).map(|x| rat(3 - x, 2)).collect();
            let z: Vec<Rat> = (0..n as i64).map(|x| integer(x % 3 - 1)).collect();
            assert_eq!(
                dot(&z, &law.advect(&u, &v).unwrap()),
                -dot(&v, &law.advect(&u, &z).unwrap())
            );
        }
        let not_skew = ExactRatMatrix::new(vec![ints(&[0, 1]), ints(&[1, 0])]).unwrap();
        assert_eq!(
            SkewAdvection::new(not_skew),
            Err(FluidError::NotAntisymmetric)
        );
    }

    /// Lean `complex_energy_exchange`, `mhd_energy_exchange`: the complex law exchanges
    /// `2⟨a, B(b,b)⟩`, MHD exchanges nothing.
    #[test]
    fn the_complex_law_exchanges_hermitian_energy_and_mhd_does_not() {
        let law = SkewAdvection::centred(5).unwrap();
        let a: Vec<Rat> = ints(&[2, -1, 0, 3, 1]);
        let b: Vec<Rat> = vec![rat(1, 2), integer(1), integer(-2), rat(1, 3), integer(0)];
        let complex = complex_advection(&law, &a, &b).unwrap();
        assert_eq!(
            energy_exchange(&a, &b, &complex),
            integer(2) * dot(&a, &law.advect(&b, &b).unwrap())
        );
        let mhd = mhd_advection(&law, &a, &b).unwrap();
        assert!(energy_exchange(&a, &b, &mhd).is_zero());
    }

    /// Lean `complex_exchange_witness`: on `ℤ/4`, `a = δ₀`, `b = δ₀ + δ₁` exchange `1` and `−a`
    /// exchanges `−1`: the exchange is nonzero and indefinite.
    #[test]
    fn the_complex_exchange_is_nonzero_and_indefinite() {
        let law = SkewAdvection::centred(4).unwrap();
        let a = ints(&[1, 0, 0, 0]);
        let minus_a = ints(&[-1, 0, 0, 0]);
        let b = ints(&[1, 1, 0, 0]);
        let exchange = |a: &[Rat]| energy_exchange(a, &b, &complex_advection(&law, a, &b).unwrap());
        assert_eq!(exchange(&a), integer(1));
        assert_eq!(exchange(&minus_a), integer(-1));
    }

    /// Lean `Physics/ConductiveFluidReflection.complexRealProjection_retains_Bbb`,
    /// `complexAdvection_conj`: the real part of the complex law retains `−B(b,b)`, and conjugation
    /// negates only the imaginary part.
    #[test]
    fn the_real_projection_loses_the_definite_term() {
        let law = SkewAdvection::centred(4).unwrap();
        let (a, b) = (ints(&[1, 0, 2, 0]), ints(&[1, 1, 0, 0]));
        let (real, imaginary) = complex_advection(&law, &a, &b).unwrap();
        let bbb = law.advect(&b, &b).unwrap();
        assert_eq!(
            sub(&real, &law.advect(&a, &a).unwrap()),
            sub(&vec![Rat::zero(); 4], &bbb)
        );
        assert!(bbb.iter().any(|x| !x.is_zero()));
        let minus_b: Vec<Rat> = b.iter().map(|x| -x.clone()).collect();
        let (real_c, imaginary_c) = complex_advection(&law, &a, &minus_b).unwrap();
        assert_eq!(real_c, real);
        assert_eq!(imaginary_c, sub(&vec![Rat::zero(); 4], &imaginary));
    }

    /// Lean `real_iff_hermitian`, `bilinear_plancherel`, `hermitian_diagonal`: a real field's
    /// transform is Hermitian, the chart pairs `k` with `−k`, and on the Hermitian slice the
    /// product is the energy.
    #[test]
    fn the_fourier_chart_of_a_real_field_is_hermitian_and_diagonalizes_the_product() {
        let chart = FourierChart::new(4).unwrap();
        let real = field(&[(3, 0), (-1, 0), (2, 0), (5, 0)]);
        let transform = chart.transform(&real).unwrap();
        assert!(chart.is_hermitian(&transform));
        let complex = field(&[(1, 2), (0, -1), (3, 1), (-2, 0)]);
        assert!(!chart.is_hermitian(&chart.transform(&complex).unwrap()));
        assert_eq!(
            chart.paired(&complex, &real).unwrap(),
            bilinear_product(&complex, &real)
        );
        let energy = transform
            .iter()
            .fold(Rat::zero(), |sum, x| sum + x.norm_sq())
            / integer(4);
        assert_eq!(
            bilinear_product(&real, &real),
            GaussianRat::real(energy.clone())
        );
        assert_eq!(energy, hermitian_energy(&real));
    }

    /// Lean `imaginary_state_witness`: the complex-fluid state `U = i δ₀` has `Σ U·U = −1` against
    /// `Σ |U|² = 1`, and its transform is not Hermitian: it is not a real field's chart.
    #[test]
    fn an_imaginary_state_is_not_a_real_fields_chart() {
        for order in [1, 2, 4] {
            let chart = FourierChart::new(order).unwrap();
            let mut state = vec![GaussianRat::zero(); order];
            state[0] = GaussianRat::i();
            assert_eq!(
                bilinear_product(&state, &state),
                GaussianRat::from_i64(-1, 0)
            );
            assert_eq!(hermitian_energy(&state), integer(1));
            assert!(!is_real(&state));
            assert!(!chart.is_hermitian(&chart.transform(&state).unwrap()));
        }
    }

    /// The chart is refused where its roots of unity leave the Gaussian rationals.
    #[test]
    fn a_chart_without_gaussian_roots_is_refused() {
        assert_eq!(
            FourierChart::new(3),
            Err(FluidError::NotAGaussianRoot { order: 3 })
        );
    }
}
