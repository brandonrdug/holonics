use super::foundation::{RealizerSextuple, monic_square_root_remainder, poly_eval, poly_mul};
use crate::rational_polynomial::{RationalPolynomial, rational_roots_by_lifting};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};
// ---------------------------------------------------------------------------------------------
// solving for the family's linear sections
// ---------------------------------------------------------------------------------------------

/// A section of the surface whose abscissa is linear in the parameter: `x(T) = slope·T + intercept`
/// with `r(x(T), T)` a perfect square in `Q[T]`.
///
/// The twelve Mestre realizers are the degenerate case `x = a_i ± T`, where the family polynomial
/// vanishes identically along the line. Every other linear section is an element of the surface's
/// Mordell–Weil group that the construction did not force, and each one raises the rank **every**
/// fibre inherits.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearSection {
    pub slope: BigRational,
    pub intercept: BigRational,
}

impl RealizerSextuple {
    /// The monic square root's coefficients `g_k(T)`, the companion of
    /// [`Self::remainder_polynomials`].
    pub fn monic_root_polynomials(&self) -> [Vec<BigRational>; 7] {
        let samples: Vec<BigRational> = (0..14)
            .map(|t| BigRational::from_integer(BigInt::from(t as i64)))
            .collect();
        let rows: Vec<Vec<BigRational>> = samples
            .iter()
            .map(|t| {
                let mut product = vec![BigRational::one()];
                for a in self.values.iter() {
                    product = poly_mul(&product, &[a * a - t * t, -(a + a), BigRational::one()]);
                }
                monic_square_root_remainder(&product, 6)
            })
            .collect();
        std::array::from_fn(|k| {
            let mut accumulated = vec![BigRational::zero(); samples.len()];
            for (i, xi) in samples.iter().enumerate() {
                let mut numerator = vec![BigRational::one()];
                let mut denominator = BigRational::one();
                for (j, xj) in samples.iter().enumerate() {
                    if i == j {
                        continue;
                    }
                    numerator = poly_mul(&numerator, &[-xj.clone(), BigRational::one()]);
                    denominator *= xi - xj;
                }
                let weight = &rows[i][k] / &denominator;
                for (slot, c) in accumulated.iter_mut().zip(numerator.iter()) {
                    *slot += c * &weight;
                }
            }
            while accumulated.len() > 1 && accumulated.last().is_some_and(|c| c.is_zero()) {
                accumulated.pop();
            }
            accumulated
        })
    }

    /// `r(slope·T + intercept, T)` as one polynomial in the parameter.
    pub fn remainder_along(
        &self,
        remainder: &[Vec<BigRational>; 5],
        slope: &BigRational,
        intercept: &BigRational,
    ) -> Vec<BigRational> {
        let line = vec![intercept.clone(), slope.clone()];
        let mut out = vec![BigRational::zero()];
        let mut power = vec![BigRational::one()];
        for coefficient in remainder.iter() {
            let term = poly_mul(coefficient, &power);
            let width = out.len().max(term.len());
            let mut sum = vec![BigRational::zero(); width];
            for (i, c) in out.iter().enumerate() {
                sum[i] += c;
            }
            for (i, c) in term.iter().enumerate() {
                sum[i] += c;
            }
            out = sum;
            power = poly_mul(&power, &line);
        }
        while out.len() > 1 && out.last().is_some_and(|c| c.is_zero()) {
            out.pop();
        }
        out
    }
}

/// Whether a polynomial is a perfect square, by its squarefree decomposition: every distinct
/// factor must occur to an even multiplicity. `squarefree_part` cannot answer this — it returns the
/// radical, so `h^2` comes back as `h` rather than as a constant.
#[cfg(test)]
pub(crate) fn is_perfect_square_for_test(c: &[BigRational]) -> bool {
    is_perfect_square(c)
}

fn is_perfect_square(coefficients: &[BigRational]) -> bool {
    let polynomial = RationalPolynomial::new(coefficients.to_vec());
    match polynomial.degree() {
        None => false,
        Some(0) => true,
        Some(_) => match polynomial.squarefree_decomposition() {
            Ok(decomposition) => decomposition.iter().all(|(multiplicity, factor)| {
                multiplicity % 2 == 0 || factor.degree().unwrap_or(0) == 0
            }),
            Err(_) => false,
        },
    }
}

impl RealizerSextuple {
    /// **Solve** for every non-forced linear section. No search, no window, no sampling.
    ///
    /// Along `x = αT + β` the family polynomial splits into twelve known linear forms, so
    /// `g^2 - p = h^2` forces `g ∓ h` to be complementary six-subsets of them. Matching leading
    /// coefficients gives `lc = (α²−1)³`, hence the constant of proportionality is one and the
    /// split is balanced — three forms of each slope, four hundred partitions. The coefficient
    /// ladder then collapses: `T^6`, `T^5` and `T^3` are identities that cannot fail, `T^4` is
    /// **free of β** and is a quartic whose rational roots are the slopes, and `T^2` is a quadratic
    /// in β. Both are handed to the exhaustive rational-root census.
    ///
    /// The final admission is the perfect-square test on the composed polynomial **and** a
    /// non-degeneracy check: a sextuple can satisfy every coefficient identity while its quartic
    /// has identically vanishing discriminant, in which case `r` is a square along *every* line and
    /// the "sections" are an artefact of a surface that is not elliptic. That check is the
    /// difference between a solution of the equations and a curve.
    pub fn linear_sections(&self) -> Vec<LinearSection> {
        let remainder = self.remainder_polynomials();
        let root = self.monic_root_polynomials();
        if !self.quartic_is_nondegenerate(&remainder) {
            return Vec::new();
        }
        let a = &self.values;
        let subsets: Vec<[usize; 3]> = {
            let mut out = Vec::new();
            for i in 0..6 {
                for j in i + 1..6 {
                    for k in j + 1..6 {
                        out.push([i, j, k]);
                    }
                }
            }
            out
        };
        let sigma = |s: &[usize; 3]| s.iter().map(|i| a[*i].clone()).sum::<BigRational>();
        let tau = |s: &[usize; 3]| &a[s[0]] * &a[s[1]] + &a[s[0]] * &a[s[2]] + &a[s[1]] * &a[s[2]];
        let complement = |s: &[usize; 3]| {
            let mut out = [0usize; 3];
            let mut n = 0;
            for i in 0..6 {
                if !s.contains(&i) {
                    out[n] = i;
                    n += 1;
                }
            }
            out
        };
        // `2·Σ_k α^k · g_k[4−k]`, the numerator of the receiver term, exactly
        let mut receiver = vec![BigRational::zero(); 5];
        for k in 0..5 {
            if let Some(c) = root[k].get(4 - k) {
                receiver[k] = c * BigRational::from_integer(BigInt::from(2));
            }
        }
        let one = BigRational::one();
        let mono = |c: BigRational, d: usize| {
            let mut v = vec![BigRational::zero(); d + 1];
            v[d] = c;
            v
        };
        let m = vec![-one.clone(), one.clone()]; // α − 1
        let n = vec![one.clone(), one.clone()]; // α + 1
        let mn = poly_mul(&m, &n);
        let m_n3 = poly_mul(&m, &poly_mul(&n, &poly_mul(&n, &n)));
        let m3_n = poly_mul(&n, &poly_mul(&m, &poly_mul(&m, &m)));
        let mn2 = poly_mul(&mn, &mn);

        let mut found: Vec<LinearSection> = Vec::new();
        let mut slopes: Vec<BigRational> = Vec::new();
        for sm in subsets.iter() {
            for sp in subsets.iter() {
                let smb = complement(sm);
                let spb = complement(sp);
                let minus = tau(sm) + tau(&smb);
                let plus = tau(sp) + tau(&spb);
                let cross = sigma(sm) * sigma(sp) + sigma(&smb) * sigma(&spb);
                let mut numerator = poly_mul(&m_n3, &mono(minus, 0));
                for (i, c) in poly_mul(&mn2, &mono(cross, 0)).iter().enumerate() {
                    if i < numerator.len() {
                        numerator[i] += c;
                    } else {
                        numerator.push(c.clone());
                    }
                }
                for (i, c) in poly_mul(&m3_n, &mono(plus, 0)).iter().enumerate() {
                    if i < numerator.len() {
                        numerator[i] += c;
                    } else {
                        numerator.push(c.clone());
                    }
                }
                for (i, c) in receiver.iter().enumerate() {
                    if i < numerator.len() {
                        numerator[i] -= c;
                    } else {
                        numerator.push(-c.clone());
                    }
                }
                let polynomial = RationalPolynomial::new(numerator);
                if polynomial.degree().unwrap_or(0) == 0 {
                    continue;
                }
                let Ok(census) = rational_roots_by_lifting(&polynomial) else {
                    continue;
                };
                for slope in census {
                    if slope == one || slope == -one.clone() || slope.is_zero() {
                        continue;
                    }
                    if !slopes.contains(&slope) {
                        slopes.push(slope);
                    }
                }
            }
        }
        // for each solved slope, the intercept from the perfect-square condition
        for slope in slopes {
            for intercept in self.intercepts_for(&remainder, &slope) {
                let composed = self.remainder_along(&remainder, &slope, &intercept);
                if is_perfect_square(&composed) {
                    let section = LinearSection {
                        slope: slope.clone(),
                        intercept,
                    };
                    if !found.contains(&section) {
                        found.push(section);
                    }
                }
            }
        }
        found
    }

    /// Candidate intercepts at a solved slope, from the first coefficient identity that is not an
    /// identity. Sampled and interpolated exactly, then handed to the rational-root census.
    fn intercepts_for(
        &self,
        remainder: &[Vec<BigRational>; 5],
        slope: &BigRational,
    ) -> Vec<BigRational> {
        // the square-root remainder of the composed polynomial, as a function of the intercept
        let samples: Vec<BigRational> = (0..9)
            .map(|t| BigRational::from_integer(BigInt::from(t as i64)))
            .collect();
        let mut out: Vec<BigRational> = Vec::new();
        for index in 0..8usize {
            let values: Vec<BigRational> = samples
                .iter()
                .map(|b| {
                    let composed = self.remainder_along(remainder, slope, b);
                    monic_square_root_remainder_scaled(&composed)
                        .get(index)
                        .cloned()
                        .unwrap_or_else(BigRational::zero)
                })
                .collect();
            let mut accumulated = vec![BigRational::zero(); samples.len()];
            for (i, xi) in samples.iter().enumerate() {
                let mut numerator = vec![BigRational::one()];
                let mut denominator = BigRational::one();
                for (j, xj) in samples.iter().enumerate() {
                    if i == j {
                        continue;
                    }
                    numerator = poly_mul(&numerator, &[-xj.clone(), BigRational::one()]);
                    denominator *= xi - xj;
                }
                let weight = &values[i] / &denominator;
                for (slot, c) in accumulated.iter_mut().zip(numerator.iter()) {
                    *slot += c * &weight;
                }
            }
            let polynomial = RationalPolynomial::new(accumulated);
            if polynomial.degree().unwrap_or(0) == 0 {
                continue;
            }
            if let Ok(census) = rational_roots_by_lifting(&polynomial) {
                for root in census {
                    if !out.contains(&root) {
                        out.push(root);
                    }
                }
            }
        }
        out
    }

    /// The quartic's discriminant `4I³ − J²` at one generic parameter. A sextuple can satisfy every
    /// coefficient identity while this vanishes identically, and then `r` is a square along every
    /// line: the surface is not elliptic and its "sections" are an artefact.
    fn quartic_is_nondegenerate(&self, remainder: &[Vec<BigRational>; 5]) -> bool {
        let probe = BigRational::from_integer(BigInt::from(1009));
        let value = |k: usize| poly_eval(&remainder[k], &probe);
        let (e, d, c, b, a) = (value(0), value(1), value(2), value(3), value(4));
        if a.is_zero() {
            return false;
        }
        let twelve = BigRational::from_integer(BigInt::from(12));
        let three = BigRational::from_integer(BigInt::from(3));
        let i = &twelve * &a * &e - &three * &b * &d + &c * &c;
        let j = BigRational::from_integer(BigInt::from(72)) * &a * &c * &e
            + BigRational::from_integer(BigInt::from(9)) * &b * &c * &d
            - BigRational::from_integer(BigInt::from(27)) * &a * &d * &d
            - BigRational::from_integer(BigInt::from(27)) * &e * &b * &b
            - BigRational::from_integer(BigInt::from(2)) * &c * &c * &c;
        let discriminant = BigRational::from_integer(BigInt::from(4)) * &i * &i * &i - &j * &j;
        !discriminant.is_zero()
    }
}

/// The square-root remainder of an even-degree polynomial against its half-degree square root,
/// without requiring the leading coefficient to be one. Returns the remainder's coefficients.
///
/// The degree is **not** twelve. Along a line `g^2` and `p` both lead with `(α²−1)^6` and cancel,
/// so `r` restricted to a line has degree eight and its square root degree four. Assuming twelve
/// made this return zeros and the solver return nothing.
fn monic_square_root_remainder_scaled(f: &[BigRational]) -> Vec<BigRational> {
    let degree = f.len().saturating_sub(1);
    if degree < 2 || degree % 2 == 1 {
        return Vec::new();
    }
    let half = degree / 2;
    // h has degree 6; h_6^2 = f_12 need not be rational, so work with the *scaled* square root
    // s = h / h_6, which is monic, and the remainder of f / f_12 against s^2.
    let lead = f[degree].clone();
    if lead.is_zero() {
        return Vec::new();
    }
    let normalised: Vec<BigRational> = f.iter().map(|c| c / &lead).collect();
    let s = monic_square_root_remainder(&normalised, half);
    let square = poly_mul(&s, &s);
    (0..half)
        .map(|i| {
            let left = square.get(i).cloned().unwrap_or_else(BigRational::zero);
            let right = normalised.get(i).cloned().unwrap_or_else(BigRational::zero);
            left - right
        })
        .collect()
}
