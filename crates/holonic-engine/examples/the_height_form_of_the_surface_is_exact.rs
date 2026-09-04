//! The height form of a Mestre surface, exactly: Shioda's formula on the sections that stand.
//!
//! On an elliptic surface `E → P¹` with zero section `O`, the Néron–Tate height pairing of
//! sections is arithmetic on the surface (Shioda 1990):
//!
//! ```text
//!     ⟨P, P⟩ = 2χ + 2(P·O) − Σ_v contr_v(P),        ⟨P, Q⟩ = ½ (⟨P+Q,P+Q⟩ − ⟨P,P⟩ − ⟨Q,Q⟩)
//! ```
//!
//! `χ` is the surface's holomorphic Euler characteristic, `P·O` the intersection number with the
//! zero section (half the pole order of `x_P`), and `contr_v` the correction from the reducible
//! fibre at `v` when `P` passes through its singular point — Silverman's local formulas (1988):
//! at a multiplicative place of order `N`, `α(1−α)N` with `α = min(ord_v ψ₂, N/2)/N`; at an
//! additive place, `(2/3) ord_v ψ₂` if `ord_v ψ₃ ≥ 3 ord_v ψ₂`, else `¼ ord_v ψ₃`; with
//! `ψ₂ = 2y`, `ψ₃ = 3x⁴ + 6Ax² + 12Bx − A²` on the short model `y² = x³ + Ax + B`. **Every term
//! is a rational read off polynomials over `ℚ[T]`** — the transcendental height on one fibre is,
//! on the surface, exact.
//!
//! The chain: the quartic `y² = r(x,T)` of the family (first divided by its `T²` content, which
//! made the naive model non-minimal at `T = 0`), the Weierstrass chart through the forced
//! section `a₁ + T` over `ℚ(T)`, the short form, the global minimal model over `ℚ[T]` (scaling
//! out every `v` with `v⁴ | A`, `v⁶ | B`) and at infinity (`χ` is the least `m` with
//! `deg A ≤ 4m`, `deg B ≤ 6m`), the bad places from the squarefree decomposition of `Δ` (never
//! factored: orders are partitioned by gcds), the sections carried through every step, and the
//! group law over `ℚ(T)` for the polarization. The output is the Gram matrix of the height form
//! on the twenty-three sections other than `O`, its exact inertia, the determinant of the form
//! on the independent ones — the regulator of the sublattice they span — and the exact
//! `ℚ`-relations among the dependent sections, read off the Gram kernel (the height pairing is
//! nondegenerate on `MW ⊗ ℚ`, so a kernel vector of the Gram matrix is a relation in the group).
//!
//! Every gcd over `ℚ[T]` runs through `modular_monic_gcd`: the Euclidean sequence over `ℚ` grew
//! its coefficients past the process aperture on the very first family, and the modular route
//! returns the same monic gcd with no growth. The deed is sectioned per family (`[label ...]`)
//! so each runs under its own aperture and writes its own receipt.

use holonic_engine::RealizerSextuple;
use holonic_engine::rational_polynomial::{RationalPolynomial, modular_monic_gcd};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::collections::BTreeMap;
use std::fs;
use std::time::Instant;

type Rat = BigRational;
type Poly = RationalPolynomial;

const OUTPUT: &str = ".local/artifacts/the_height_form_of_the_surface_is_exact";

fn rational(values: [i64; 6]) -> [Rat; 6] {
    values.map(|v| Rat::from_integer(BigInt::from(v)))
}
fn int(v: i64) -> Rat {
    Rat::from_integer(BigInt::from(v))
}
fn constant(value: Rat) -> Poly {
    Poly::new(vec![value])
}
fn poly(c: &[Rat]) -> Poly {
    Poly::new(c.to_vec())
}

// --- rational functions over ℚ[T] --------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
struct Frac {
    num: Poly,
    den: Poly,
}

impl Frac {
    fn new(num: Poly, den: Poly) -> Self {
        assert!(!den.is_zero(), "zero denominator");
        if num.is_zero() {
            return Self {
                num: Poly::zero(),
                den: Poly::one(),
            };
        }
        let g = modular_monic_gcd(&num, &den).unwrap_or_else(|_| Poly::one());
        let (mut num, mut den) = if g.degree().unwrap_or(0) > 0 {
            (
                num.divided_exactly_by(&g).unwrap(),
                den.divided_exactly_by(&g).unwrap(),
            )
        } else {
            (num, den)
        };
        let lead = den.leading().cloned().unwrap();
        let inverse = Rat::one() / lead;
        num = num.scaled(&inverse);
        den = den.scaled(&inverse);
        Self { num, den }
    }
    fn from_poly(p: Poly) -> Self {
        Self::new(p, Poly::one())
    }
    fn is_zero(&self) -> bool {
        self.num.is_zero()
    }
    fn add(&self, o: &Self) -> Self {
        Self::new(
            self.num.times(&o.den).plus(&o.num.times(&self.den)),
            self.den.times(&o.den),
        )
    }
    fn sub(&self, o: &Self) -> Self {
        Self::new(
            self.num.times(&o.den).minus(&o.num.times(&self.den)),
            self.den.times(&o.den),
        )
    }
    fn mul(&self, o: &Self) -> Self {
        Self::new(self.num.times(&o.num), self.den.times(&o.den))
    }
    fn div(&self, o: &Self) -> Self {
        Self::new(self.num.times(&o.den), self.den.times(&o.num))
    }
    fn scale(&self, r: &Rat) -> Self {
        Self::new(self.num.scaled(r), self.den.clone())
    }
    fn neg(&self) -> Self {
        Self::new(self.num.negated(), self.den.clone())
    }
    fn sq(&self) -> Self {
        self.mul(self)
    }
}

/// The order of `f` at `U = 0` for a polynomial.
fn ord_zero(f: &Poly) -> Option<usize> {
    if f.is_zero() {
        return None;
    }
    (0..).find(|k| !f.coefficient(*k).is_zero())
}

/// `U^weight · f(1/U)`: the reversal into the chart at infinity.
fn reverse(f: &Poly, weight: usize) -> Poly {
    let d = f.degree().unwrap_or(0);
    assert!(
        d <= weight,
        "degree {d} exceeds weight {weight} at infinity"
    );
    let mut c = vec![Rat::zero(); weight + 1];
    for k in 0..=d {
        c[weight - k] = f.coefficient(k);
    }
    Poly::new(c)
}

/// Squarefree decomposition as a map multiplicity → squarefree factor (monic), by Yun's
/// algorithm over the modular gcd: `a₀ = gcd(f, f′)`, `b₁ = f/a₀`, `c₁ = f′/a₀`, `d₁ = c₁ − b₁′`,
/// then `aᵢ = gcd(bᵢ, dᵢ)`, `bᵢ₊₁ = bᵢ/aᵢ`, `cᵢ₊₁ = dᵢ/aᵢ`, `dᵢ₊₁ = cᵢ₊₁ − bᵢ₊₁′`.
fn decomposition(f: &Poly) -> BTreeMap<u32, Poly> {
    let mut out = BTreeMap::new();
    if f.is_zero() || f.degree().unwrap_or(0) == 0 {
        return out;
    }
    let f = f.made_monic();
    let df = f.derivative();
    let a0 = gcd(&f, &df);
    let mut b = exact_div(&f, &a0);
    let mut c = exact_div(&df, &a0);
    let mut d = c.minus(&b.derivative());
    let mut i = 1u32;
    while b.degree().unwrap_or(0) > 0 {
        let a = gcd(&b, &d);
        if a.degree().unwrap_or(0) > 0 {
            out.insert(i, a.clone());
        }
        b = exact_div(&b, &a);
        c = exact_div(&d, &a);
        d = c.minus(&b.derivative());
        i += 1;
    }
    out
}

fn squarefree_part(f: &Poly) -> Poly {
    if f.is_zero() || f.degree().unwrap_or(0) == 0 {
        return Poly::one();
    }
    exact_div(f, &gcd(f, &f.derivative())).made_monic()
}

fn gcd(a: &Poly, b: &Poly) -> Poly {
    if a.is_zero() {
        return b.made_monic();
    }
    if b.is_zero() {
        return a.made_monic();
    }
    modular_monic_gcd(a, b).unwrap_or_else(|_| Poly::one())
}

fn exact_div(a: &Poly, b: &Poly) -> Poly {
    a.divided_exactly_by(b).expect("exact division")
}

// --- the short Weierstrass model over ℚ[T] and its sections ----------------------------------

#[derive(Clone, Debug)]
struct Model {
    a: Poly,
    b: Poly,
}

impl Model {
    fn discriminant(&self) -> Poly {
        let a3 = self.a.times(&self.a).times(&self.a).scaled(&int(4));
        let b2 = self.b.times(&self.b).scaled(&int(27));
        a3.plus(&b2).scaled(&int(-16))
    }
}

#[derive(Clone, Debug)]
struct Point {
    label: String,
    x: Frac,
    y: Frac,
}

fn on_model(m: &Model, p: &Point) -> bool {
    let rhs =
        p.x.mul(&p.x)
            .mul(&p.x)
            .add(&Frac::from_poly(m.a.clone()).mul(&p.x))
            .add(&Frac::from_poly(m.b.clone()));
    p.y.sq() == rhs
}

/// The group law on `y² = x³ + Ax + B` over ℚ(T). `None` is the point at infinity.
fn add_points(
    m: &Model,
    p: &Option<(Frac, Frac)>,
    q: &Option<(Frac, Frac)>,
) -> Option<(Frac, Frac)> {
    let (Some((x1, y1)), Some((x2, y2))) = (p, q) else {
        return p.clone().or_else(|| q.clone());
    };
    let lambda = if x1 == x2 {
        if y1.add(y2).is_zero() {
            return None;
        }
        let three_x2 = x1.sq().scale(&int(3)).add(&Frac::from_poly(m.a.clone()));
        three_x2.div(&y1.scale(&int(2)))
    } else {
        y2.sub(y1).div(&x2.sub(x1))
    };
    let x3 = lambda.sq().sub(x1).sub(x2);
    let y3 = lambda.mul(&x1.sub(&x3)).sub(y1);
    Some((x3, y3))
}

/// Silverman's local corrections summed over the finite bad places, by gcd partitions.
fn finite_corrections(m: &Model, delta_dec: &BTreeMap<u32, Poly>, x: &Frac, y: &Frac) -> Rat {
    let mut total = Rat::zero();
    // v-integrality: a place dividing the denominator of x is where P reduces to O — nonsingular
    let poles = squarefree_part(&x.den);
    // ψ₂ = 2y and ψ₃ = 3x⁴ + 6Ax² + 12Bx − A², as rational functions; their numerators carry the orders
    let psi2 = y.scale(&int(2));
    let a = Frac::from_poly(m.a.clone());
    let b = Frac::from_poly(m.b.clone());
    let x2 = x.sq();
    let psi3 = x2
        .sq()
        .scale(&int(3))
        .add(&a.mul(&x2).scale(&int(6)))
        .add(&b.mul(x).scale(&int(12)))
        .sub(&a.sq());
    let singular_x = x2.scale(&int(3)).add(&a); // 3x² + A
    let psi2_dec = decomposition(&psi2.num);
    let psi3_dec = decomposition(&psi3.num);
    let sing_support = squarefree_part(&singular_x.num);
    for (n, d_n) in delta_dec.iter() {
        // places of Δ-order n, split into multiplicative (v ∤ A) and additive (v | A)
        let d_add = gcd(d_n, &m.a);
        let d_mult = if d_add.degree().unwrap_or(0) > 0 {
            exact_div(d_n, &d_add)
        } else {
            d_n.clone()
        };
        for (support, additive) in [(d_mult, false), (d_add, true)] {
            if support.degree().unwrap_or(0) == 0 {
                continue;
            }
            // remove places where P reduces to O or to a nonsingular point
            let mut s = support.clone();
            let with_pole = gcd(&s, &poles);
            if with_pole.degree().unwrap_or(0) > 0 {
                s = exact_div(&s, &with_pole);
            }
            let s = gcd(&s, &sing_support); // 3x²+A ≡ 0
            if s.degree().unwrap_or(0) == 0 {
                continue;
            }
            // partition s by ord(ψ₂) = o2 ≥ 1 (places with ord(ψ₂) = 0 are nonsingular)
            for (o2, y_k) in psi2_dec.iter() {
                let s2 = gcd(&s, y_k);
                if s2.degree().unwrap_or(0) == 0 {
                    continue;
                }
                if !additive {
                    let n_rat = int(*n as i64);
                    let alpha = {
                        let o = int(*o2 as i64);
                        let half_n = &n_rat / int(2);
                        if o < half_n {
                            o / &n_rat
                        } else {
                            half_n / &n_rat
                        }
                    };
                    let contr = &alpha * (Rat::one() - &alpha) * &n_rat;
                    total += contr * int(s2.degree().unwrap_or(0) as i64);
                } else {
                    // partition further by ord(ψ₃) = o3 (o3 = 0 where ψ₃ is a unit)
                    let mut covered = Poly::one();
                    for (o3, p_k) in psi3_dec.iter() {
                        let s3 = gcd(&s2, p_k);
                        if s3.degree().unwrap_or(0) == 0 {
                            continue;
                        }
                        covered = covered.times(&s3);
                        let contr = if *o3 >= 3 * *o2 {
                            int(2 * *o2 as i64) / int(3)
                        } else {
                            int(*o3 as i64) / int(4)
                        };
                        total += contr * int(s3.degree().unwrap_or(0) as i64);
                    }
                    let rest = if covered.degree().unwrap_or(0) > 0 {
                        exact_div(&s2, &covered)
                    } else {
                        s2.clone()
                    };
                    if rest.degree().unwrap_or(0) > 0 {
                        // ord(ψ₃) = 0 < 3 o2: contr = 0
                    }
                }
            }
        }
    }
    total
}

/// The correction at infinity: the same law in the chart `U = 1/T` at `U = 0`.
fn infinity_correction(m: &Model, chi: usize, delta: &Poly, x: &Frac, y: &Frac) -> (Rat, usize) {
    // transformed model A'(U) = U^{4χ} A(1/U), B'(U) = U^{6χ} B(1/U); point x' = U^{2χ} x, y' = U^{3χ} y
    let a_inf = reverse(&m.a, 4 * chi);
    let b_inf = reverse(&m.b, 6 * chi);
    let delta_inf_order = 12 * chi - delta.degree().unwrap_or(0);
    let dx = x.num.degree().unwrap_or(0) as i64 - x.den.degree().unwrap_or(0) as i64; // degree of x as a rational function
    let dy = y.num.degree().unwrap_or(0) as i64 - y.den.degree().unwrap_or(0) as i64;
    // ord_U x' = 2χ − deg x ; ord_U y' = 3χ − deg y
    let ord_x = 2 * chi as i64 - dx;
    let ord_y = if y.is_zero() {
        i64::MAX
    } else {
        3 * chi as i64 - dy
    };
    if ord_x < 0 {
        // P meets O at infinity: pole of x' of order −ord_x (even), no singular reduction
        return (Rat::zero(), ((-ord_x) / 2) as usize);
    }
    if delta_inf_order == 0 {
        return (Rat::zero(), 0);
    }
    // the reduced point at U = 0 must be the singular point: ord_U(2y') ≥ 1 and ord_U(3x'² + A') ≥ 1
    if ord_y < 1 {
        return (Rat::zero(), 0);
    }
    // form x'(U), y'(U) as rational functions in U and the singular-point test
    let xu = Frac::new(
        reverse(&x.num, x.num.degree().unwrap_or(0)),
        reverse(&x.den, x.den.degree().unwrap_or(0)),
    );
    let shift_x = 2 * chi as i64 - dx; // x' = U^{shift} · xu-ish: we only need orders
    let _ = shift_x;
    // 3x'² + A' at U=0: use degrees: ord_U(3 x'^2 + A') ≥ 1 ⇔ the U^0 coefficients cancel
    let a_lead = a_inf.coefficient(0);
    let x_lead = if ord_x == 0 {
        xu.num.coefficient(0) / xu.den.coefficient(0)
    } else {
        Rat::zero()
    };
    let singular = (&x_lead * &x_lead * int(3) + a_lead).is_zero();
    if !singular {
        return (Rat::zero(), 0);
    }
    let n = delta_inf_order;
    let o2 = ord_y as usize; // ord_U(2y')
    let multiplicative = ord_zero(&a_inf) == Some(0);
    if multiplicative {
        let n_rat = int(n as i64);
        let o = int(o2 as i64);
        let half_n = &n_rat / int(2);
        let alpha = if o < half_n {
            o / &n_rat
        } else {
            half_n / &n_rat
        };
        return (&alpha * (Rat::one() - &alpha) * &n_rat, 0);
    }
    // additive: need ord_U ψ₃'; form ψ₃' from the transformed coordinates exactly
    let xp = Frac::new(
        reverse(&x.num, x.num.degree().unwrap_or(0)).times(&{
            let mut u = vec![Rat::zero(); ord_x.max(0) as usize + 1];
            u[ord_x.max(0) as usize] = Rat::one();
            Poly::new(u)
        }),
        reverse(&x.den, x.den.degree().unwrap_or(0)),
    );
    let a_f = Frac::from_poly(a_inf.clone());
    let b_f = Frac::from_poly(b_inf.clone());
    let x2 = xp.sq();
    let psi3 = x2
        .sq()
        .scale(&int(3))
        .add(&a_f.mul(&x2).scale(&int(6)))
        .add(&b_f.mul(&xp).scale(&int(12)))
        .sub(&a_f.sq());
    let o3 =
        ord_zero(&psi3.num).unwrap_or(usize::MAX) as i64 - ord_zero(&psi3.den).unwrap_or(0) as i64;
    let o3 = o3.max(0) as usize;
    let contr = if o3 >= 3 * o2 {
        int(2 * o2 as i64) / int(3)
    } else {
        int(o3 as i64) / int(4)
    };
    (contr, 0)
}

/// `P·O` at finite places: half the pole order of `x_P`, summed with degrees.
fn finite_pole_meeting(x: &Frac) -> Rat {
    let mut total = Rat::zero();
    for (j, e_j) in decomposition(&x.den) {
        total += int(e_j.degree().unwrap_or(0) as i64) * int(j as i64) / int(2);
    }
    total
}

/// The exact kernel of a symmetric rational matrix: one relation per non-pivot column, each
/// expressing that column's section through the pivoted ones.
fn gram_kernel(gram: &[Vec<Rat>]) -> Vec<Vec<Rat>> {
    let n = gram.len();
    let mut a: Vec<Vec<Rat>> = gram.to_vec();
    let mut pivot_columns: Vec<usize> = Vec::new();
    let mut row = 0usize;
    for col in 0..n {
        let Some(r) = (row..n).find(|&r| !a[r][col].is_zero()) else {
            continue;
        };
        a.swap(row, r);
        let inverse = Rat::one() / &a[row][col];
        for j in 0..n {
            a[row][j] = &a[row][j] * &inverse;
        }
        for i in 0..n {
            if i != row && !a[i][col].is_zero() {
                let factor = a[i][col].clone();
                for j in 0..n {
                    let update = &factor * &a[row][j];
                    a[i][j] -= update;
                }
            }
        }
        pivot_columns.push(col);
        row += 1;
        if row == n {
            break;
        }
    }
    let mut kernel = Vec::new();
    for free in 0..n {
        if pivot_columns.contains(&free) {
            continue;
        }
        let mut v = vec![Rat::zero(); n];
        v[free] = Rat::one();
        for (r, &pc) in pivot_columns.iter().enumerate() {
            v[pc] = -a[r][free].clone();
        }
        kernel.push(v);
    }
    kernel
}

fn integer_gcd(a: &BigInt, b: &BigInt) -> BigInt {
    let (mut a, mut b) = (a.abs(), b.abs());
    while !b.is_zero() {
        let r = &a % &b;
        a = std::mem::replace(&mut b, r);
    }
    a
}

/// The index of the pivot sublattice inside the `ℤ`-span of every section, from the Hermite
/// form of the integer coordinate matrix: with `d` the common denominator of the kernel
/// coordinates, the rows `d·(coordinates of each section in the pivot basis)` generate a lattice
/// whose Hermite-form determinant divided by `d^rank` is `1 / [span : pivots]`.
fn span_index(kernel: &[Vec<Rat>], pivots: &[usize], n: usize) -> BigInt {
    let rank = pivots.len();
    // coordinates of every section in the pivot basis: pivots are unit vectors; a free column's
    // kernel vector v (with v[free] = 1) says free = −Σ_{pc} v[pc]·pc
    let mut rows: Vec<Vec<Rat>> = Vec::new();
    for i in 0..n {
        if let Some(k) = pivots.iter().position(|&p| p == i) {
            let mut r = vec![Rat::zero(); rank];
            r[k] = Rat::one();
            rows.push(r);
        } else if let Some(v) = kernel.iter().find(|v| v[i].is_one()) {
            rows.push(pivots.iter().map(|&pc| -v[pc].clone()).collect());
        }
    }
    let mut d = BigInt::one();
    for r in &rows {
        for c in r {
            let den = c.denom().clone();
            let g = integer_gcd(&d, &den);
            d = &d / g * den;
        }
    }
    let mut m: Vec<Vec<BigInt>> = rows
        .iter()
        .map(|r| {
            r.iter()
                .map(|c| (c * Rat::from_integer(d.clone())).to_integer())
                .collect()
        })
        .collect();
    // Hermite form by row operations (Euclid down each column)
    let mut det = BigInt::one();
    let mut row = 0usize;
    for col in 0..rank {
        loop {
            let nonzero: Vec<usize> = (row..m.len()).filter(|&i| !m[i][col].is_zero()).collect();
            if nonzero.is_empty() {
                break;
            }
            let &best = nonzero.iter().min_by_key(|&&i| m[i][col].abs()).unwrap();
            m.swap(row, best);
            let mut reduced = true;
            for i in (row + 1)..m.len() {
                if m[i][col].is_zero() {
                    continue;
                }
                let q = &m[i][col] / &m[row][col];
                for j in col..rank {
                    let update = &q * &m[row][j];
                    m[i][j] -= update;
                }
                if !m[i][col].is_zero() {
                    reduced = false;
                }
            }
            if reduced {
                break;
            }
        }
        if row < m.len() && !m[row][col].is_zero() {
            det *= m[row][col].abs();
            row += 1;
        }
    }
    // covolume relative to pivots = det / d^rank ; index = d^rank / det
    let mut d_power = BigInt::one();
    for _ in 0..rank {
        d_power *= &d;
    }
    &d_power / det
}

/// Exact symmetric elimination: rank, inertia, determinant on the pivoted independent set.
fn gram_reading(gram: &[Vec<Rat>]) -> (usize, (usize, usize, usize), Rat, Vec<usize>) {
    let n = gram.len();
    let mut a: Vec<Vec<Rat>> = gram.to_vec();
    let (mut positive, mut negative) = (0usize, 0usize);
    let mut pivots: Vec<usize> = Vec::new();
    let mut determinant = Rat::one();
    let mut remaining: Vec<usize> = (0..n).collect();
    loop {
        let Some(&k) = remaining.iter().find(|&&k| !a[k][k].is_zero()) else {
            break;
        };
        let pivot = a[k][k].clone();
        if pivot.is_positive() {
            positive += 1
        } else {
            negative += 1
        }
        determinant *= &pivot;
        pivots.push(k);
        remaining.retain(|&i| i != k);
        for &i in remaining.iter() {
            let factor = &a[i][k] / &pivot;
            for &j in remaining.iter() {
                let update = &factor * &a[k][j];
                a[i][j] -= update;
            }
        }
    }
    let mut zero = 0usize;
    let mut handled = vec![false; n];
    let rem = remaining.clone();
    for &i in rem.iter() {
        if handled[i] {
            continue;
        }
        if let Some(&j) = rem
            .iter()
            .find(|&&j| j != i && !handled[j] && !a[i][j].is_zero())
        {
            positive += 1;
            negative += 1;
            handled[i] = true;
            handled[j] = true;
        } else {
            zero += 1;
            handled[i] = true;
        }
    }
    (
        positive + negative,
        (positive, zero, negative),
        determinant,
        pivots,
    )
}

fn main() -> Result<(), String> {
    let published: [(&str, [i64; 6]); 3] = [
        ("159", [-1146, -2304, -654, 3054, 2880, -1830]),
        ("161", [348, -600, -216, 492, 876, -900]),
        ("280", [0, 1075, 1394, 2291, 4186, 4824]),
    ];
    fs::create_dir_all(OUTPUT).map_err(|e| e.to_string())?;
    // `[label ...]` sections the deed per family so each runs under its own process aperture;
    // each family writes `receipt-<label>.txt`, and the combined receipt is assembled from those.
    let requested: Vec<String> = std::env::args().skip(1).collect();
    let mut report = String::new();
    for (label, values) in published {
        if !requested.is_empty() && !requested.iter().any(|r| r == label) {
            continue;
        }
        let started = Instant::now();
        let family = RealizerSextuple::found_after_centring(rational(values))
            .map_err(|e| format!("{e:?}"))?;
        let remainder = family.remainder_polynomials();
        let root = family.monic_root_polynomials();
        let t_poly = Poly::variable();
        // divide out the T² content: r = T² r̃, y = T ỹ
        let t2 = t_poly.times(&t_poly);
        let r: Vec<Poly> = remainder.iter().map(|c| exact_div(&poly(c), &t2)).collect();
        let g: Vec<Poly> = root.iter().map(|c| poly(c)).collect();
        let mut quartic_sections: Vec<(String, Poly, Poly)> = Vec::new();
        for (i, a_i) in family.values().iter().enumerate() {
            for (sign, name) in [(1i64, "+"), (-1i64, "−")] {
                let x = if sign > 0 {
                    t_poly.plus(&constant(a_i.clone()))
                } else {
                    t_poly.negated().plus(&constant(a_i.clone()))
                };
                let mut y = Poly::zero();
                let mut power = Poly::one();
                for gk in g.iter() {
                    y = y.plus(&gk.times(&power));
                    power = power.times(&x);
                }
                quartic_sections.push((format!("a{}{}T", i + 1, name), x, exact_div(&y, &t_poly)));
            }
        }
        for (k, section) in family.linear_sections().iter().enumerate() {
            let composed =
                poly(&family.remainder_along(&remainder, &section.slope, &section.intercept));
            let reduced = exact_div(&composed, &t2);
            // exact square root of `reduced` by the same completed-square routine on the quartic
            let Some(h) = polynomial_square_root(&reduced) else {
                report.push_str(&format!("#{label}: linear section {k}: remainder not a rational square after T² removal\n"));
                continue;
            };
            let x = poly(&[section.intercept.clone(), section.slope.clone()]);
            quartic_sections.push((format!("L{k}+"), x.clone(), h.clone()));
            quartic_sections.push((format!("L{k}−"), x, h.negated()));
        }
        for (name, x, y) in &quartic_sections {
            let mut rx = Poly::zero();
            let mut power = Poly::one();
            for rk in r.iter() {
                rx = rx.plus(&rk.times(&power));
                power = power.times(x);
            }
            if rx != y.times(y) {
                return Err(format!("#{label}: {name} is not on the reduced surface"));
            }
        }
        // Weierstrass chart over ℚ(T) through the first section (a₁ + T): shift x → x + u0, base ordinate q
        let (_, u0, q) = quartic_sections[0].clone();
        let shifted: Vec<Poly> = {
            // coefficients of r̃(x + u0)
            let mut out = vec![Poly::zero(); 5];
            for (i, ci) in r.iter().enumerate() {
                let mut binomial = Rat::one();
                for j in 0..=i {
                    // ci · C(i,j) · u0^{i−j} x^j
                    let mut u_power = Poly::one();
                    for _ in 0..(i - j) {
                        u_power = u_power.times(&u0);
                    }
                    out[j] = out[j].plus(&ci.times(&u_power).scaled(&binomial));
                    binomial = binomial * int((i - j) as i64) / int((j + 1) as i64);
                }
            }
            out
        };
        let (e, d, c, b, a) = (
            Frac::from_poly(shifted[0].clone()),
            Frac::from_poly(shifted[1].clone()),
            Frac::from_poly(shifted[2].clone()),
            Frac::from_poly(shifted[3].clone()),
            Frac::from_poly(shifted[4].clone()),
        );
        let qf = Frac::from_poly(q.clone());
        if e != qf.sq() {
            return Err(format!(
                "#{label}: the base section's ordinate squared is not the shifted constant term"
            ));
        }
        let a1 = d.div(&qf);
        let a2 = c.sub(&d.sq().div(&qf.sq().scale(&int(4))));
        let a3 = qf.mul(&b).scale(&int(2));
        let a4 = qf.sq().mul(&a).scale(&int(-4));
        let a6 = a2.mul(&a4);
        // short form: b2 = a1² + 4a2, b4 = 2a4 + a1a3, b6 = a3² + 4a6; c4, c6; y² = x³ − 27c4 x − 54c6 with (x,y) ↦ (36x + 3b2, 108(2y + a1x + a3))
        let b2 = a1.sq().add(&a2.scale(&int(4)));
        let b4 = a4.scale(&int(2)).add(&a1.mul(&a3));
        let b6 = a3.sq().add(&a6.scale(&int(4)));
        let c4 = b2.sq().sub(&b4.scale(&int(24)));
        let c6 = b2
            .sq()
            .mul(&b2)
            .neg()
            .add(&b2.mul(&b4).scale(&int(36)))
            .sub(&b6.scale(&int(216)));
        let a_short = c4.scale(&int(-27));
        let b_short = c6.scale(&int(-54));
        // clear denominators: with D = lcm of denominators, (A, B) ↦ (D⁴A, D⁶B), (x, y) ↦ (D²x, D³y)
        let dlcm = {
            let g = gcd(&a_short.den, &b_short.den);
            exact_div(&a_short.den.times(&b_short.den), &g)
        };
        let d2 = dlcm.times(&dlcm);
        let d4 = d2.times(&d2);
        let d6 = d4.times(&d2);
        let mut model = Model {
            a: exact_div(&a_short.num.times(&d4), &a_short.den),
            b: exact_div(&b_short.num.times(&d6), &b_short.den),
        };
        let mut points: Vec<Point> = Vec::new();
        for (name, xq, yq) in quartic_sections.iter().skip(1) {
            // carry: u = x − u0; xw = (2q(y+q) + d u)/u², yw = (4q²(y+q) + 2q(d u + c u²) − d² u²/(2q))/u³
            let u = Frac::from_poly(xq.minus(&u0));
            let yq_f = Frac::from_poly(yq.clone());
            let y_plus_q = yq_f.add(&qf);
            let xw = qf
                .mul(&y_plus_q)
                .scale(&int(2))
                .add(&d.mul(&u))
                .div(&u.sq());
            let yw = qf
                .sq()
                .mul(&y_plus_q)
                .scale(&int(4))
                .add(&qf.mul(&d.mul(&u).add(&c.mul(&u.sq()))).scale(&int(2)))
                .sub(&d.sq().mul(&u.sq()).div(&qf.scale(&int(2))))
                .div(&u.sq().mul(&u));
            // to short form and scaled
            let xs = xw.scale(&int(36)).add(&b2.scale(&int(3)));
            let ys = yw
                .scale(&int(2))
                .add(&a1.mul(&xw))
                .add(&a3)
                .scale(&int(108));
            let x = xs.mul(&Frac::from_poly(d2.clone()));
            let y = ys.mul(&Frac::from_poly(dlcm.times(&d2)));
            points.push(Point {
                label: name.clone(),
                x,
                y,
            });
        }
        for p in &points {
            if !on_model(&model, p) {
                return Err(format!("#{label}: {} left the short model", p.label));
            }
        }
        eprintln!(
            "#{label}: short model deg A {} deg B {} carried {} sections at {:.1} s",
            model.a.degree().unwrap_or(0),
            model.b.degree().unwrap_or(0),
            points.len(),
            started.elapsed().as_secs_f64()
        );
        // global minimal model over ℚ[T]: scale out every v with v⁴ | A and v⁶ | B, repeatedly
        let mut scalings: Vec<Poly> = Vec::new();
        loop {
            let a_dec = decomposition(&model.a);
            let b_dec = decomposition(&model.b);
            let mut a4: Poly = Poly::one();
            for (i, f) in a_dec.iter() {
                if *i >= 4 {
                    a4 = a4.times(f);
                }
            }
            let mut b6: Poly = Poly::one();
            for (j, f) in b_dec.iter() {
                if *j >= 6 {
                    b6 = b6.times(f);
                }
            }
            let s = if model.b.is_zero() {
                squarefree_part(&a4)
            } else {
                gcd(&a4, &b6)
            };
            if s.degree().unwrap_or(0) == 0 {
                break;
            }
            let s2 = s.times(&s);
            let s4 = s2.times(&s2);
            let s6 = s4.times(&s2);
            model = Model {
                a: exact_div(&model.a, &s4),
                b: exact_div(&model.b, &s6),
            };
            for p in points.iter_mut() {
                p.x = p.x.div(&Frac::from_poly(s2.clone()));
                p.y = p.y.div(&Frac::from_poly(s2.times(&s)));
            }
            scalings.push(s);
        }
        eprintln!(
            "#{label}: minimal model deg A {} deg B {} after {} scalings at {:.1} s",
            model.a.degree().unwrap_or(0),
            model.b.degree().unwrap_or(0),
            scalings.len(),
            started.elapsed().as_secs_f64()
        );
        let delta = model.discriminant();
        let chi = {
            let da = model.a.degree().unwrap_or(0);
            let db = model.b.degree().unwrap_or(0);
            (1..).find(|m| da <= 4 * m && db <= 6 * m).unwrap()
        };
        let delta_degree = delta.degree().unwrap_or(0);
        let infinity_order = 12 * chi - delta_degree;
        let delta_dec = decomposition(&delta);
        let bad: Vec<String> = delta_dec
            .iter()
            .map(|(n, f)| format!("ord {n}: degree {}", f.degree().unwrap_or(0)))
            .collect();
        let a_inf = reverse(&model.a, 4 * chi);
        let b_inf = reverse(&model.b, 6 * chi);
        let infinity_type = if infinity_order == 0 {
            "I0 (smooth)".to_owned()
        } else {
            let oa = ord_zero(&a_inf).unwrap_or(99);
            let ob = ord_zero(&b_inf).unwrap_or(99);
            if oa == 0 {
                format!("I{infinity_order}")
            } else {
                match (infinity_order, oa, ob) {
                    (2, _, 1) => "II".into(),
                    (3, 1, _) => "III".into(),
                    (4, _, 2) => "IV".into(),
                    (6, _, _) => "I0*".into(),
                    (n, 2, 3) => format!("I{}*", n - 6),
                    (8, _, 4) => "IV*".into(),
                    (9, 3, _) => "III*".into(),
                    (10, _, 5) => "II*".into(),
                    _ => format!("additive ord Δ {infinity_order} (ord A {oa}, ord B {ob})"),
                }
            }
        };
        // heights: h(P) = 2χ + 2 P·O − Σ contr
        let height = |p: &Option<(Frac, Frac)>| -> Rat {
            let Some((x, y)) = p else { return Rat::zero() };
            let (contr_inf, meet_inf) = infinity_correction(&model, chi, &delta, x, y);
            let po = finite_pole_meeting(x) + int(meet_inf as i64);
            int(2 * chi as i64) + int(2) * po
                - finite_corrections(&model, &delta_dec, x, y)
                - contr_inf
        };
        let n = points.len();
        let coords: Vec<Option<(Frac, Frac)>> = points
            .iter()
            .map(|p| Some((p.x.clone(), p.y.clone())))
            .collect();
        let heights: Vec<Rat> = coords.iter().map(&height).collect();
        eprintln!(
            "#{label}: {} heights at {:.1} s: [{}]",
            n,
            started.elapsed().as_secs_f64(),
            heights
                .iter()
                .map(|h| h.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        );
        let mut gram = vec![vec![Rat::zero(); n]; n];
        for i in 0..n {
            gram[i][i] = heights[i].clone();
            for j in (i + 1)..n {
                let sum = add_points(&model, &coords[i], &coords[j]);
                let h_sum = height(&sum);
                let pairing = (&h_sum - &heights[i] - &heights[j]) / int(2);
                gram[i][j] = pairing.clone();
                gram[j][i] = pairing;
            }
            eprintln!(
                "#{label}: row {i} paired at {:.1} s",
                started.elapsed().as_secs_f64()
            );
        }
        let (rank, inertia, determinant, pivots) = gram_reading(&gram);
        let kernel = gram_kernel(&gram);
        let index = span_index(&kernel, &pivots, n);
        let span_regulator = &determinant / Rat::from_integer(&index * &index);
        let relations: Vec<String> = kernel
            .iter()
            .map(|v| {
                v.iter()
                    .enumerate()
                    .filter(|(_, c)| !c.is_zero())
                    .map(|(i, c)| format!("({})·{}", c, points[i].label))
                    .collect::<Vec<_>>()
                    .join(" + ")
                    + " = 0"
            })
            .collect();
        let elapsed = started.elapsed().as_secs_f64();
        let family_report = format!(
            "leaderboard #{label}\n  minimal short model over ℚ[T]: deg A = {}, deg B = {}, deg Δ = {delta_degree}, scalings removed {}; χ = {chi}\n  bad finite places: [{}]; fibre at ∞: {infinity_type} (ord_U Δ = {infinity_order})\n  sections: {} (twelve forced, linear ±), origin O = a1+T\n  heights ⟨P,P⟩: [{}]\n  height form: rank {rank}, inertia (n+, n0, n−) = {:?}, determinant on the pivoted set {:?} = {}\n  ℤ-span of all sections: index {} over the pivots, regulator {}\n  relations in MW ⊗ ℚ ({}):\n    {}\n  elapsed {elapsed:.1} s\n",
            model.a.degree().unwrap_or(0),
            model.b.degree().unwrap_or(0),
            scalings.len(),
            bad.join("; "),
            n,
            heights
                .iter()
                .map(|h| h.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            inertia,
            pivots
                .iter()
                .map(|i| points[*i].label.clone())
                .collect::<Vec<_>>(),
            determinant,
            index,
            span_regulator,
            relations.len(),
            relations.join("\n    ")
        );
        fs::write(format!("{OUTPUT}/receipt-{label}.txt"), &family_report)
            .map_err(|e| e.to_string())?;
        report.push_str(&family_report);
        let mut table =
            format!("leaderboard #{label}: height form (χ = {chi}) on sections other than O\n");
        for (i, p) in points.iter().enumerate() {
            table.push_str(&format!(
                "  [{i}] {}  deg x = {}/{}\n",
                p.label,
                p.x.num.degree().unwrap_or(0),
                p.x.den.degree().unwrap_or(0)
            ));
        }
        for row in &gram {
            table.push_str(&format!(
                "  {}\n",
                row.iter()
                    .map(|v| format!("{:>7}", v.to_string()))
                    .collect::<Vec<_>>()
                    .join(" ")
            ));
        }
        fs::write(format!("{OUTPUT}/{label}.txt"), table).map_err(|e| e.to_string())?;
        eprintln!("#{label} done in {elapsed:.1} s");
    }
    print!("{report}");
    // the combined receipt is the concatenation of every family receipt that stands
    let mut combined = String::new();
    for (label, _) in published {
        if let Ok(part) = fs::read_to_string(format!("{OUTPUT}/receipt-{label}.txt")) {
            combined.push_str(&part);
        }
    }
    fs::write(format!("{OUTPUT}/receipt.txt"), &combined).map_err(|e| e.to_string())?;
    println!("artifact={OUTPUT}/receipt.txt");
    Ok(())
}

/// Exact square root of a perfect-square polynomial by matching coefficients from the top.
fn polynomial_square_root(f: &Poly) -> Option<Poly> {
    let degree = f.degree()?;
    if degree % 2 == 1 {
        return None;
    }
    let half = degree / 2;
    let lead = f.leading()?.clone();
    if lead.is_negative() {
        return None;
    }
    let (ln, ld) = (lead.numer().sqrt(), lead.denom().sqrt());
    if &ln * &ln != *lead.numer() || &ld * &ld != *lead.denom() {
        return None;
    }
    let root_lead = Rat::new(ln, ld);
    let mut h = vec![Rat::zero(); half + 1];
    h[half] = root_lead.clone();
    let two_lead = &root_lead * int(2);
    for k in (0..half).rev() {
        // [x^{half+k}] h² = 2 h_half h_k + Σ_{i+j=half+k, k<i,j<half} h_i h_j
        let mut cross = Rat::zero();
        for i in (k + 1)..half {
            let j = half + k - i;
            if j > k && j < half {
                cross += &h[i] * &h[j];
            }
        }
        h[k] = (f.coefficient(half + k) - cross) / &two_lead;
    }
    let candidate = Poly::new(h);
    if candidate.times(&candidate) == *f {
        Some(candidate)
    } else {
        None
    }
}
