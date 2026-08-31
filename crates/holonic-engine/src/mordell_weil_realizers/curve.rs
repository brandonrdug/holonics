use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};
// ---------------------------------------------------------------------------------------------
// the curve, its group law, and the float-free independence certificate
// ---------------------------------------------------------------------------------------------

/// A Weierstrass curve over the rationals, exactly.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExactCurve {
    pub a: [BigRational; 5],
    pub b2: BigRational,
    pub b4: BigRational,
    pub b6: BigRational,
    pub discriminant: BigRational,
}

impl ExactCurve {
    pub fn new(
        a1: BigRational,
        a2: BigRational,
        a3: BigRational,
        a4: BigRational,
        a6: BigRational,
    ) -> Self {
        let four = BigRational::from_integer(BigInt::from(4));
        let b2 = &a1 * &a1 + &four * &a2;
        let b4 = BigRational::from_integer(BigInt::from(2)) * &a4 + &a1 * &a3;
        let b6 = &a3 * &a3 + &four * &a6;
        let b8 =
            &a1 * &a1 * &a6 + &four * &a2 * &a6 - &a1 * &a3 * &a4 + &a2 * &a3 * &a3 - &a4 * &a4;
        let discriminant = -(&b2 * &b2 * &b8)
            - BigRational::from_integer(BigInt::from(8)) * &b4 * &b4 * &b4
            - BigRational::from_integer(BigInt::from(27)) * &b6 * &b6
            + BigRational::from_integer(BigInt::from(9)) * &b2 * &b4 * &b6;
        Self {
            a: [a1, a2, a3, a4, a6],
            b2,
            b4,
            b6,
            discriminant,
        }
    }

    pub fn contains(&self, x: &BigRational, y: &BigRational) -> bool {
        let [a1, a2, a3, a4, a6] = &self.a;
        y * y + a1 * x * y + a3 * y == x * x * x + a2 * x * x + a4 * x + a6
    }
}

/// The classical map from a quartic with a rational point to a Weierstrass model. Translating the
/// point to `x = 0` makes the constant term a square `q^2`, and the rest is Connell's formulae.
#[derive(Debug, Clone)]
pub struct QuarticChart {
    pub curve: ExactCurve,
    shift: BigRational,
    c: BigRational,
    d: BigRational,
    q: BigRational,
}

impl QuarticChart {
    /// `coefficient` ascending, `base` a rational point of the quartic with nonzero ordinate.
    pub fn through(
        coefficient: &[BigRational; 5],
        base: &(BigRational, BigRational),
    ) -> Option<Self> {
        let (u0, v0) = base;
        if v0.is_zero() {
            return None;
        }
        // shift x -> x + u0
        let mut shifted = [
            BigRational::zero(),
            BigRational::zero(),
            BigRational::zero(),
            BigRational::zero(),
            BigRational::zero(),
        ];
        for (i, ci) in coefficient.iter().enumerate() {
            let mut binomial = BigInt::one();
            for j in 0..=i {
                let term =
                    ci * BigRational::from_integer(binomial.clone()) * u0.pow((i - j) as i32);
                shifted[j] += term;
                binomial = &binomial * BigInt::from((i - j) as u32) / BigInt::from((j + 1) as u32);
            }
        }
        let (e, d, c, b, a) = (
            shifted[0].clone(),
            shifted[1].clone(),
            shifted[2].clone(),
            shifted[3].clone(),
            shifted[4].clone(),
        );
        let q = v0.clone();
        if e != &q * &q {
            return None;
        }
        let two = BigRational::from_integer(BigInt::from(2));
        let four = BigRational::from_integer(BigInt::from(4));
        let a1 = &d / &q;
        let a2 = &c - &d * &d / (&four * &q * &q);
        let a3 = &two * &q * &b;
        let a4 = -&four * &q * &q * &a;
        let a6 = &a2 * &a4;
        Some(Self {
            curve: ExactCurve::new(a1, a2, a3, a4, a6),
            shift: u0.clone(),
            c,
            d,
            q,
        })
    }

    /// Carry a quartic realizer onto the Weierstrass model. `None` is the point at infinity.
    pub fn carry(&self, x: &BigRational, y: &BigRational) -> Option<(BigRational, BigRational)> {
        let u = x - &self.shift;
        if u.is_zero() {
            return None;
        }
        let two = BigRational::from_integer(BigInt::from(2));
        let four = BigRational::from_integer(BigInt::from(4));
        let xw = (&two * &self.q * (y + &self.q) + &self.d * &u) / (&u * &u);
        let yw = (&four * &self.q * &self.q * (y + &self.q)
            + &two * &self.q * (&self.d * &u + &self.c * &u * &u)
            - &self.d * &self.d * &u * &u / (&two * &self.q))
            / (&u * &u * &u);
        Some((xw, yw))
    }
}

// --- arithmetic in E(F_p) ---

pub(super) fn inverse_mod(a: i128, p: i128) -> i128 {
    let (mut t, mut newt) = (0i128, 1i128);
    let (mut r, mut newr) = (p, a.rem_euclid(p));
    while newr != 0 {
        let quotient = r / newr;
        (t, newt) = (newt, t - quotient * newt);
        (r, newr) = (newr, r - quotient * newr);
    }
    t.rem_euclid(p)
}

type ModularPoint = Option<(i128, i128)>;

fn add_mod(a: &[i128; 5], p: i128, left: ModularPoint, right: ModularPoint) -> ModularPoint {
    let (Some((x1, y1)), Some((x2, y2))) = (left, right) else {
        return left.or(right);
    };
    let [a1, a2, a3, a4, _] = *a;
    if x1 == x2 && (y1 + y2 + a1 * x2 + a3).rem_euclid(p) == 0 {
        return None;
    }
    let (numerator, denominator) = if left == right {
        (
            3 * x1 * x1 + 2 * a2 * x1 + a4 - a1 * y1,
            2 * y1 + a1 * x1 + a3,
        )
    } else {
        (y2 - y1, x2 - x1)
    };
    let denominator = denominator.rem_euclid(p);
    if denominator == 0 {
        return None;
    }
    let lambda = (numerator.rem_euclid(p) * inverse_mod(denominator, p)).rem_euclid(p);
    let nu = (y1 - lambda * x1).rem_euclid(p);
    let x3 = (lambda * lambda + a1 * lambda - a2 - x1 - x2).rem_euclid(p);
    let y3 = (-(lambda + a1) * x3 - nu - a3).rem_euclid(p);
    Some((x3, y3))
}

fn multiply_mod(a: &[i128; 5], p: i128, scalar: u64, point: ModularPoint) -> ModularPoint {
    let mut result: ModularPoint = None;
    let mut addend = point;
    let mut k = scalar;
    while k > 0 {
        if k & 1 == 1 {
            result = add_mod(a, p, result, addend);
        }
        addend = add_mod(a, p, addend, addend);
        k >>= 1;
    }
    result
}

pub(super) fn residue_signs(p: i128) -> Vec<i8> {
    let n = p as usize;
    let mut table = vec![-1i8; n];
    table[0] = 0;
    let mut x = 1i128;
    while x <= p / 2 {
        table[((x * x) % p) as usize] = 1;
        x += 1;
    }
    table
}

/// `#E(F_p)`, by summing residue signs of the completed square. Exact, `O(p)`, no float.
fn order_mod(a: &[i128; 5], p: i128, signs: &[i8]) -> u64 {
    let [a1, a2, a3, a4, a6] = *a;
    let b2 = (a1 * a1 + 4 * a2).rem_euclid(p);
    let b4 = (2 * a4 + a1 * a3).rem_euclid(p);
    let b6 = (a3 * a3 + 4 * a6).rem_euclid(p);
    let mut total = 0i64;
    for x in 0..p {
        let value = ((((4 * x + b2) * x + 2 * b4) * x + b6) % p).rem_euclid(p);
        total += signs[value as usize] as i64;
    }
    (p as i64 + 1 + total) as u64
}

/// What a rank certificate carries: the bound, the torsion prime it used, and every receiver.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndependenceCertificate {
    pub rank_lower_bound: usize,
    pub torsion_prime: u64,
    pub receivers: Vec<u64>,
    /// `true` when two receivers returned coprime orders, so `E(ℚ)` is torsion free and the
    /// relation lattice is genuinely `ℓ`-saturated. Without it the bound is conditional on that.
    pub torsion_free: bool,
}

/// Independence at declared prime receivers, with no height pairing and no float.
///
/// A relation `Σ e_i P_i = O` reduces at every good prime, so the relation lattice `Λ` lies inside
/// every kernel. Pushing each reduction into `E(F_p)[ℓ]` by multiplying by `#E(F_p)/ℓ` turns each
/// receiver into at most two linear conditions over `F_ℓ`. When those conditions force `e ≡ 0`,
/// `Λ ⊆ ℓℤ^n`; and `Λ` is `ℓ`-saturated whenever `E(ℚ)` has no `ℓ`-torsion, so `Λ ⊆ ℓΛ` and
/// therefore `Λ = 0`. The regulator is never formed, which is the point: it is transcendental and
/// every implementation of it is a float.
pub fn independence_certificate(
    curve: &ExactCurve,
    points: &[(BigRational, BigRational)],
    torsion_prime: u64,
    receivers: &[u64],
) -> IndependenceCertificate {
    let n = points.len();
    let ell = torsion_prime as i128;
    let mut rows: Vec<Vec<i128>> = Vec::new();
    let mut used = Vec::new();
    let mut orders: Vec<u64> = Vec::new();
    let mut rank = 0usize;
    for &p in receivers {
        if p < 5 || n == 0 {
            continue;
        }
        let modulus = BigInt::from(p);
        let reduce = |value: &BigRational| -> Option<i128> {
            if (value.denom() % &modulus).is_zero() {
                return None;
            }
            let numerator: i128 = (value.numer() % &modulus).try_into().ok()?;
            let denominator: i128 = (value.denom() % &modulus).try_into().ok()?;
            Some(
                (numerator.rem_euclid(p as i128) * inverse_mod(denominator, p as i128))
                    .rem_euclid(p as i128),
            )
        };
        if reduce(&curve.discriminant).map(|v| v == 0).unwrap_or(true) {
            continue;
        }
        let mut a = [0i128; 5];
        let mut usable = true;
        for (slot, value) in a.iter_mut().zip(curve.a.iter()) {
            match reduce(value) {
                Some(v) => *slot = v,
                None => usable = false,
            }
        }
        if !usable {
            continue;
        }
        let signs = residue_signs(p as i128);
        let order = order_mod(&a, p as i128, &signs);
        orders.push(order);
        if order % torsion_prime != 0 {
            continue;
        }
        let cofactor = order / torsion_prime;
        let mut reduced: Vec<ModularPoint> = Vec::with_capacity(n);
        let mut all_reduced = true;
        for (x, y) in points.iter() {
            match (reduce(x), reduce(y)) {
                (Some(xp), Some(yp)) => {
                    reduced.push(multiply_mod(&a, p as i128, cofactor, Some((xp, yp))));
                }
                _ => {
                    all_reduced = false;
                    break;
                }
            }
        }
        if !all_reduced {
            continue;
        }
        // Coordinates of each image against a basis of the `ℓ`-torsion it lands in.
        let mut basis: Vec<ModularPoint> = Vec::new();
        let mut coordinates: Vec<Vec<i128>> = Vec::new();
        for image in reduced.iter() {
            let mut found = None;
            'search: for combination in 0..ell.pow(basis.len() as u32) {
                let mut digits = Vec::with_capacity(basis.len());
                let mut rest = combination;
                for _ in basis.iter() {
                    digits.push(rest % ell);
                    rest /= ell;
                }
                let mut accumulated: ModularPoint = None;
                for (b, digit) in basis.iter().zip(digits.iter()) {
                    accumulated = add_mod(
                        &a,
                        p as i128,
                        accumulated,
                        multiply_mod(&a, p as i128, *digit as u64, *b),
                    );
                }
                if accumulated == *image {
                    found = Some(digits);
                    break 'search;
                }
            }
            match found {
                Some(digits) => coordinates.push(digits),
                None => {
                    basis.push(*image);
                    let mut digits = vec![0i128; basis.len()];
                    digits[basis.len() - 1] = 1;
                    coordinates.push(digits);
                }
            }
        }
        let width = basis.len();
        for j in 0..width {
            rows.push(
                coordinates
                    .iter()
                    .map(|c| c.get(j).copied().unwrap_or(0).rem_euclid(ell))
                    .collect(),
            );
        }
        used.push(p);
        rank = row_rank_mod(&rows, n, ell);
        if rank >= n {
            break;
        }
    }
    let torsion_free = orders
        .iter()
        .enumerate()
        .any(|(i, x)| orders.iter().skip(i + 1).any(|y| gcd_u64(*x, *y) == 1));
    IndependenceCertificate {
        rank_lower_bound: rank,
        torsion_prime,
        receivers: used,
        torsion_free,
    }
}

fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

fn row_rank_mod(rows: &[Vec<i128>], width: usize, modulus: i128) -> usize {
    let mut matrix: Vec<Vec<i128>> = rows.to_vec();
    let mut rank = 0usize;
    for column in 0..width {
        let Some(pivot) =
            (rank..matrix.len()).find(|&i| matrix[i][column].rem_euclid(modulus) != 0)
        else {
            continue;
        };
        matrix.swap(rank, pivot);
        let inverse = inverse_mod(matrix[rank][column], modulus);
        for value in matrix[rank].iter_mut() {
            *value = (*value * inverse).rem_euclid(modulus);
        }
        for i in 0..matrix.len() {
            if i != rank && matrix[i][column].rem_euclid(modulus) != 0 {
                let factor = matrix[i][column];
                for j in 0..width {
                    matrix[i][j] = (matrix[i][j] - factor * matrix[rank][j]).rem_euclid(modulus);
                }
            }
        }
        rank += 1;
        if rank == matrix.len() {
            break;
        }
    }
    rank
}
