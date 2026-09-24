use super::curve::{inverse_mod, residue_signs};
use super::foundation::{RealizerSextuple, elementary_symmetric, poly_mul};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
// ---------------------------------------------------------------------------------------------
// generating families off the variety rather than off a parametrisation
// ---------------------------------------------------------------------------------------------

/// Complete four values to a realizer sextuple.
///
/// With `a_5 + a_6 = -(a_1 + … + a_4)` forced by `e_1 = 0`, the remaining freedom is
/// `π = a_5 a_6`, and both `e_5` and `e_2 e_3` are polynomial in `π` of degree at most one and two
/// respectively — so the variety's second identity is **one quadratic in `π`**. A rational
/// sextuple therefore needs two squares: the quadratic's discriminant, and `σ² - 4π` to split the
/// pair. That is the whole generator, and it reaches the full three-dimensional variety rather
/// than the two-dimensional `(u, v)` slice the literature parametrises.
pub fn complete_to_sextuple(head: [BigRational; 4]) -> Vec<RealizerSextuple> {
    let sigma = -(head[0].clone() + &head[1] + &head[2] + &head[3]);
    let residual = |pi: &BigRational| -> BigRational {
        let head_e = elementary_symmetric(&head);
        // e_j(all six) = Σ_i head_e[i] · f_{j-i} with f_0 = 1, f_1 = σ, f_2 = π
        let tail = [BigRational::one(), sigma.clone(), pi.clone()];
        let mut total = vec![BigRational::zero(); 7];
        for (j, slot) in total.iter_mut().enumerate() {
            for i in 0..=j.min(4) {
                if j - i <= 2 {
                    *slot += &head_e[i] * &tail[j - i];
                }
            }
        }
        &total[5] * BigRational::from_integer(BigInt::from(2)) - &total[2] * &total[3]
    };
    let zero = residual(&BigRational::zero());
    let one = residual(&BigRational::one());
    let two = residual(&BigRational::from_integer(BigInt::from(2)));
    let quadratic = (&two - &one - &one + &zero) / BigRational::from_integer(BigInt::from(2));
    let linear = &one - &zero - &quadratic;
    let constant = zero;

    let rational_square_root = |value: &BigRational| -> Option<BigRational> {
        if value.numer().is_negative() {
            return None;
        }
        let n = value.numer().sqrt();
        let d = value.denom().sqrt();
        if &n * &n == *value.numer() && &d * &d == *value.denom() {
            Some(BigRational::new(n, d))
        } else {
            None
        }
    };

    let mut roots = Vec::new();
    if quadratic.is_zero() {
        if !linear.is_zero() {
            roots.push(-constant / linear);
        }
    } else {
        let discriminant =
            &linear * &linear - BigRational::from_integer(BigInt::from(4)) * &quadratic * &constant;
        if let Some(root) = rational_square_root(&discriminant) {
            let two = BigRational::from_integer(BigInt::from(2));
            roots.push((-&linear + &root) / (&two * &quadratic));
            roots.push((-&linear - &root) / (&two * &quadratic));
        }
    }

    let mut found = Vec::new();
    for pi in roots {
        let split = &sigma * &sigma - BigRational::from_integer(BigInt::from(4)) * &pi;
        let Some(root) = rational_square_root(&split) else {
            continue;
        };
        let two = BigRational::from_integer(BigInt::from(2));
        let fifth = (&sigma + &root) / &two;
        let sixth = (&sigma - &root) / &two;
        let candidate = [
            head[0].clone(),
            head[1].clone(),
            head[2].clone(),
            head[3].clone(),
            fifth,
            sixth,
        ];
        if let Ok(sextuple) = RealizerSextuple::found(candidate) {
            found.push(sextuple);
        }
    }
    found
}

/// Whether a sextuple is fixed by negation. Those satisfy the variety's identities trivially
/// (every odd power sum vanishes) and are refused as families: the remainder is then even in `x`,
/// which forces the involution `ι(P) = c - P` and halves the realizer rank.
pub fn is_negation_symmetric(sextuple: &RealizerSextuple) -> bool {
    let values = sextuple.values();
    values
        .iter()
        .all(|v| values.iter().any(|w| w == &-v.clone()))
}

// ---------------------------------------------------------------------------------------------
// the specialization wheel
// ---------------------------------------------------------------------------------------------

impl RealizerSextuple {
    /// The remainder's five coefficients as polynomials in the pairing parameter.
    ///
    /// `p(x) = ∏((x - a_i)^2 - T^2)` has joint degree twelve, so `r_k(T)` has degree at most
    /// `12 - k` and thirteen samples determine it. Recovering the parameter dependence once is
    /// what makes the wheel possible: after this, a specialization is an evaluation rather than a
    /// construction.
    pub fn remainder_polynomials(&self) -> [Vec<BigRational>; 5] {
        let samples: Vec<BigRational> = (0..13)
            .map(|t| BigRational::from_integer(BigInt::from(t as i64)))
            .collect();
        let values: Vec<[BigRational; 5]> = samples
            .iter()
            .map(|t| self.remainder_at(t).coefficient)
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
                let weight = &values[i][k] / &denominator;
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
}

/// One prime receiver's partition of specialization space.
///
/// `a_p` of the specialized quartic depends only on `T mod p`, so each prime receiver cuts
/// specialization space into exactly `p` classes and can say nothing finer. The cell it carries is
/// the **exact additive chart of the crossing ratio** `p + 1 : #E(F_p)` at a declared integer
/// aperture:
///
/// ```text
///     cell(r) = ⌊ M · (#E(F_p) − p − 1) / #E(F_p) ⌋        (Euclidean division, exact)
/// ```
///
/// Larger means more supported. There is no logarithm and no float: `log(p/#E)` is one receiver's
/// reading of the ratio, and taking it here would let a float order which specializations get
/// built — a scalar governor choosing the population, which is exactly what is forbidden. The
/// ratio's own first-order chart is an integer division and orders the same way.
///
/// A singular class abstains with `0` rather than scoring.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReceiverPartition {
    pub prime: u32,
    pub cell: Vec<i64>,
}

/// The aperture the cells are scaled by. Declared, not tuned: it sets the resolution at which two
/// classes are distinguishable and it is reported with every wheel.
pub const WHEEL_APERTURE: i64 = 1 << 20;

/// Turn one trace into its cell, exactly.
pub fn cell_of_trace(prime: u32, trace: i64) -> i64 {
    let order = prime as i64 + 1 - trace;
    if order <= 0 {
        return 0;
    }
    // #E − p − 1 = −a_p, so a class with many points scores high.
    (WHEEL_APERTURE * (-trace)).div_euclid(order)
}

/// The composite partition of several receivers — the wheel with its motion.
///
/// Distinct prime receivers see disjoint information about `T`, and the Chinese Remainder Theorem
/// is the law by which their partitions **compose**: a class of the composite is one class from
/// each receiver, held simultaneously. Rolling is that composition performed one receiver at a
/// time, and it is why the wheel is not a lookup table — the object it builds is the *interaction*
/// of the partitions, and an admitted class is a coincidence across all of them at once.
///
/// The score carried on a composite class is the sum of its receivers' cells, which is exact
/// because the cells are integers. Summation is a coarse reading of the coincidence and it never
/// decides anything: it orders attention, and the exact rank certificate decides.
#[derive(Debug, Clone)]
pub struct RolledWheel {
    pub modulus: u64,
    pub score: Vec<i64>,
    pub receivers: Vec<u32>,
}

impl RolledWheel {
    /// Compose partitions by CRT, smallest first, stopping before the composite exceeds `ceiling`
    /// classes. The receivers left out are reported so the aperture is never implicit.
    pub fn roll(partitions: &[ReceiverPartition], ceiling: u64) -> (Self, Vec<u32>) {
        let mut ordered: Vec<&ReceiverPartition> = partitions.iter().collect();
        ordered.sort_by_key(|p| p.prime);
        let mut modulus = 1u64;
        let mut score = vec![0i64];
        let mut receivers = Vec::new();
        let mut deferred = Vec::new();
        for partition in ordered {
            let prime = partition.prime as u64;
            match modulus.checked_mul(prime) {
                Some(next) if next <= ceiling => {
                    let mut extended = vec![0i64; next as usize];
                    for (index, slot) in extended.iter_mut().enumerate() {
                        let index = index as u64;
                        *slot = score[(index % modulus) as usize]
                            + partition.cell[(index % prime) as usize];
                    }
                    modulus = next;
                    score = extended;
                    receivers.push(partition.prime);
                }
                _ => deferred.push(partition.prime),
            }
        }
        (
            Self {
                modulus,
                score,
                receivers,
            },
            deferred,
        )
    }

    /// The best `keep` composite classes, by exact integer order. These are the only classes any
    /// later enumeration visits: the wheel turns past the rest without ever building a curve.
    pub fn admitted_classes(&self, keep: usize) -> Vec<u64> {
        let mut indexed: Vec<(i64, u64)> = self
            .score
            .iter()
            .enumerate()
            .map(|(index, value)| (*value, index as u64))
            .collect();
        indexed.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
        indexed.into_iter().take(keep).map(|(_, i)| i).collect()
    }
}

/// The receivers a rolled wheel could not absorb, kept as a residual reading over their own
/// partitions. Their contribution is added exactly, after the roll has already pruned.
#[derive(Debug, Clone)]
pub struct ResidualReceivers {
    pub partitions: Vec<ReceiverPartition>,
}

impl ResidualReceivers {
    pub fn score(&self, parameter: i64) -> i64 {
        self.partitions
            .iter()
            .map(|p| p.cell[parameter.rem_euclid(p.prime as i64) as usize])
            .sum()
    }
}

impl RealizerSextuple {
    /// Every receiver's partition, computed on the host. Exact throughout.
    pub fn receiver_partitions(&self, primes: &[u64]) -> Vec<ReceiverPartition> {
        let polynomials = self.remainder_polynomials();
        let mut partitions = Vec::new();
        for &p in primes {
            if p < 5 {
                continue;
            }
            let modulus = p as i128;
            let reduced: Vec<Vec<i128>> = polynomials
                .iter()
                .map(|poly| {
                    poly.iter()
                        .map(|c| reduce_rational(c, p, modulus))
                        .collect()
                })
                .collect();
            let signs = residue_signs(modulus);
            let mut cell = Vec::with_capacity(p as usize);
            for residue in 0..modulus {
                let mut coefficient = [0i128; 5];
                for (k, slot) in coefficient.iter_mut().enumerate() {
                    let mut value = 0i128;
                    for c in reduced[k].iter().rev() {
                        value = (value * residue + c).rem_euclid(modulus);
                    }
                    *slot = value;
                }
                if coefficient == [0i128; 5] {
                    cell.push(0);
                    continue;
                }
                let mut total = 0i64;
                for x in 0..modulus {
                    let mut value = coefficient[4];
                    for k in (0..4).rev() {
                        value = (value * x + coefficient[k]).rem_euclid(modulus);
                    }
                    total += signs[value as usize] as i64;
                }
                let trace = -(total + signs[coefficient[4] as usize] as i64);
                cell.push(cell_of_trace(p as u32, trace));
            }
            partitions.push(ReceiverPartition {
                prime: p as u32,
                cell,
            });
        }
        partitions
    }
}

fn reduce_rational(value: &BigRational, prime: u64, modulus: i128) -> i128 {
    let m = BigInt::from(prime);
    let n: i128 = (value.numer() % &m).try_into().unwrap_or(0);
    let d: i128 = (value.denom() % &m).try_into().unwrap_or(0);
    if d == 0 {
        0
    } else {
        (n.rem_euclid(modulus) * inverse_mod(d, modulus)).rem_euclid(modulus)
    }
}

/// One receiver's inputs to a resident wheel build, prepared without touching the card.
pub struct WheelPreparation {
    pub prime: u32,
    pub polynomials: Vec<u32>,
    pub degree: u32,
    pub signs: Vec<i8>,
}

impl RealizerSextuple {
    /// Reduce the family's coefficient polynomials at every receiver and build its residue-sign
    /// table. Everything the card needs and nothing it does not; the direction of the dependency
    /// stays host → card.
    pub fn wheel_preparation(&self, primes: &[u64]) -> Vec<WheelPreparation> {
        let polynomials = self.remainder_polynomials();
        let degree = polynomials.iter().map(|p| p.len()).max().unwrap_or(1) - 1;
        let mut prepared = Vec::new();
        for &p in primes {
            if p < 5 {
                continue;
            }
            let modulus = p as i128;
            let mut run = Vec::with_capacity(5 * (degree + 1));
            for poly in polynomials.iter() {
                for index in 0..=degree {
                    let value = poly.get(index).map_or(0i128, |c| {
                        let m = BigInt::from(p);
                        let n: i128 = (c.numer() % &m).try_into().unwrap_or(0);
                        let d: i128 = (c.denom() % &m).try_into().unwrap_or(0);
                        if d == 0 {
                            0
                        } else {
                            (n.rem_euclid(modulus) * inverse_mod(d, modulus)).rem_euclid(modulus)
                        }
                    });
                    run.push(value as u32);
                }
            }
            prepared.push(WheelPreparation {
                prime: p as u32,
                polynomials: run,
                degree: degree as u32,
                signs: residue_signs(modulus),
            });
        }
        prepared
    }
}

/// Assemble receiver partitions from the card's returned traces. `INT32_MIN` marks a singular
/// class, which abstains rather than scoring.
pub fn partitions_from_traces(
    prepared: &[WheelPreparation],
    traces: &[i32],
) -> Vec<ReceiverPartition> {
    let mut partitions = Vec::with_capacity(prepared.len());
    let mut cursor = 0usize;
    for receiver in prepared {
        let width = receiver.prime as usize;
        let mut cell = Vec::with_capacity(width);
        for index in 0..width {
            let trace = traces[cursor + index];
            cell.push(if trace == i32::MIN {
                0
            } else {
                cell_of_trace(receiver.prime, trace as i64)
            });
        }
        cursor += width;
        partitions.push(ReceiverPartition {
            prime: receiver.prime,
            cell,
        });
    }
    partitions
}

/// Convert a leaderboard's published `log(naive height)` into an exact integer ceiling.
///
/// **This is the only place in this owner where a float is admitted, and it is a codec, not a
/// decision.** The record frontier exists exterior to this tree in one form only — a decimal
/// logarithm printed in a published column — so reading it costs one conversion. The conversion
/// rounds **up**, so the bound is conservative: it can admit a curve that turns out not to be a
/// record, and it can never reject one that is. Everything downstream compares
/// `max(|c4|^3, c6^2)` against this integer, exactly.
pub fn height_ceiling_from_published_log(published: f64) -> BigInt {
    if !published.is_finite() || published <= 0.0 {
        return BigInt::zero();
    }
    let exponent = (published / std::f64::consts::LN_2).floor();
    let fractional = published - exponent * std::f64::consts::LN_2;
    // mantissa in [1, 2), lifted to 53 bits and rounded away from zero
    let mantissa = (fractional.exp() * (1u64 << 53) as f64).ceil() as u128 + 1;
    let mantissa = BigInt::from(mantissa);
    let shift = exponent as i64 - 53;
    if shift >= 0 {
        mantissa << shift as usize
    } else {
        // never below one: a ceiling of zero would refuse everything
        let divisor = BigInt::from(1u8) << ((-shift) as usize);
        let value = mantissa / divisor;
        if value.is_zero() {
            BigInt::from(1)
        } else {
            value
        }
    }
}
