//! Exact exterior arithmetic for `f(x)=a*x+b`. A zero residue and
//! `1<d<=z<f^n(z)` certify a composite term without constructing that integer.
//! The modulus can be composite. Search costs at most d modular steps (a value
//! bound); verification uses O(log n) modular affine compositions. This is an
//! arithmetic application/reference, not a native HNN formation law.

use crate::receiver_history_compression::exact_biguint_gcd;
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use thiserror::Error;

/// Untrusted, independently checkable source/divisor/clock. This need not name
/// the *first* composite term of the orbit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AffineOrbitCertificate {
    pub a: BigUint,
    pub b: BigUint,
    pub z: BigUint,
    pub d: BigUint,
    pub n: BigUint,
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum AffineOrbitError {
    #[error("requires a>1, z>1 and, for search, 1<d<=z coprime to a")]
    InvalidParameters,
    #[error("backward numerator search requires b>0")]
    StationaryBackwardNumerators,
    #[error("no coprime divisor survived before backward index {index} reached {numerator}")]
    NoCoprimeModulus { index: BigUint, numerator: BigInt },
    #[error("the source, divisor or return clock does not certify a composite term")]
    InvalidCertificate,
}

fn coprime(a: &BigUint, d: &BigUint) -> bool {
    exact_biguint_gcd(a.clone(), d.clone()).is_one()
}

fn compose(l: &(BigUint, BigUint), r: &(BigUint, BigUint), d: &BigUint) -> (BigUint, BigUint) {
    // l after r; the offset is part of the action.
    ((&l.0 * &r.0) % d, (&l.0 * &r.1 + &l.1) % d)
}

fn affine_pow(a: &BigUint, b: &BigUint, n: &BigUint, d: &BigUint) -> (BigUint, BigUint) {
    let mut result = (BigUint::one(), BigUint::zero());
    let mut base = (a % d, b % d);
    let mut exponent = n.clone();
    while !exponent.is_zero() {
        if (&exponent & BigUint::one()).is_one() {
            result = compose(&base, &result, d);
        }
        exponent >>= 1usize;
        if !exponent.is_zero() {
            base = compose(&base, &base, d);
        }
    }
    result
}

impl AffineOrbitCertificate {
    /// Checks the modular equation and strict-growth hypotheses. Coprimality
    /// and n<=d certify the bounded search domain; the proper-divisor argument
    /// itself needs neither extra condition. b=0 remains lawful here.
    pub fn verify(&self) -> Result<(), AffineOrbitError> {
        if self.a <= BigUint::one()
            || self.z <= BigUint::one()
            || self.d <= BigUint::one()
            || self.z < self.d
            || self.n.is_zero()
            || self.n > self.d
            || !coprime(&self.a, &self.d)
        {
            return Err(AffineOrbitError::InvalidCertificate);
        }
        let (power, offset) = affine_pow(&self.a, &self.b, &self.n, &self.d);
        if ((power * (&self.z % &self.d) + offset) % &self.d).is_zero() {
            Ok(())
        } else {
            Err(AffineOrbitError::InvalidCertificate)
        }
    }
}

/// One continuing search, transferred into its next result. The residue is
/// exactly f^tested(z) modulo d; caller allowance measures actual work.
#[derive(Debug, PartialEq, Eq)]
pub struct AffineOrbitContinuation {
    a: BigUint,
    b: BigUint,
    z: BigUint,
    d: BigUint,
    current_residue: BigUint,
    tested: BigUint,
}

impl AffineOrbitContinuation {
    pub fn new(a: BigUint, b: BigUint, z: BigUint, d: BigUint) -> Result<Self, AffineOrbitError> {
        if a <= BigUint::one()
            || z <= BigUint::one()
            || d <= BigUint::one()
            || z < d
            || !coprime(&a, &d)
        {
            return Err(AffineOrbitError::InvalidParameters);
        }
        let current_residue = &z % &d;
        Ok(Self {
            a,
            b,
            z,
            d,
            current_residue,
            tested: BigUint::zero(),
        })
    }
    pub fn steps(&self) -> &BigUint {
        &self.tested
    }
    pub fn residue(&self) -> &BigUint {
        &self.current_residue
    }
    pub fn modulus(&self) -> &BigUint {
        &self.d
    }

    /// Exhaustion means this modular cycle misses zero; it is not a primality
    /// claim about the integer orbit. A terminal state cannot advance further.
    pub fn search(mut self, allowance: usize) -> AffineOrbitSearch {
        if self.tested == self.d {
            return AffineOrbitSearch::Exhausted(self);
        }
        for _ in 0..allowance {
            self.current_residue = (&self.a * &self.current_residue + &self.b) % &self.d;
            self.tested += BigUint::one();
            if self.current_residue.is_zero() {
                return AffineOrbitSearch::Certificate(AffineOrbitCertificate {
                    a: self.a,
                    b: self.b,
                    z: self.z,
                    d: self.d,
                    n: self.tested,
                });
            }
            if self.tested == self.d {
                return AffineOrbitSearch::Exhausted(self);
            }
        }
        AffineOrbitSearch::Continuation(self)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum AffineOrbitSearch {
    Certificate(AffineOrbitCertificate),
    Continuation(AffineOrbitContinuation),
    Exhausted(AffineOrbitContinuation),
}

/// s_i=z-b(1+a+...+a^(i-1)), with its source and gcd-stripped divisor retained.
/// The equation z=f^i(0) modulo d places the root on zero's finite cycle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoprimeModulusDerivation {
    pub a: BigUint,
    pub b: BigUint,
    pub z: BigUint,
    pub index: BigUint,
    pub numerator: BigUint,
    pub modulus: BigUint,
    /// Nontrivial gcd divisions across all inspected numerators.
    pub divisions: BigUint,
}

/// Successive positive backward numerators, with gcd stripping and no prime
/// factorization. Later numerators matter: (2,1,9) gives 8 then 6; the latter
/// leaves modulus 3. Finite descent stops explicitly at signed numerator <=1.
pub fn derive_coprime_modulus(
    a: &BigUint,
    b: &BigUint,
    z: &BigUint,
) -> Result<CoprimeModulusDerivation, AffineOrbitError> {
    if *a <= BigUint::one() || *z <= BigUint::one() {
        return Err(AffineOrbitError::InvalidParameters);
    }
    if b.is_zero() {
        return Err(AffineOrbitError::StationaryBackwardNumerators);
    }
    let mut offset = b.clone();
    let mut step = a * b;
    let mut index = BigUint::one();
    let mut divisions = BigUint::zero();
    loop {
        if &offset >= z || z - &offset <= BigUint::one() {
            return Err(AffineOrbitError::NoCoprimeModulus {
                index,
                numerator: BigInt::from(z.clone()) - BigInt::from(offset),
            });
        }
        let numerator = z - &offset;
        let mut modulus = numerator.clone();
        while modulus > BigUint::one() {
            let common = exact_biguint_gcd(modulus.clone(), a.clone());
            if common.is_one() {
                return Ok(CoprimeModulusDerivation {
                    a: a.clone(),
                    b: b.clone(),
                    z: z.clone(),
                    index,
                    numerator,
                    modulus,
                    divisions,
                });
            }
            modulus /= common;
            divisions += BigUint::one();
        }
        offset += &step;
        step *= a;
        index += BigUint::one();
    }
}

pub fn search_affine_orbit(
    a: BigUint,
    b: BigUint,
    z: BigUint,
    d: BigUint,
    allowance: usize,
) -> Result<AffineOrbitSearch, AffineOrbitError> {
    Ok(AffineOrbitContinuation::new(a, b, z, d)?.search(allowance))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn u(v: u64) -> BigUint {
        BigUint::from(v)
    }
    fn certificate(result: AffineOrbitSearch) -> AffineOrbitCertificate {
        let AffineOrbitSearch::Certificate(c) = result else {
            panic!("expected divisor return")
        };
        c.verify().unwrap();
        c
    }

    #[test]
    fn coprime_root_is_itself_a_modulus() {
        let c = certificate(search_affine_orbit(u(2), u(1), u(5), u(5), 5).unwrap());
        assert_eq!(c.n, u(4)); // f^4(5)=95.
        let c = certificate(search_affine_orbit(u(2), u(0), u(5), u(5), 5).unwrap());
        assert_eq!(c.n, u(1)); // b=0 is allowed by strict growth.
    }
    #[test]
    fn composite_modulus_and_later_backward_escape() {
        let d = derive_coprime_modulus(&u(6), &u(1), &u(316)).unwrap();
        assert_eq!(
            (d.index, d.numerator, d.modulus.clone(), d.divisions),
            (u(1), u(315), u(35), u(2))
        );
        let c = certificate(search_affine_orbit(u(6), u(1), u(316), d.modulus, 35).unwrap());
        assert_eq!(c.n, u(9));
        let d = derive_coprime_modulus(&u(2), &u(1), &u(9)).unwrap();
        assert_eq!(
            (d.index, d.numerator, d.modulus.clone()),
            (u(2), u(6), u(3))
        );
        assert_eq!(
            certificate(search_affine_orbit(d.a, d.b, d.z, d.modulus, 3).unwrap()).n,
            u(2)
        );
    }
    #[test]
    fn pause_resume_keeps_the_clock_and_large_source() {
        let z = u(7) * (BigUint::one() << 200usize) + u(1);
        let s = AffineOrbitContinuation::new(u(2), u(1), z.clone(), u(7)).unwrap();
        let AffineOrbitSearch::Continuation(s) = s.search(0) else {
            panic!()
        };
        assert_eq!(s.steps(), &u(0));
        assert_eq!(s.residue(), &u(1));
        let AffineOrbitSearch::Continuation(s) = s.search(1) else {
            panic!()
        };
        assert_eq!(s.steps(), &u(1));
        assert_eq!(s.residue(), &u(3));
        let c = certificate(s.search(1));
        assert_eq!(c.n, u(2));
        assert_eq!(c.z, z);
        println!(
            "certificate: a={}, b={}, z={}, divisor={}, clock={}",
            c.a, c.b, c.z, c.d, c.n
        );
    }
    #[test]
    fn a_cycle_missing_zero_has_terminal_exhaustion() {
        // The fixed residue 6 mod 7 never enters 0->1->3->0.
        let s = AffineOrbitContinuation::new(u(2), u(1), u(13), u(7)).unwrap();
        let AffineOrbitSearch::Exhausted(s) = s.search(100) else {
            panic!()
        };
        assert_eq!(s.steps(), &u(7));
        assert_eq!(s.residue(), &u(6));
        let AffineOrbitSearch::Exhausted(s) = s.search(100) else {
            panic!()
        };
        assert_eq!(s.steps(), &u(7));
    }
    #[test]
    fn a_large_return_clock_is_verified_without_traversing_it() {
        // Here a=1 mod d and b=1, so r_n=n mod d from root z=d.
        // This clock is derived from the translation law, not found by search.
        let d = (BigUint::one() << 200usize) + u(1);
        let c = AffineOrbitCertificate {
            a: &d + u(1),
            b: u(1),
            z: d.clone(),
            d: d.clone(),
            n: d.clone(),
        };
        let start = std::time::Instant::now();
        c.verify().unwrap();
        println!(
            "translation certificate: exponent_bits={}, modulus_bits={}, verification_ns={}",
            c.n.bits(),
            c.d.bits(),
            start.elapsed().as_nanos()
        );
        assert_eq!(
            AffineOrbitCertificate { n: d - u(1), ..c }.verify(),
            Err(AffineOrbitError::InvalidCertificate)
        );
    }
    #[test]
    fn wrong_source_clock_and_divisor_are_rejected() {
        let c = certificate(search_affine_orbit(u(2), u(1), u(8), u(7), 7).unwrap());
        for bad in [
            AffineOrbitCertificate {
                n: u(0),
                ..c.clone()
            },
            AffineOrbitCertificate {
                n: u(1),
                ..c.clone()
            },
            AffineOrbitCertificate {
                n: u(8),
                ..c.clone()
            },
            AffineOrbitCertificate {
                z: u(7),
                ..c.clone()
            },
            AffineOrbitCertificate {
                d: u(1),
                ..c.clone()
            },
            AffineOrbitCertificate {
                d: u(9),
                ..c.clone()
            },
            AffineOrbitCertificate { d: u(6), ..c },
        ] {
            assert_eq!(bad.verify(), Err(AffineOrbitError::InvalidCertificate));
        }
        assert_eq!(
            derive_coprime_modulus(&u(2), &u(3), &u(2)),
            Err(AffineOrbitError::NoCoprimeModulus {
                index: u(1),
                numerator: BigInt::from(-1)
            })
        );
    }
    #[test]
    fn binary_certificates_match_direct_integer_orbits() {
        for a in 2..8u64 {
            for b in 0..5u64 {
                for z in 2..25u64 {
                    if !coprime(&u(a), &u(z)) {
                        continue;
                    }
                    let c = certificate(
                        search_affine_orbit(u(a), u(b), u(z), u(z), z as usize).unwrap(),
                    );
                    let mut exact = u(z);
                    let mut n = u(0);
                    while n < c.n {
                        exact = u(a) * exact + u(b);
                        n += u(1);
                    }
                    assert!(exact > c.z);
                    assert_eq!(&exact % &c.d, u(0));
                    assert!(exact / &c.d > u(1));
                }
            }
        }
        for a in 2..8u64 {
            for b in 1..5u64 {
                for z in 2..60u64 {
                    if let Ok(d) = derive_coprime_modulus(&u(a), &u(b), &u(z)) {
                        let (_, offset) = affine_pow(&d.a, &d.b, &d.index, &d.modulus);
                        assert_eq!(&d.z % &d.modulus, offset);
                        certificate(
                            search_affine_orbit(d.a, d.b, d.z, d.modulus, z as usize).unwrap(),
                        );
                    }
                }
            }
        }
    }
}
