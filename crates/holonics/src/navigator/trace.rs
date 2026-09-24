//! **Trace faces and the dynamical zeta of a navigator machine.**
//!
//! Carrying material to another phase conjugates it, `M ↦ S⁻ᵈMSᵈ`, so every class function of
//! the material is a face conserved along the winding: its determinant, its trace sequence
//! `tr(Mᵏ)` and its transfer determinant `det(1 − T·M)`
//! ([objects §3](../../../../docs/ELEMENTARY_OBJECTS.md#the-swing-the-navigators-elementary-motion)).
//! For independent sites the transfer determinants multiply and the trace sequences add; the
//! product `∏(1 − a_g T + q_g T²)` is the machine's dynamical zeta denominator.
//!
//! | Lean | Rust |
//! |---|---|
//! | `Millennium/LocalFactor.companion`, `theLocalFactorIsTheTransferDeterminant` | [`SiteFactor`] |
//! | `Millennium/TraceSequence.trace`, `LocalFactor.theCompanionPowersCarryTheSequence` | [`SiteFactor::trace_sequence`] |
//! | `Transport/GeneratorTraceFaces.machine_factor_of_companions`, `machine_trace_sequence` | [`Machine`] |
//! | `Transport/GeneratorTraceFaces.carried_material_conserves_{determinant,trace_sequence,transfer_determinant}` | tests |

use crate::ratio::Rat;
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

/// [definition] The dichotomy of the site's transfer: where its characteristic root sits.
/// Lean: `TraceSequence` — the circle of radius `√q` against the hyperbola.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SiteKind {
    /// `a² < 4q`: the root is off the real line and the sequence circulates.
    Rotation,
    /// `a² = 4q`: the boundary case, a repeated real root.
    Marginal,
    /// `a² > 4q`: two real roots and the sequence goes hyperbolic.
    Dilation,
}

/// [definition] One site of the machine, read through its two conserved faces: the trace `a` and
/// the determinant `q` of its transfer material. Lean: `LocalFactor.companion` and
/// `theCompanionHasTraceAndDeterminant`; both faces are conserved by phase carriage
/// (`GeneratorTraceFaces.carried_material_conserves_determinant`, `..._trace_sequence`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SiteFactor {
    trace: Rat,
    determinant: Rat,
}

impl SiteFactor {
    pub fn new(trace: Rat, determinant: Rat) -> Self {
        Self { trace, determinant }
    }

    pub fn trace(&self) -> &Rat {
        &self.trace
    }

    pub fn determinant(&self) -> &Rat {
        &self.determinant
    }

    /// The Frobenius companion `!![a, −q; 1, 0]`. Lean: `LocalFactor.companion`.
    pub fn companion(&self) -> [[Rat; 2]; 2] {
        [
            [self.trace.clone(), -self.determinant.clone()],
            [Rat::one(), Rat::zero()],
        ]
    }

    /// The trace sequence `t₀ = 2`, `t₁ = a`, `t_{n+2} = a·t_{n+1} − q·t_n`, through index
    /// `degree` inclusive. Lean: `TraceSequence.trace`, and
    /// `LocalFactor.theCompanionPowersCarryTheSequence` identifies it with `tr(Mⁿ)`.
    ///
    /// Cost: `degree` exact multiplications; the companion is never exponentiated.
    pub fn trace_sequence(&self, degree: usize) -> Vec<Rat> {
        let mut sequence = Vec::with_capacity(degree + 1);
        sequence.push(Rat::from_integer(BigInt::from(2)));
        for index in 1..=degree {
            let term = if index == 1 {
                self.trace.clone()
            } else {
                &self.trace * &sequence[index - 1] - &self.determinant * &sequence[index - 2]
            };
            sequence.push(term);
        }
        sequence
    }

    /// The coefficients of `det(1 − T·M) = 1 − aT + qT²`, lowest power first.
    /// Lean: `LocalFactor.theLocalFactorIsTheTransferDeterminant`.
    pub(crate) fn transfer_coefficients(&self) -> [Rat; 3] {
        [Rat::one(), -self.trace.clone(), self.determinant.clone()]
    }

    /// The site's dichotomy, decided exactly on `a²` against `4q`.
    pub fn kind(&self) -> SiteKind {
        let discriminant =
            &self.trace * &self.trace - Rat::from_integer(BigInt::from(4)) * &self.determinant;
        if discriminant.is_negative() {
            SiteKind::Rotation
        } else if discriminant.is_zero() {
            SiteKind::Marginal
        } else {
            SiteKind::Dilation
        }
    }
}

/// [definition] A machine of independent sites: the block-diagonal material of
/// `GeneratorTraceFaces`. Its transfer determinant is the product of the site factors and its
/// closed-word count is the sum of the site trace sequences.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Machine {
    sites: Vec<SiteFactor>,
}

impl Machine {
    pub fn new(sites: Vec<SiteFactor>) -> Self {
        Self { sites }
    }

    pub fn sites(&self) -> &[SiteFactor] {
        &self.sites
    }

    /// The exact coefficient vector of `∏_g (1 − a_g T + q_g T²)`, lowest power first, of length
    /// `2·sites + 1`. Lean: `GeneratorTraceFaces.machine_factor_of_companions`.
    ///
    /// Cost: one convolution per site, quadratic in the site count.
    pub fn transfer_determinant(&self) -> Vec<Rat> {
        let mut coefficients = vec![Rat::one()];
        for site in &self.sites {
            let factor = site.transfer_coefficients();
            let mut next = vec![Rat::zero(); coefficients.len() + 2];
            for (left, coefficient) in coefficients.iter().enumerate() {
                for (right, entry) in factor.iter().enumerate() {
                    next[left + right] += coefficient * entry;
                }
            }
            coefficients = next;
        }
        coefficients
    }

    /// The machine's closed-word count through index `degree`: the sum of the site trace
    /// sequences. Lean: `GeneratorTraceFaces.machine_trace_sequence`.
    pub fn trace_sequence(&self, degree: usize) -> Vec<Rat> {
        let mut total = vec![Rat::zero(); degree + 1];
        for site in &self.sites {
            for (index, term) in site.trace_sequence(degree).into_iter().enumerate() {
                total[index] += term;
            }
        }
        total
    }

    /// The common dilation `q` when every site shares it, and `None` otherwise — including for a
    /// machine with no sites, which declares no `q` at all.
    pub fn common_dilation(&self) -> Option<Rat> {
        let first = self.sites.first()?.determinant();
        if self.sites.iter().all(|site| site.determinant() == first) {
            Some(first.clone())
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::{integer, rat};

    type Mat2 = [[Rat; 2]; 2];

    fn mat2_identity() -> Mat2 {
        [[Rat::one(), Rat::zero()], [Rat::zero(), Rat::one()]]
    }

    fn mat2_multiply(left: &Mat2, right: &Mat2) -> Mat2 {
        let entry = |row: usize, column: usize| {
            &left[row][0] * &right[0][column] + &left[row][1] * &right[1][column]
        };
        [[entry(0, 0), entry(0, 1)], [entry(1, 0), entry(1, 1)]]
    }

    fn mat2_trace(matrix: &Mat2) -> Rat {
        &matrix[0][0] + &matrix[1][1]
    }

    fn mat2_determinant(matrix: &Mat2) -> Rat {
        &matrix[0][0] * &matrix[1][1] - &matrix[0][1] * &matrix[1][0]
    }

    fn mat2_inverse(matrix: &Mat2) -> Mat2 {
        let determinant = mat2_determinant(matrix);
        assert!(
            !determinant.is_zero(),
            "the test carrier must be invertible"
        );
        [
            [
                &matrix[1][1] / &determinant,
                -(&matrix[0][1] / &determinant),
            ],
            [
                -(&matrix[1][0] / &determinant),
                &matrix[0][0] / &determinant,
            ],
        ]
    }

    #[test]
    fn the_companion_powers_carry_the_trace_sequence() {
        for site in [
            SiteFactor::new(integer(3), integer(2)),
            SiteFactor::new(integer(-1), integer(5)),
            SiteFactor::new(rat(1, 2), rat(3, 4)),
        ] {
            let companion = site.companion();
            let sequence = site.trace_sequence(9);
            let mut power = mat2_identity();
            for (index, expected) in sequence.iter().enumerate() {
                assert_eq!(
                    mat2_trace(&power),
                    *expected,
                    "tr(M^{index}) must be the trace sequence"
                );
                power = mat2_multiply(&power, &companion);
            }
            assert_eq!(mat2_trace(&companion), *site.trace());
            assert_eq!(mat2_determinant(&companion), *site.determinant());
        }
    }

    #[test]
    fn conjugating_the_companion_moves_no_face() {
        let site = SiteFactor::new(rat(5, 2), integer(3));
        let carrier: Mat2 = [[rat(1, 2), integer(2)], [integer(3), integer(7)]];
        let conjugated = mat2_multiply(
            &mat2_multiply(&mat2_inverse(&carrier), &site.companion()),
            &carrier,
        );
        let carried = SiteFactor::new(mat2_trace(&conjugated), mat2_determinant(&conjugated));
        assert_eq!(carried.trace(), site.trace());
        assert_eq!(carried.determinant(), site.determinant());
        assert_eq!(
            carried.transfer_coefficients(),
            site.transfer_coefficients(),
            "the three transfer coefficients are conserved"
        );
        assert_eq!(carried.trace_sequence(8), site.trace_sequence(8));
        // And the conjugate's own power traces agree term by term.
        let mut power = mat2_identity();
        for expected in site.trace_sequence(8) {
            assert_eq!(mat2_trace(&power), expected);
            power = mat2_multiply(&power, &conjugated);
        }
    }

    #[test]
    fn newtons_identities_link_the_machines_coefficients_and_traces() {
        let machine = Machine::new(vec![
            SiteFactor::new(integer(3), integer(2)),
            SiteFactor::new(integer(-1), integer(5)),
            SiteFactor::new(rat(1, 2), rat(3, 4)),
        ]);
        let coefficients = machine.transfer_determinant();
        assert_eq!(coefficients.len(), 7, "three sites give degree six");
        assert_eq!(coefficients[0], Rat::one());
        let degree = coefficients.len() - 1;
        let traces = machine.trace_sequence(degree);
        assert_eq!(traces[0], integer(6), "t_0 counts the machine's roots");
        for k in 1..=degree {
            let mut right = Rat::zero();
            for index in 1..=k {
                right -= &coefficients[k - index] * &traces[index];
            }
            assert_eq!(
                &coefficients[k] * &integer(k as i64),
                right,
                "Newton's identity failed at k = {k}"
            );
        }
        // The product of the two single-site factors is the two-site machine's factor.
        let pair = Machine::new(vec![
            SiteFactor::new(integer(3), integer(2)),
            SiteFactor::new(integer(-1), integer(5)),
        ]);
        assert_eq!(
            pair.transfer_determinant(),
            vec![
                integer(1),
                integer(-2),
                integer(4),
                integer(-13),
                integer(10)
            ],
            "(1-3T+2T^2)(1+T+5T^2)"
        );
    }

    #[test]
    fn the_discriminant_classifies_the_site_and_a_shared_q_is_reported() {
        assert_eq!(
            SiteFactor::new(integer(1), integer(1)).kind(),
            SiteKind::Rotation
        );
        assert_eq!(
            SiteFactor::new(integer(4), integer(4)).kind(),
            SiteKind::Marginal
        );
        assert_eq!(
            SiteFactor::new(integer(5), integer(4)).kind(),
            SiteKind::Dilation
        );
        assert_eq!(
            SiteFactor::new(rat(1, 2), rat(1, 16)).kind(),
            SiteKind::Marginal,
            "a^2 = 1/4 = 4q exactly"
        );
        assert_eq!(
            Machine::new(vec![
                SiteFactor::new(integer(3), integer(2)),
                SiteFactor::new(integer(-1), integer(2)),
            ])
            .common_dilation(),
            Some(integer(2))
        );
        assert_eq!(
            Machine::new(vec![
                SiteFactor::new(integer(3), integer(2)),
                SiteFactor::new(integer(-1), integer(5)),
            ])
            .common_dilation(),
            None
        );
        assert_eq!(Machine::default().common_dilation(), None);
        assert_eq!(Machine::default().transfer_determinant(), vec![Rat::one()]);
    }
}
