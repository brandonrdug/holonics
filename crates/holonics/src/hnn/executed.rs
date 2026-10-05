//! **The located pair's deposit: a key located by loop closure becomes material by one certified
//! deposition of the source port** (THE_REBUILD, the library spine's S2; U6 lane B; #73, #148, #63).
//!
//! [definition; agent-inferred, October 5] Learning is locating keys (CLAUDE.md, "Keys and
//! navigation"). `hnn::keys` reads the menu of pair contacts over the seen passage and locates a
//! pair `(δ, f)` by loop closure (`compression::keys::TurnMenu`, the Bombe); this owner deposits it
//! ([`pair_deposit`]): the pair contact's slip against the declared prior,
//! `Δ_y = P^δ B e_y − (E − B) e_(f(y))`, descends along the source port's normal law by one
//! certified step of the library (`holon::deposition::CertifiedStep`), only at the loci the located
//! key reaches (the located classes' columns); on the declared opening that step closes the slip,
//! and the consumer `(E − B) T = P^δ B` holds on the menu's classes ([`PairDeposit::consumer`]
//! reads whether it does). The release reads the same slip ([`pair_slip`]) to find the contacts the
//! material holds closed (`hnn::prediction::closed_pairs`), and reads each candidate's pair storage
//! on equal material (lane C).
//!
//! **What this module no longer holds** [measured; the
//! [retirement record](../../../../research/records/2026-10-05_S2_THE_CERTIFIED_DESCENT_RETIRES_AND_KEY_LOCATION_THEN_DEPOSITION_REPLACES_IT.md)].
//! Until October 5 it held the release's own comparison (the class, threshold, order and section
//! predicates, the hinge and the lock face, their readings and covectors) and the certified descent
//! move on it (`Trial`, `ExecutedMove`, the halving ladder, `executed_move` and its witness,
//! kinetic and joined metrics, the release run). The descent read 1,024 observations on order-2
//! without locking the rule the terrain pins in 7, and a strictly monotone descent cannot cross a
//! sheet's flip; key location then deposition locked it from 16 and released 128 of 128 sections
//! whole on the final confirmation. The comparison and the move retired under S2 once that
//! acceptance read; their source is at
//! [`9078f103`](https://github.com/brandonrdug/holonics/blob/9078f103/crates/holonics/src/hnn/executed.rs),
//! their laws in Lean `HNN/ExecutedComparison`, `HNN/ReleaseRun` and `HNN/CarriedCuts`, in the
//! atlas rows (owner `H:` at that commit) and in their dated records.
//!
//! **Every modality deposits the same way**: an edge is two ticks of the source ring's clock and a
//! class map; nothing here reads a byte, a pixel or an alphabet's meaning.
//!
//! | Law | Lean | Rust |
//! |---|---|---|
//! | a located pair's deposit: the pair contact's slip against the carried prior, its exact line minimizer and the consumer `(E − B) T = P^δ B` (lane B, October 5) | owed (#62); the slip's derivative is `contact.dq` | [`pair_deposit`] |
//! | the closed contacts are the deposit's distances: a contact `y → x` at `δ` is closed exactly where its slip vanishes | owed (#62) | [`pair_slip`], read by `hnn::prediction::closed_pairs` |

use std::sync::OnceLock;

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use crate::hnn::HnnError;
use crate::hnn::constitution::{Constitution, Sample, SourceStep};
use crate::hnn::field::{ConstitutionRead, Field};
use crate::hnn::retention::retained_on_motion;
use crate::holon::deposition::CertifiedStep;
use crate::ratio::Rat;
use crate::ratio::algebraic::{ExactInterval, ln_enclosure};
use crate::ratio::linear::ExactRatMatrix;

/// [definition; agent-inferred, September 30] **The entry bound** `2³`: every entry of the source
/// port `E` at most three binary orders above the founding's unit scale (the certified step's pins,
/// acceptance 1: every development read stayed below 2, the divergence it excludes passed 316). A
/// condition of a deposit's adoption ([`pair_deposit`]), never a tally.
pub fn entry_bound() -> Rat {
    Rat::from_integer(BigInt::from(8))
}

/// `ln 2` enclosed on the declared grid, formed once (the reference's refining grain and the
/// receiving prior's grid member read it).
pub(crate) fn ln_two() -> Result<ExactInterval, HnnError> {
    static LN_TWO: OnceLock<ExactInterval> = OnceLock::new();
    if let Some(value) = LN_TWO.get() {
        return Ok(value.clone());
    }
    let value = ln_enclosure(&Rat::from_integer(BigInt::from(2)))?;
    Ok(LN_TWO.get_or_init(|| value).clone())
}

// -------------------------------------------------------------------------------------------
// the located pair's deposit (lane B, October 5)

/// [definition; agent-inferred, October 5; the
/// [record](../../../../research/records/2026-10-05_LOCATED_KEYS_BECOME_THE_SOURCE_PORTS_PAIR_COMPONENT.md)]
/// **The located pair's deposit**: learning is locating keys, and a located key becomes material by
/// one certified deposition of the source port. A [`crate::hnn::keys::LocatedPair`] at distance `δ`
/// with map `f` on its menu ports (read by loop closure over the seen passage, `hnn::keys`, "The
/// pair menu") is a pair contact between each consequence's column and its antecedent's image
/// carried over `δ` ticks by the ring's own transport `U = P^δ`. Its slip on a located class `y`,
/// against the source port's declared prior `B` (the opening `E₀`, the fixed feature map the normal
/// law keeps), is
///
/// ```text
/// Δ_y = U B e_y − (E − B) e_(f(y))          the consequence's learned part against the carried prior
/// Q = Σ_y ⟨Δ_y | Δ_y⟩,   ∂Q/∂(E e_(f(y))) = −2 Δ_y                         the pair contact's DQ = 2J*Δ
/// consumer: (E − B) T = U B   on the menu ports  (T e_y = e_(f(y)))
/// ```
///
/// so in the release's storage a continuation that follows the located pair carries, at its
/// antecedent's placement `P^(a+δ)`, the antecedent's prior image a second time
/// (`P^a (E − B) e_(f(y)) = P^(a+δ) B e_y`): a candidate that fits the key adds coherently to its
/// antecedent, one that does not adds a different column there. Every datum enters by the same law,
/// whatever its modality: the edge is two ticks of the source ring's clock and the class map.
///
/// The deposition is `Θ′|_U = Θ|_U + η Γ_U` at the loci `U` the located key reaches, the located
/// classes' columns of the source port, through its normal law (`Constitution::stepped_source`):
/// one sample per located class, feature `e_(f(y))`, covector `Δ_y`, weight one (the key, not its
/// count: the retention reads the located map, never how often it was seen). The slip is quadratic
/// along the law's unit step `D`, `Q(η) = Q − η a + ½ η² C` exactly with `a = 2Σ⟨Δ_y, D e_(f(y))⟩`
/// and `C = 2Σ |D e_(f(y))|²`, so its step is the library's certified step
/// (`holon::deposition::CertifiedStep`): the largest dyadic `η` with `η C ≤ a` and `η c ≤ 1`, `c`
/// the largest covector entry of one return, adopted only when `CertifiedStep::holds`, the slip falls
/// by at least the certified decrease `½ η a`, every entry stays within the [`entry_bound`], and the
/// constitution's own conditions hold (its storage growth certified, its budget). A key whose slip is
/// already zero moves nothing and is refused (`a = 0`). Refused, typed, when a menu port holds other
/// than one class of the exterior chart.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairDeposit {
    pub offset: usize,
    /// `(y, f(y))` on the exterior chart.
    pub classes: Vec<(usize, usize)>,
    pub slip_before: Rat,
    pub slip_after: Rat,
    /// The certified step: `η`, `a`, `C` and `c`.
    pub certificate: CertifiedStep,
    /// Whether `(E − B) T = U B` holds exactly on the menu's classes after the deposit.
    pub consumer: bool,
    pub source: SourceStep,
}

/// The exterior chart's one class at a ring's port (the residue chart holds one class at each port
/// when `|A| ≤ d_g`); refused otherwise.
fn class_at(field: &Field, ring: usize, port: usize) -> Result<usize, HnnError> {
    let geometry = field.ring(ring);
    let classes: Vec<usize> = (0..field.alphabet())
        .filter(|&code| geometry.port(code) == port)
        .collect();
    match classes.as_slice() {
        [class] => Ok(*class),
        _ => Err(HnnError::Shape {
            what: "a located port holding one class of the exterior chart",
            expected: 1,
            found: classes.len(),
        }),
    }
}

fn column(matrix: &ExactRatMatrix, class: usize) -> Result<Vec<Rat>, HnnError> {
    (0..matrix.rows())
        .map(|row| Ok(matrix.get(row, class)?.clone()))
        .collect()
}

/// **One pair contact's slip on the source port** ([`PairDeposit`]): the contact `y → x` at
/// distance `δ` on ring `g`, `Δ = P^δ B e_y − (E − B) e_x`, with `E` the port and `B` its declared
/// prior. It vanishes exactly when the port's learned part on `x` is `y`'s prior carried over `δ`
/// ticks: the deposit's consumer on that pair, and the release's reading of which pair contacts the
/// port holds closed (`hnn::prediction::BankPlacement::contacts`).
pub fn pair_slip(
    field: &Field,
    ring: usize,
    port: &ExactRatMatrix,
    prior: &ExactRatMatrix,
    offset: usize,
    (y, x): (usize, usize),
) -> Result<Vec<Rat>, HnnError> {
    let image = field.ring(ring).rotate(&column(prior, y)?, &BigInt::from(offset));
    let (learned, base) = (column(port, x)?, column(prior, x)?);
    Ok(image
        .iter()
        .zip(learned.iter().zip(&base))
        .map(|(u, (e, b))| u - (e - b))
        .collect())
}

/// The slips `Δ_y` of every located class at the port `E`.
fn pair_slips(
    field: &Field,
    ring: usize,
    port: &ExactRatMatrix,
    prior: &ExactRatMatrix,
    offset: usize,
    classes: &[(usize, usize)],
) -> Result<Vec<Vec<Rat>>, HnnError> {
    classes
        .iter()
        .map(|&pair| pair_slip(field, ring, port, prior, offset, pair))
        .collect()
}

fn squared(vectors: &[Vec<Rat>]) -> Rat {
    vectors.iter().flatten().map(|x| x * x).sum()
}

/// **Deposit a located pair** (the type [`PairDeposit`]) on `constitution`'s source port of `ring`,
/// against the declared prior `prior` (the opening's `E₀`).
pub fn pair_deposit(
    field: &Field,
    constitution: &Constitution,
    prior: &ExactRatMatrix,
    ring: usize,
    located: &crate::hnn::keys::LocatedPair,
) -> Result<(Constitution, PairDeposit), HnnError> {
    let port = constitution
        .source_port(ring)
        .ok_or(HnnError::MissingSourcePort { ring })?
        .clone();
    if prior.rows() != port.rows() || prior.columns() != port.columns() {
        return Err(HnnError::Shape {
            what: "the declared prior against the source port",
            expected: port.rows() * port.columns(),
            found: prior.rows() * prior.columns(),
        });
    }
    let classes = located
        .map
        .iter()
        .map(|&(from, to)| Ok((class_at(field, ring, from)?, class_at(field, ring, to)?)))
        .collect::<Result<Vec<_>, HnnError>>()?;
    let slips = pair_slips(field, ring, &port, prior, located.offset, &classes)?;
    let slip_before = squared(&slips);
    let unit_feature = |class: usize| -> Vec<Rat> {
        (0..field.alphabet())
            .map(|code| if code == class { Rat::one() } else { Rat::zero() })
            .collect()
    };
    let samples: Vec<Sample> = classes
        .iter()
        .zip(&slips)
        .map(|(&(_, x), slip)| Sample {
            weight: Rat::one(),
            feature: unit_feature(x),
            covector: slip.clone(),
        })
        .collect();
    let retained = retained_on_motion(field, &[ring]);
    let refused = |what: &'static str| HnnError::Shape {
        what,
        expected: 1,
        found: 0,
    };
    let (unit, _) = constitution
        .stepped_source(ring, &samples, &Rat::one(), &retained)?
        .ok_or_else(|| refused("a located pair whose slip reaches the source port"))?;
    let moved = unit
        .source_port(ring)
        .ok_or(HnnError::MissingSourcePort { ring })?;
    let direction: Vec<Vec<Rat>> = classes
        .iter()
        .map(|&(_, x)| {
            Ok(column(moved, x)?
                .iter()
                .zip(column(&port, x)?)
                .map(|(a, b)| a - b)
                .collect())
        })
        .collect::<Result<_, HnnError>>()?;
    let two = Rat::from_integer(BigInt::from(2));
    let along: Rat = slips
        .iter()
        .zip(&direction)
        .map(|(slip, d)| slip.iter().zip(d).map(|(a, b)| a * b).sum::<Rat>())
        .sum();
    let alignment = &two * along;
    let curvature = &two * squared(&direction);
    let covector = slips
        .iter()
        .flatten()
        .map(Signed::abs)
        .max()
        .unwrap_or_else(Rat::zero);
    let certificate = CertifiedStep::certify(&alignment, &curvature, &covector)?
        .ok_or_else(|| refused("a located pair whose slip the unit step descends"))?;
    if !certificate.holds() {
        return Err(refused("a certified step that holds"));
    }
    let (next, source) = constitution
        .stepped_source(ring, &samples, &certificate.step, &retained)?
        .ok_or_else(|| refused("a located pair whose slip reaches the source port"))?;
    let stepped = next
        .source_port(ring)
        .ok_or(HnnError::MissingSourcePort { ring })?;
    if stepped.entries().iter().any(|entry| entry.abs() > entry_bound()) {
        return Err(refused("a deposit within the entry bound"));
    }
    let after = pair_slips(field, ring, stepped, prior, located.offset, &classes)?;
    let slip_after = squared(&after);
    if slip_after > &slip_before - certificate.decrease() {
        return Err(refused("a deposit whose slip falls by its certified decrease"));
    }
    let consumer = after.iter().flatten().all(Zero::is_zero);
    Ok((
        next,
        PairDeposit {
            offset: located.offset,
            classes,
            slip_before,
            slip_after,
            certificate,
            consumer,
            source,
        },
    ))
}

