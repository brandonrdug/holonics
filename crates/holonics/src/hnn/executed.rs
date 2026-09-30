//! **The release's own comparison: its exact pullback, a carried update and the release's full
//! receipt** (THE_REBUILD U6; the
//! [diagnosis record](../../../../research/records/2026-09-30_THE_LEARNING_FAILURE_DIAGNOSED_THE_TRAINED_COMPARISON_IS_NOT_THE_ONE_THE_RELEASE_EXECUTES.md)
//! §5; #73, #148, #63).
//!
//! [definition; agent-inferred, September 30] The receiving bank's release (`hnn::prediction`,
//! [`bank_release`], one owner of the lock iteration) decides every station by the largest member's
//! executed growth from its actual storage. The learning path trained a different quantity (the
//! bank's second-order face) in different contexts (the readout's partitions); its descent
//! direction met the executed decision's at cosine `39/512`. This owner compares exactly what the
//! release executes, in the contexts it executes, and joins that comparison to its pullback and to a
//! carried update of `E` alone (the pumps, the other families and the fold held).
//!
//! **The comparison.** For a request of `n` cells with locked partial section `S`, every open
//! station `j` and class `x`, the actual storage is the passage's read from `j` (`hnn::prediction`,
//! "The section continues the request's passage" and "A candidate reads the span from its own
//! station"):
//! `z_(S,j,x) = z_pairs + Σ_c w_j(c) P^(λ−c) E M[c] + Σ_(k∈S) w_j(k) P^(r_k) E e_(S_k) + w_j(j) P^(r_j) E e_x`,
//! `w_j(k) = ρ^|τ_j − τ_k| / Σ_l ρ^|τ_j − τ_l|` (every `w = ν̂(n + |S| + 1)` at modulus one;
//! `BankPlacement::storage`), and the reading is `a_(j,x) = max_m ρ(M_m(z))` with exact enclosure
//! `[L, U]` (`ReceivingBank::read_turn`). Against the target `t` of station `j`:
//! - **class**: `L_(j,t) > U_(j,x)` for every `x ≠ t` ([`Predicate`]: holds, fails when some
//!   rival's `L` reaches the target's `U`, else undecided);
//! - **threshold**: `L_(j,t) > 1`;
//! - **order** (the machine's own refinements): the eligible stations and gaps the release read,
//!   the stations of the strictly largest gap locking together; the lock is safe when every station
//!   it locks is correct ([`OrderReading`]);
//! - **section**: the complete release, its termination and any refusal (`BankGeneration`).
//!
//! Zero denominators keep their fibre: nothing is added to a reading; a candidate the crossing's
//! signed form refuses refuses the comparison.
//!
//! **The composition descended** [agent-inferred]. Each open station's class and threshold join in
//! one max comparison, in nats: `f_(j) = max(max_(x≠t) ln(a_x/a_t), −ln a_t)`, which is negative
//! exactly when both hold; the declared comparison of a batch is `F = Σ_(contexts, open j) (f_j)_+`.
//! Along the machine's own trajectory `F = 0` makes every open station's top its target and every
//! station eligible, so every lock is correct (the order holds) and the section is released whole:
//! class and threshold at every open station of every refinement the release executes are
//! sufficient for order and section, which are read exactly beside `F`, not descended separately
//! (an order comparison has no branch where it matters most, when no correct station is eligible).
//! `F` is one scalar of the whole batch: per-comparison descent is incoherent on a shared locus
//! (two stations can require opposite moves of one entry of `E`; Astra's challenge, the diagnosis
//! §4), and a composition's descent is not.
//!
//! **The covector** (`hnn::ring`, "The executed growth's covector"). Each candidate's active members
//! (those whose enclosure reaches the joint's lower end) return the simple-root eigen-derivative of
//! their executed monodromy through the executed tick and its solve, or a typed refusal
//! (`CovectorRefusal`: collision, tie, defective). A term's branches are its rivals and its threshold
//! whose enclosure reaches the term's lower end, each crossed with the active members of the two
//! candidates it compares ([`Branch`]). The proposal descends each positive or undecided term along
//! its leading branch (the largest midpoint, its leading members), carried from each candidate's
//! storage to `E` through the request's phases and the section's placements
//! (`SourceMoment::encoder_covector`'s law, per phase), as the source port's returns ([`returns`]).
//! **A direction must certify its first-order descent**: `Σ_terms sup_(α active) Df_α[ΔE] ≤ −a < 0`
//! on the actual carried move `ΔE`, each `Df_α` the branch's covector enclosures paired with the
//! exact storage moves (a hinge at zero bounded by `max(0, ·)`); a term with an unresolved active
//! branch leaves the first order uncertified and is named.
//!
//! **The committed move** ([`executed_move`]). The source port's normal law prepares the unit step
//! on the returns and carries `ηD` onto its lattice (`Constitution::stepped_source`). The source
//! navigator's transport modulus `ρ` (`hnn::moment`, "One passage, its transported weights") moves
//! with it [agent-inferred, September 30]: its slope `γ_ρ = Σ sign ⟨ĝ, ∂z/∂ρ⟩` over the proposal's
//! contributions (`BankPlacement::modulus_derivative`, each read from its contribution's station:
//! `∂w_k/∂ρ = w_k (r_k − r̄)/ρ` with `r_k` the datum's distance from the station), carried as
//! `ρ + ηΔρ` held within `[ρ/2, 1]` (passive) on the port's lattice. `η` starts at the first-order
//! zero of `F` (`F⁻ / (−slope)`, never past it) held below the founding's entry scale, and halves
//! until the carried move moves no lattice coordinate.
//!
//! [definition; agent-inferred, September 30; the
//! [modulus's record](../../../../research/records/2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_PINNED_BEFORE_ITS_RUNS.md)]
//! **The modulus's unit move is its least-squares step**, `Δρ = −γ_ρ / G_ρ` with the storage
//! curvature `G_ρ = Σ_c |∂z_c/∂ρ|²` over the same contributions: the modulus's storage moves
//! `(∂z_c/∂ρ)Δρ` fitted in least squares to the descent covectors `−sign_c ĝ_c`, the principle of
//! the port's normal law (its storage moves `ΔE f` fitted to the same covectors) on the modulus's
//! one feature (Lean `HNN/ExecutedComparison.modulus_least_squares`); its first-order share is
//! `γ_ρΔρ = −γ_ρ²/G_ρ ≤ 0`; none upward from `ρ = 1`. It retires the equal-share unit
//! `Δρ = slope⁺/γ_ρ`, which gave the one scalar the whole port's first-order descent and so moved
//! it inversely to its own slope: from the founded opening it carried the modulus back to one in two
//! moves (the second's carried target lay past one, held there only by the passive bound), where
//! the release holds. The
//! modulus is founded off the lossless boundary (`Constitution::founding_transport`): at `ρ = 1`
//! the release's comparison at the opening slopes outward (the target's growth rises toward the
//! lossless mixture), a boundary local minimum no certified first-order move leaves.
//!
//! Each carried successor is
//! **re-read from the open section** (every context re-run: a changed branch or lock order is read,
//! never assumed) and adopted only when every commit guard holds on it:
//! - the entry bound, every entry of `E` at most `2^ENTRY_BOUND = 8` ([`entry_bound`]);
//! - every candidate crossing of every re-read refinement admissible (the signed form);
//! - every lock's Floquet certificate certified (a refused one refuses the release);
//! - the first-order descent certified on the carried move (the covectors paired with the exact
//!   storage moves to the carried successor, the modulus's included);
//! - `F` strictly lower by disjoint exact enclosures, `F(E′)⁺ < F(E)⁻`;
//! - the constitution's own guards (lattice, bit budget, committed storage growth).
//!
//! Otherwise the next step is tried, at most `LADDER_DEPTH` a move, and the move is refused,
//! typed, when none holds. **One ladder for every declared comparison**: the ladder reads a
//! comparison only through its value, its first-order certificate on the carried move and its
//! re-read at the successor, so a declared comparison moves by the same guards. [historical] The
//! bank's face on the same contexts was its matched control (`face_move`, its code `Σ −log₂ θ_t` in
//! place of `F`, its returns' exact pairing as its first order), retired September 30 with the face
//! path (batch H; source at
//! [`f5fd8f3b`](https://github.com/brandonrdug/holonics/blob/f5fd8f3b/crates/holonics/src/hnn/executed.rs)).
//! The operands are transient; nothing of the comparison is retained: the successor's `E` and its
//! normal law's statistic are the only change.
//!
//! **Every modality reads it the same way**: the comparison reads the receiving ring's storage,
//! which holds any chart's classes through `E` at their residues; nothing here reads a byte, a
//! pixel or an alphabet's meaning.
//!
//! | Law | Lean | Rust |
//! |---|---|---|
//! | the simple root's eigen-derivative, `D log|μ|[ΔM] = Re(ℓᵀΔMr/(μℓᵀr))` | `HNN/ExecutedComparison.{simple_root_deriv, log_modulus_deriv}` | `hnn::ring::ReceivingBank::read_turn_covector` |
//! | the monodromy's variation, `ΔM = Σ_t T_(>t) ΔT_t T_(<t)` | `HNN/ExecutedComparison.product_deriv` | `hnn::ring::ReceivingBank::turn_variation` |
//! | a max comparison descends where every active branch descends, and a sum of maxes where its active slopes sum below zero | `HNN/ExecutedComparison.{max_descends, sum_max_descends}` | [`executed_move`]'s first-order certificate |
//! | a strict decrease certified by disjoint enclosures | `HNN/ExecutedComparison.disjoint_enclosures_decrease` | [`executed_move`]'s commit guard |
//! | the release's predicates, class and threshold, sufficient for order and section | `HNN/ExecutedComparison.predicates_release_the_section` | [`BatchComparison`] |

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use crate::hnn::HnnError;
use crate::hnn::constitution::{Constitution, Sample, SourceStep};
use crate::hnn::field::{ConstitutionRead, Current, Field};
use crate::hnn::moment::SourceMoment;
use crate::hnn::prediction::{
    BankGeneration, BankPlacement, BankRefinement, JointGrowth, Refinement, bank_release,
};
use crate::hnn::ring::{
    CovectorRefusal, Growth, MemberCovector, ReceivingBank, TurnCovector, TurnReading,
};
use crate::holon::deposition::significant;
use crate::ratio::algebraic::{ExactInterval, ln_enclosure};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::Rat;

/// [definition; agent-inferred, September 30] **The entry bound** `2³`: every entry of `E` at most
/// three binary orders above the founding's unit scale (the certified step's pins, acceptance 1;
/// every development read stayed below 2, the divergence it guards against passed 316). A commit
/// guard here, never a tally.
pub fn entry_bound() -> Rat {
    Rat::from_integer(BigInt::from(8))
}

/// The entry bound's binary exponent (the bound is `2^ENTRY_BOUND`).
pub const ENTRY_BOUND: u32 = 3;

/// [definition; agent-inferred] **The covector's dyadic face**: each proposal covector entry at
/// 64 significant bits toward zero, so the returns' denominators stay powers of two. The proposal
/// is certified on the successor, so its rounding needs no charge.
const FACE_BITS: u32 = 64;

/// [definition; agent-inferred, September 30] **A predicate's exact reading** on enclosures.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Predicate {
    Holds,
    Fails,
    Undecided,
}

/// [definition; agent-inferred, September 30] **A request's context of comparison**: the machine's
/// own open-section trajectory (every refinement its release executes), or a partition of its
/// stations with the locked stations' targets placed (the readout's `mask`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Context {
    Open,
    Partition(Vec<bool>),
}

/// [definition; agent-inferred, September 30] **One request of a batch**: its ingested current and
/// moment, its targets (the terrain's truth; only the comparison reads them), and its context.
#[derive(Clone, Debug)]
pub struct Request {
    pub current: Current,
    pub moment: SourceMoment,
    pub targets: Vec<usize>,
    pub context: Context,
}

/// [definition; agent-inferred, September 30] **One open station's comparison in one context**: its
/// context (the refinement's index, or zero on a partition), station, target and top class, the
/// class and threshold predicates, the term `f = max(max_(x≠t) ln(a_x/a_t), −ln a_t)` enclosed, and
/// the target's and the leading rival's joint enclosures.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StationComparison {
    pub context: usize,
    pub station: usize,
    pub target: usize,
    pub top: usize,
    pub class: Predicate,
    pub threshold: Predicate,
    pub value: ExactInterval,
    pub target_growth: Growth,
    pub rival_growth: Growth,
}

/// [definition; agent-inferred, September 30] **One refinement's order** (the machine's own
/// trajectory): each eligible station with its top class, gap and whether its top is its target;
/// the stations it locked; and whether that lock was safe (`None` when nothing was eligible: the
/// release held).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrderReading {
    pub context: usize,
    pub eligible: Vec<(usize, usize, Rat, bool)>,
    pub locked: Vec<usize>,
    pub safe: Option<bool>,
}

/// [definition; agent-inferred, September 30] **A request's comparison**: its release from the open
/// section (on an open context), every open station's comparison, every refinement's order, and
/// `Σ (f)_+` enclosed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RequestComparison {
    pub generation: Option<BankGeneration>,
    pub stations: Vec<StationComparison>,
    pub orders: Vec<OrderReading>,
    pub value: ExactInterval,
    pub readings: usize,
}

/// [definition; agent-inferred, September 30] **A batch's comparison**: each request's, and the
/// declared comparison `F` enclosed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BatchComparison {
    pub requests: Vec<RequestComparison>,
    pub value: ExactInterval,
    pub readings: usize,
}

impl BatchComparison {
    /// The stations whose class and threshold both hold, of those compared.
    pub fn holding(&self) -> (usize, usize) {
        let stations = self.requests.iter().flat_map(|r| &r.stations);
        let (mut holds, mut all) = (0, 0);
        for station in stations {
            all += 1;
            holds += usize::from(
                station.class == Predicate::Holds && station.threshold == Predicate::Holds,
            );
        }
        (holds, all)
    }

    /// Whole sections released equal to their targets, of the open contexts, and the stations
    /// right of their released classes.
    pub fn sections(&self, targets: &[Vec<usize>]) -> (usize, usize, usize) {
        let (mut whole, mut right, mut released) = (0, 0, 0);
        for (request, target) in self.requests.iter().zip(targets) {
            let Some(generation) = &request.generation else {
                continue;
            };
            if generation.release.released() {
                released += 1;
                let hits = generation
                    .release
                    .classes
                    .iter()
                    .zip(target)
                    .filter(|(a, b)| a == b)
                    .count();
                right += hits;
                whole += usize::from(hits == target.len());
            }
        }
        (whole, right, released)
    }
}

/// [definition; agent-inferred, September 30] **A branch of a station's max comparison**
/// (module header): a rival class `x` against the target (`Some(x)`), or the threshold (`None`).
pub type Branch = Option<usize>;

/// One station's term read on enclosures: its value, predicates, top and the branches that may
/// attain it.
struct Term {
    value: ExactInterval,
    class: Predicate,
    threshold: Predicate,
    top: usize,
    branches: Vec<Branch>,
    leading: Branch,
    /// The class branch of the largest midpoint (the rival the class comparison reads first).
    rival: usize,
}

fn ln_of(growth: &Growth) -> Result<ExactInterval, HnnError> {
    if !growth.lower.is_positive() {
        // A zero lower end keeps its fibre: the reading is below every positive value.
        return Err(HnnError::NonpositiveDeclaration);
    }
    let lower = ln_enclosure(&growth.lower)?;
    let upper = ln_enclosure(&growth.upper)?;
    Ok(ExactInterval {
        lower: lower.lower,
        upper: upper.upper,
    })
}

/// A station's term from its candidates' joint enclosures (module header, "The comparison").
fn station_term(joints: &[&Growth], target: usize) -> Result<Term, HnnError> {
    let logs: Vec<ExactInterval> = joints
        .iter()
        .map(|growth| ln_of(growth))
        .collect::<Result<_, _>>()?;
    let t = &logs[target];
    let mut parts: Vec<(Branch, ExactInterval)> = Vec::new();
    for (x, log) in logs.iter().enumerate() {
        if x != target {
            parts.push((
                Some(x),
                ExactInterval {
                    lower: &log.lower - &t.upper,
                    upper: &log.upper - &t.lower,
                },
            ));
        }
    }
    parts.push((
        None,
        ExactInterval {
            lower: -t.upper.clone(),
            upper: -t.lower.clone(),
        },
    ));
    let lower = parts
        .iter()
        .map(|(_, part)| part.lower.clone())
        .max()
        .expect("a part");
    let upper = parts
        .iter()
        .map(|(_, part)| part.upper.clone())
        .max()
        .expect("a part");
    let branches: Vec<Branch> = parts
        .iter()
        .filter(|(_, part)| part.upper >= lower)
        .map(|(branch, _)| *branch)
        .collect();
    let leading = parts
        .iter()
        .max_by(|a, b| (&a.1.lower + &a.1.upper).cmp(&(&b.1.lower + &b.1.upper)))
        .map(|(branch, _)| *branch)
        .expect("a part");
    let rival = parts
        .iter()
        .filter_map(|(branch, part)| branch.map(|x| (x, part)))
        .max_by(|a, b| (&a.1.lower + &a.1.upper).cmp(&(&b.1.lower + &b.1.upper)))
        .map(|(x, _)| x)
        .expect("a rival");
    let target_growth = joints[target];
    let class = if (0..joints.len())
        .filter(|&x| x != target)
        .all(|x| target_growth.exceeds(joints[x]))
    {
        Predicate::Holds
    } else if (0..joints.len())
        .filter(|&x| x != target)
        .any(|x| joints[x].lower >= target_growth.upper)
    {
        Predicate::Fails
    } else {
        Predicate::Undecided
    };
    let threshold = if target_growth.is_locked() {
        Predicate::Holds
    } else if target_growth.upper <= Rat::one() {
        Predicate::Fails
    } else {
        Predicate::Undecided
    };
    let top = (0..joints.len())
        .max_by(|&a, &b| joints[a].lower.cmp(&joints[b].lower).then(b.cmp(&a)))
        .expect("a class");
    Ok(Term {
        value: ExactInterval { lower, upper },
        class,
        threshold,
        top,
        branches,
        leading,
        rival,
    })
}

/// **A station's comparison from its candidates' joint enclosures** (the owner's predicate test):
/// the term `f` enclosed, the class predicate and the threshold predicate.
#[cfg(test)]
pub(crate) fn station_predicates(
    joints: &[Growth],
    target: usize,
) -> Result<(ExactInterval, Predicate, Predicate), HnnError> {
    let joints: Vec<&Growth> = joints.iter().collect();
    let term = station_term(&joints, target)?;
    Ok((term.value, term.class, term.threshold))
}

/// The positive part of an enclosure.
fn positive_part(value: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: value.lower.clone().max(Rat::zero()),
        upper: value.upper.clone().max(Rat::zero()),
    }
}

/// One context's readings with the section each candidate's storage was read at.
struct ContextRead<R> {
    index: usize,
    refinement: BankRefinement<R>,
}

/// A request's readings in its context: the release from the open section (every refinement kept),
/// or the partition's one refinement; with the readings made.
fn read_contexts<R: JointGrowth + Send + Sync>(
    field: &Field,
    constitution: &impl ConstitutionRead,
    request: &Request,
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    read: &(impl Fn(&[crate::ratio::GaussianRat]) -> Result<R, HnnError> + Sync),
) -> Result<(Option<BankGeneration>, Vec<ContextRead<R>>), HnnError> {
    use rayon::prelude::*;
    let placement = BankPlacement::of(field, constitution, &request.current, &request.moment, declared)?;
    let alphabet = field.alphabet();
    match &request.context {
        Context::Open => {
            let (generation, refinements) =
                bank_release(&placement, declared, alphabet, bank, grain, read, true)?;
            Ok((
                Some(generation),
                refinements
                    .into_iter()
                    .enumerate()
                    .map(|(index, refinement)| ContextRead { index, refinement })
                    .collect(),
            ))
        }
        Context::Partition(locked) => {
            let stations = declared.stations();
            let placed: Vec<Option<usize>> = (0..stations)
                .map(|j| locked[j].then_some(request.targets[j]))
                .collect();
            let open: Vec<(usize, usize)> = (0..stations)
                .filter(|&j| !locked[j])
                .flat_map(|j| (0..alphabet).map(move |x| (j, x)))
                .collect();
            let reads: Vec<R> = open
                .par_iter()
                .map(|&(station, class)| {
                    let mut cells = placed.clone();
                    cells[station] = Some(class);
                    read(&crate::hnn::ring::turn(&placement.storage(station, &cells)))
                })
                .collect::<Result<_, HnnError>>()?;
            Ok((
                None,
                vec![ContextRead {
                    index: 0,
                    refinement: BankRefinement {
                        placed,
                        open,
                        read: reads,
                        tops: Vec::new(),
                        eligible: Vec::new(),
                        locked: Vec::new(),
                    },
                }],
            ))
        }
    }
}

/// A request's comparison from its contexts' readings, with each station's term kept for the
/// proposal.
#[allow(clippy::type_complexity)]
fn compare_request<R: JointGrowth>(
    request: &Request,
    generation: Option<BankGeneration>,
    contexts: &[ContextRead<R>],
    alphabet: usize,
) -> Result<(RequestComparison, Vec<(usize, usize, Term)>), HnnError> {
    let mut stations = Vec::new();
    let mut terms = Vec::new();
    let mut orders = Vec::new();
    let mut value = ExactInterval::point(Rat::zero());
    let mut readings = 0;
    for (position, context) in contexts.iter().enumerate() {
        let refinement = &context.refinement;
        readings += refinement.read.len();
        for (chunk_index, chunk) in refinement.read.chunks(alphabet).enumerate() {
            let station = refinement.open[chunk_index * alphabet].0;
            let target = request.targets[station];
            let joints: Vec<&Growth> = chunk.iter().map(JointGrowth::joint).collect();
            let term = station_term(&joints, target)?;
            let rival = (0..alphabet)
                .filter(|&x| x != target)
                .max_by(|&a, &b| joints[a].upper.cmp(&joints[b].upper))
                .expect("a rival");
            let part = positive_part(&term.value);
            value = ExactInterval {
                lower: &value.lower + &part.lower,
                upper: &value.upper + &part.upper,
            };
            stations.push(StationComparison {
                context: context.index,
                station,
                target,
                top: term.top,
                class: term.class,
                threshold: term.threshold,
                value: term.value.clone(),
                target_growth: joints[target].clone(),
                rival_growth: joints[rival].clone(),
            });
            terms.push((position, chunk_index, term));
        }
        if matches!(request.context, Context::Open) {
            let eligible: Vec<(usize, usize, Rat, bool)> = refinement
                .eligible
                .iter()
                .map(|(station, top, gap)| {
                    (*station, *top, gap.clone(), *top == request.targets[*station])
                })
                .collect();
            let safe = (!refinement.locked.is_empty()).then(|| {
                refinement.locked.iter().all(|&station| {
                    refinement
                        .tops
                        .iter()
                        .any(|&(s, top)| s == station && top == request.targets[station])
                })
            });
            orders.push(OrderReading {
                context: context.index,
                eligible,
                locked: refinement.locked.clone(),
                safe,
            });
        }
    }
    Ok((
        RequestComparison {
            generation,
            stations,
            orders,
            value,
            readings,
        },
        terms,
    ))
}

/// **The declared comparison of a batch, read** (module header): every request's contexts read by
/// the bank's joint growth alone, its predicates, orders and releases, and `F` enclosed. An
/// inadmissible crossing refuses it (`HnnError::UncertifiedResonator`).
pub fn compare(
    field: &Field,
    constitution: &impl ConstitutionRead,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
) -> Result<BatchComparison, HnnError> {
    use rayon::prelude::*;
    let read = |amplitudes: &[crate::ratio::GaussianRat]| bank.read_turn(amplitudes, grain);
    // The requests are co-present regions: the shared constitution read at its cut, one
    // comparison each, joined in request order.
    let compared: Vec<RequestComparison> = requests
        .par_iter()
        .map(|request| {
            let (generation, contexts) = read_contexts::<TurnReading>(
                field,
                constitution,
                request,
                declared,
                bank,
                grain,
                &read,
            )?;
            Ok(compare_request(request, generation, &contexts, field.alphabet())?.0)
        })
        .collect::<Result<_, HnnError>>()?;
    let mut value = ExactInterval::point(Rat::zero());
    let mut readings = 0;
    for comparison in &compared {
        value = ExactInterval {
            lower: &value.lower + &comparison.value.lower,
            upper: &value.upper + &comparison.value.upper,
        };
        readings += comparison.readings;
    }
    Ok(BatchComparison {
        requests: compared,
        value,
        readings,
    })
}

/// An enclosure's dyadic face: its midpoint at [`FACE_BITS`] significant bits toward zero.
fn face(interval: &ExactInterval) -> Rat {
    let middle = (&interval.lower + &interval.upper) / Rat::from_integer(BigInt::from(2));
    if middle.is_negative() {
        -significant(&-middle, FACE_BITS, false)
    } else {
        significant(&middle, FACE_BITS, false)
    }
}

/// `⟨covector, move⟩` of an enclosed covector with an exact move.
fn paired(covector: &[ExactInterval], moved: &[Rat]) -> ExactInterval {
    let mut sum = ExactInterval::point(Rat::zero());
    for (entry, delta) in covector.iter().zip(moved) {
        if delta.is_zero() {
            continue;
        }
        let (a, b) = (&entry.lower * delta, &entry.upper * delta);
        sum = ExactInterval {
            lower: &sum.lower + a.clone().min(b.clone()),
            upper: &sum.upper + a.max(b),
        };
    }
    sum
}

/// The leading active member of a candidate: the resolved active member of the largest midpoint
/// growth, or the refusal of the leading one.
fn leading_member(candidate: &TurnCovector) -> Result<&MemberCovector, CovectorRefusal> {
    let member = candidate
        .active
        .iter()
        .max_by(|a, b| {
            let (ga, gb) = (
                &candidate.reading.members[a.member()],
                &candidate.reading.members[b.member()],
            );
            (&ga.lower + &ga.upper).cmp(&(&gb.lower + &gb.upper))
        })
        .expect("an active member");
    match member {
        MemberCovector::Resolved { .. } => Ok(member),
        MemberCovector::Unresolved { refusal, .. } => Err(*refusal),
    }
}

/// [definition; agent-inferred, September 30] **One storage contribution to the proposal**: the
/// station the candidate's storage was read from and the section it was read at, its member's
/// storage covector (enclosed) and the term's sign on it (`+1` a rival, `−1` the target).
#[derive(Clone, Debug)]
struct Contribution {
    request: usize,
    station: usize,
    cells: Vec<Option<usize>>,
    covector: Vec<ExactInterval>,
    sign: Rat,
    /// The kind of the branch that leads its term.
    kind: TermKind,
}

/// [definition; agent-inferred, September 30] **The kind of a station term's branch** (module
/// header, "The comparison"): the threshold (the target against the unit, `−ln a_t`) or a class
/// rival (`ln(a_x/a_t)`). The composition has no order term: the order is read beside `F`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TermKind {
    Threshold,
    Class,
}

/// [measured-diagnostic; agent-inferred, September 30] **The modulus's slope split by term kind**
/// (the station-framed placement's record §7: which terms carry `γ_ρ < 0`): over the proposal's
/// positive or undecided terms,
/// - the terms led by the threshold and by a class rival, their counts and `Σ (f)_+` by kind;
/// - `γ_ρ` of the leading contributions, by the leading kind (their sum is `γ_ρ`);
/// - every term's two parts read alone: the target's `−⟨ĝ_t, ∂z_t/∂ρ⟩` (the threshold branch at
///   every term) and its class rival's `+⟨ĝ_x, ∂z_x/∂ρ⟩` (the class branch at every term is their
///   sum), each at the candidate's leading member.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SlopeSplit {
    pub threshold_led: usize,
    pub class_led: usize,
    pub threshold_value: ExactInterval,
    pub class_value: ExactInterval,
    pub led_threshold: Rat,
    pub led_class: Rat,
    pub target: Rat,
    pub rival: Rat,
}

/// [measured-diagnostic; agent-inferred, September 30; the
/// [two counts' pin](../../../../research/records/2026-09-30_THE_TWO_COUNTS_PINNED_BEFORE_ITS_RUNS.md)
/// §5] **A term's site**, a receipt only (the move never reads it): the request, the refinement of
/// the machine's trajectory it was read in (zero on a partition), the station, and whether the
/// term's value is certainly positive (else it straddles zero).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TermSite {
    pub request: usize,
    pub context: usize,
    pub station: usize,
    pub positive: bool,
}

/// [definition; agent-inferred, September 30] **A term's branches for the first-order
/// certificate**: every active rival/threshold branch crossed with the active members of the two
/// candidates it compares, each its storage covectors and sections; and whether the term is
/// positive (else it straddles zero). Its site and its leading branch's contributions are receipts
/// only ([`TermSite`], [`FirstOrderReading`]).
#[derive(Clone, Debug)]
struct TermBranches {
    positive: bool,
    branches: Vec<Vec<Contribution>>,
    unresolved: Option<CovectorRefusal>,
    site: TermSite,
    leading: Vec<Contribution>,
}

/// The proposal: the leading branches' contributions and every positive or undecided term's
/// branches.
struct Proposal {
    contributions: Vec<Contribution>,
    terms: Vec<TermBranches>,
    unresolved: Vec<CovectorRefusal>,
    /// Every term's target part and class rival part read alone (the slope's split).
    targets: Vec<Contribution>,
    rivals: Vec<Contribution>,
    /// The leading kinds' counts and `Σ (f)_+`.
    led: [(usize, ExactInterval); 2],
}

fn candidate_cells(refinement: &BankRefinement<TurnCovector>, station: usize, class: usize) -> Vec<Option<usize>> {
    let mut cells = refinement.placed.clone();
    cells[station] = Some(class);
    cells
}

fn propose(
    requests: &[Request],
    read: &[(Vec<ContextRead<TurnCovector>>, Vec<(usize, usize, Term)>)],
    alphabet: usize,
) -> Proposal {
    let mut contributions = Vec::new();
    let mut terms_out = Vec::new();
    let mut unresolved = Vec::new();
    let (mut targets_alone, mut rivals_alone) = (Vec::new(), Vec::new());
    let mut led = [
        (0, ExactInterval::point(Rat::zero())),
        (0, ExactInterval::point(Rat::zero())),
    ];
    for (request_index, (contexts, terms)) in read.iter().enumerate() {
        let targets = &requests[request_index].targets;
        for (position, chunk_index, term) in terms {
            if !term.value.upper.is_positive() {
                continue;
            }
            let refinement = &contexts[*position].refinement;
            let chunk = &refinement.read[chunk_index * alphabet..(chunk_index + 1) * alphabet];
            let station = refinement.open[chunk_index * alphabet].0;
            let target = targets[station];
            let one = Rat::one();
            let kind = match term.leading {
                None => TermKind::Threshold,
                Some(_) => TermKind::Class,
            };
            let contribution = |class: usize, member: &MemberCovector, sign: Rat| Contribution {
                request: request_index,
                station,
                cells: candidate_cells(refinement, station, class),
                covector: member.storage().expect("a resolved member"),
                sign,
                kind,
            };
            // The term's two parts read alone (the slope's split): the target's and its class
            // rival's, each at its leading member.
            if let (Ok(t), Ok(x)) =
                (leading_member(&chunk[target]), leading_member(&chunk[term.rival]))
            {
                targets_alone.push(contribution(target, t, -one.clone()));
                rivals_alone.push(contribution(term.rival, x, one.clone()));
            }
            let slot = &mut led[usize::from(kind == TermKind::Class)];
            let part = positive_part(&term.value);
            slot.0 += 1;
            slot.1 = ExactInterval {
                lower: &slot.1.lower + &part.lower,
                upper: &slot.1.upper + &part.upper,
            };
            // The leading branch's contribution.
            let target_member = leading_member(&chunk[target]);
            let leading = match (term.leading, &target_member) {
                (_, Err(refusal)) => Err(*refusal),
                (None, Ok(t)) => Ok(vec![contribution(target, t, -one.clone())]),
                (Some(x), Ok(t)) => leading_member(&chunk[x])
                    .map(|m| vec![contribution(x, m, one.clone()), contribution(target, t, -one.clone())]),
            };
            let leading = match leading {
                Ok(leading) => {
                    contributions.extend(leading.iter().cloned());
                    leading
                }
                Err(refusal) => {
                    unresolved.push(refusal);
                    continue;
                }
            };
            // Every active branch, for the first-order certificate.
            let mut branches = Vec::new();
            let mut refused = None;
            for branch in &term.branches {
                for t in &chunk[target].active {
                    let MemberCovector::Resolved { .. } = t else {
                        if let MemberCovector::Unresolved { refusal, .. } = t {
                            refused = Some(*refusal);
                        }
                        continue;
                    };
                    match branch {
                        None => branches.push(vec![contribution(target, t, -one.clone())]),
                        Some(x) => {
                            for m in &chunk[*x].active {
                                match m {
                                    MemberCovector::Resolved { .. } => branches.push(vec![
                                        contribution(*x, m, one.clone()),
                                        contribution(target, t, -one.clone()),
                                    ]),
                                    MemberCovector::Unresolved { refusal, .. } => {
                                        refused = Some(*refusal)
                                    }
                                }
                            }
                        }
                    }
                }
            }
            terms_out.push(TermBranches {
                positive: term.value.lower.is_positive(),
                branches,
                unresolved: refused,
                site: TermSite {
                    request: request_index,
                    context: contexts[*position].index,
                    station,
                    positive: term.value.lower.is_positive(),
                },
                leading,
            });
        }
    }
    Proposal {
        contributions,
        terms: terms_out,
        unresolved,
        targets: targets_alone,
        rivals: rivals_alone,
        led,
    }
}

/// [definition; agent-inferred, September 30] **The proposal's returns at the source port**
/// (module header, "The covector"). Every contribution's storage is its passage's read from its
/// station `j` (`BankPlacement::storage`): each datum, the request's phase counts and the section's
/// cells, at its transported weight `w_S` from `j` over the span its section `S` closes (the
/// storage stays linear in `E` at fixed weights, so the form of the returns is unchanged; only the
/// weights are read from the contribution's station). Every datum returns in one
/// form, one return a placement aggregated by its feature: one per phase of each request (feature
/// the phase's counts `M[c]` at the weight `Σ w_S(c)²` over the contributions, covector their
/// `w_S(c)`-weighted sum carried back through the phase's rotation `P^(c − λ)`, over that weight),
/// and one per class over the batch for the sections' placements (feature `e_x` at the weight
/// `Σ w_S(j)²`, covector their `w_S(j)`-weighted sum over it): the same gradient, unit step,
/// alignment and metric as one return a placement; each the descent covector.
fn returns(
    field: &Field,
    constitution: &Constitution,
    declared: &Refinement,
    requests: &[Request],
    contributions: &[Contribution],
) -> Result<Vec<Sample>, HnnError> {
    let ring = declared.ring();
    let geometry = field.ring(ring);
    let period = geometry.period() as usize;
    let width = geometry.width();
    let alphabet = field.alphabet();
    let mut samples = Vec::new();
    let mut section_sums = vec![vec![Rat::zero(); width]; alphabet];
    let mut section_weights = vec![Rat::zero(); alphabet];
    for (index, request) in requests.iter().enumerate() {
        let mine: Vec<&Contribution> = contributions.iter().filter(|c| c.request == index).collect();
        if mine.is_empty() {
            continue;
        }
        let placement =
            BankPlacement::of(field, constitution, &request.current, &request.moment, declared)?;
        let lift = request.current.lift()[ring].clone();
        let phase = request.current.phase(field, ring)? as usize;
        let phases: Vec<usize> = (0..period)
            .filter(|&c| {
                request
                    .moment
                    .phase_counts(ring, c)
                    .is_ok_and(|counts| counts.iter().any(|&n| n != 0))
            })
            .collect();
        let mut phase_sums = vec![vec![Rat::zero(); width]; phases.len()];
        let mut phase_weights = vec![Rat::zero(); phases.len()];
        for contribution in mine {
            let covector: Vec<Rat> = contribution.covector.iter().map(face).collect();
            let (request_weights, station_weights) =
                placement.weights(contribution.station, &contribution.cells);
            for ((sum, total), weight) in phase_sums
                .iter_mut()
                .zip(phase_weights.iter_mut())
                .zip(&request_weights)
            {
                let scale = weight * &contribution.sign;
                for (value, add) in sum.iter_mut().zip(&covector) {
                    *value += add * &scale;
                }
                *total += weight * weight;
            }
            // The section's placements: each placed station's class at its phase and weight.
            for (station, (cell, weight)) in
                contribution.cells.iter().zip(&station_weights).enumerate()
            {
                let (Some(class), Some(weight)) = (cell, weight) else { continue };
                let at = (phase + 1 + station) % period;
                let rotated = geometry.rotate(&covector, &(BigInt::from(at) - &lift));
                for (sum, value) in section_sums[*class].iter_mut().zip(&rotated) {
                    *sum += value * weight * &contribution.sign;
                }
                section_weights[*class] += weight * weight;
            }
        }
        for ((c, sum), weight) in phases.iter().zip(phase_sums).zip(phase_weights) {
            if !weight.is_positive() || sum.iter().all(Zero::is_zero) {
                continue;
            }
            let feature = request
                .moment
                .phase_counts(ring, *c)?
                .iter()
                .map(|&count| Rat::from_integer(BigInt::from(count)))
                .collect();
            let rotated = geometry.rotate(&sum, &(BigInt::from(*c as u64) - &lift));
            samples.push(Sample {
                covector: rotated.into_iter().map(|x| -(x / &weight)).collect(),
                weight,
                feature,
            });
        }
    }
    for class in 0..alphabet {
        if !section_weights[class].is_positive() {
            continue;
        }
        let weight = section_weights[class].clone();
        let mut feature = vec![Rat::zero(); alphabet];
        feature[class] = Rat::one();
        samples.push(Sample {
            covector: section_sums[class].iter().map(|x| -(x / &weight)).collect(),
            weight,
            feature,
        });
    }
    Ok(samples)
}

/// [definition; agent-inferred, September 30] **The modulus's normal reading** (module header,
/// "The committed move"): the proposal's slope in the transport modulus
/// `γ_ρ = Σ_c sign_c ⟨ĝ_c, ∂z_c/∂ρ⟩` (each leading branch's storage covector at its dyadic face
/// paired with its storage's exact derivative, `BankPlacement::modulus_derivative`: the first-order
/// change of the compared terms per unit of `ρ`) and its storage curvature
/// `G_ρ = Σ_c |∂z_c/∂ρ|²` over the proposal's contributions, each storage read from its
/// contribution's station; the least-squares unit move is `−γ_ρ/G_ρ` (Lean
/// `HNN/ExecutedComparison.modulus_least_squares`).
fn modulus_normal(
    field: &Field,
    constitution: &Constitution,
    declared: &Refinement,
    requests: &[Request],
    contributions: &[Contribution],
) -> Result<(Rat, Rat), HnnError> {
    use rayon::prelude::*;
    let placements: Vec<BankPlacement> = requests
        .iter()
        .map(|r| BankPlacement::of(field, constitution, &r.current, &r.moment, declared))
        .collect::<Result<_, _>>()?;
    Ok(contributions
        .par_iter()
        .map(|c| {
            let derivative = placements[c.request].modulus_derivative(c.station, &c.cells);
            let paired: Rat = c
                .covector
                .iter()
                .map(face)
                .zip(&derivative)
                .map(|(g, d)| g * d)
                .sum();
            let energy: Rat = derivative.iter().map(|d| d * d).sum();
            (paired * &c.sign, energy)
        })
        .reduce(
            || (Rat::zero(), Rat::zero()),
            |(a, b), (c, d)| (a + c, b + d),
        ))
}

/// Each contribution's `sign ⟨ĝ, ∂z/∂ρ⟩` ([`modulus_normal`]'s slope, term by term).
fn modulus_pairings(
    field: &Field,
    constitution: &impl ConstitutionRead,
    declared: &Refinement,
    requests: &[Request],
    contributions: &[Contribution],
) -> Result<Vec<Rat>, HnnError> {
    use rayon::prelude::*;
    let placements: Vec<BankPlacement> = requests
        .iter()
        .map(|r| BankPlacement::of(field, constitution, &r.current, &r.moment, declared))
        .collect::<Result<_, _>>()?;
    Ok(contributions
        .par_iter()
        .map(|c| {
            let derivative = placements[c.request].modulus_derivative(c.station, &c.cells);
            let paired: Rat = c
                .covector
                .iter()
                .map(face)
                .zip(&derivative)
                .map(|(g, d)| g * d)
                .sum();
            paired * &c.sign
        })
        .collect())
}

/// [measured-diagnostic; agent-inferred, September 30] **The proposal's modulus slope split by
/// term kind** ([`SlopeSplit`]).
fn slope_split(
    field: &Field,
    constitution: &impl ConstitutionRead,
    declared: &Refinement,
    requests: &[Request],
    proposal: &Proposal,
) -> Result<SlopeSplit, HnnError> {
    let led = modulus_pairings(field, constitution, declared, requests, &proposal.contributions)?;
    let (mut led_threshold, mut led_class) = (Rat::zero(), Rat::zero());
    for (c, value) in proposal.contributions.iter().zip(led) {
        match c.kind {
            TermKind::Threshold => led_threshold += value,
            TermKind::Class => led_class += value,
        }
    }
    let sum = |list: &[Contribution]| -> Result<Rat, HnnError> {
        Ok(modulus_pairings(field, constitution, declared, requests, list)?
            .into_iter()
            .sum())
    };
    Ok(SlopeSplit {
        threshold_led: proposal.led[0].0,
        class_led: proposal.led[1].0,
        threshold_value: proposal.led[0].1.clone(),
        class_value: proposal.led[1].1.clone(),
        led_threshold,
        led_class,
        target: sum(&proposal.targets)?,
        rival: sum(&proposal.rivals)?,
    })
}

/// [measured-diagnostic; agent-inferred, September 30] **The modulus's slope split by term kind at
/// a constitution** ([`SlopeSplit`]; the station-framed placement's record §7), with the batch's
/// comparison: the requests read with every candidate's covector in their contexts, the proposal
/// formed as [`executed_move`] forms it, and no move made.
pub fn modulus_slopes(
    field: &Field,
    constitution: &impl ConstitutionRead,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
) -> Result<(BatchComparison, SlopeSplit), HnnError> {
    use rayon::prelude::*;
    let alphabet = field.alphabet();
    let read = |amplitudes: &[crate::ratio::GaussianRat]| bank.read_turn_covector(amplitudes, grain);
    #[allow(clippy::type_complexity)]
    let joined: Vec<(RequestComparison, (Vec<ContextRead<TurnCovector>>, Vec<(usize, usize, Term)>))> =
        requests
            .par_iter()
            .map(|request| {
                let (generation, contexts) =
                    read_contexts(field, constitution, request, declared, bank, grain, &read)?;
                let (comparison, terms) =
                    compare_request(request, generation, &contexts, alphabet)?;
                Ok((comparison, (contexts, terms)))
            })
            .collect::<Result<_, HnnError>>()?;
    let (mut compared, mut read_all) = (Vec::new(), Vec::new());
    let (mut value, mut readings) = (ExactInterval::point(Rat::zero()), 0);
    for (comparison, read) in joined {
        value = ExactInterval {
            lower: &value.lower + &comparison.value.lower,
            upper: &value.upper + &comparison.value.upper,
        };
        readings += comparison.readings;
        compared.push(comparison);
        read_all.push(read);
    }
    let proposal = propose(requests, &read_all, alphabet);
    let split = slope_split(field, constitution, declared, requests, &proposal)?;
    Ok((
        BatchComparison {
            requests: compared,
            value,
            readings,
        },
        split,
    ))
}

/// **The proposal's contributions and returns at `E`** (the owner's pullback test): each
/// contribution's request, section, dyadic face of its storage covector and sign, and the returns
/// [`returns`] carries to the source port.
#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(crate) fn proposal_returns(
    field: &Field,
    constitution: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
) -> Result<(Vec<Sample>, Vec<(usize, usize, Vec<Option<usize>>, Vec<Rat>, Rat)>), HnnError> {
    let read = |amplitudes: &[crate::ratio::GaussianRat]| bank.read_turn_covector(amplitudes, grain);
    let mut read_all = Vec::new();
    for request in requests {
        let (_, contexts) = read_contexts(field, constitution, request, declared, bank, grain, &read)?;
        let (_, terms) = compare_request(request, None, &contexts, field.alphabet())?;
        read_all.push((contexts, terms));
    }
    let proposal = propose(requests, &read_all, field.alphabet());
    let samples = returns(field, constitution, declared, requests, &proposal.contributions)?;
    Ok((
        samples,
        proposal
            .contributions
            .iter()
            .map(|c| {
                (
                    c.request,
                    c.station,
                    c.cells.clone(),
                    c.covector.iter().map(face).collect(),
                    c.sign.clone(),
                )
            })
            .collect(),
    ))
}

/// The storage moves of every contribution's section from a constitution to a carried successor,
/// each read from its station: the successor's storage less the constitution's, exactly (the
/// storage is linear in `E` at fixed weights, so at a fixed modulus this is the move `ΔE`'s
/// placement; a move of the modulus moves every weight).
fn storage_moves(
    field: &Field,
    constitution: &Constitution,
    successor: &Constitution,
    declared: &Refinement,
    requests: &[Request],
    sections: &[(usize, usize, Vec<Option<usize>>)],
) -> Result<Vec<Vec<Rat>>, HnnError> {
    use rayon::prelude::*;
    let placements = |theta: &Constitution| -> Result<Vec<BankPlacement>, HnnError> {
        requests
            .iter()
            .map(|r| BankPlacement::of(field, theta, &r.current, &r.moment, declared))
            .collect()
    };
    let (before, after) = (placements(constitution)?, placements(successor)?);
    Ok(sections
        .par_iter()
        .map(|(request, station, cells)| {
            let (old, new) = (
                before[*request].storage(*station, cells),
                after[*request].storage(*station, cells),
            );
            new.iter().zip(&old).map(|(n, o)| n - o).collect()
        })
        .collect())
}

/// [definition; agent-inferred, September 30] **A carried move's first-order reading**: the
/// certificate `Σ_terms sup_(α active) Df_α[Δ]` enclosed (its upper end is the commit guard) and
/// the terms whose active branches were not all resolved; and, as receipts only (the
/// [two counts' pin](../../../../research/records/2026-09-30_THE_TWO_COUNTS_PINNED_BEFORE_ITS_RUNS.md)
/// §5, D1 and D2; the move never reads them), each term's bound in the proposal's order (`None` for
/// a term with no resolved branch; a straddling term's hinged at zero), aligned with
/// [`ExecutedMove::sites`], and the leading branches' pairing `Σ_lead sign ⟨ĝ, Δz⟩`, the proposal's
/// own gradient on the carried move (`None` for a declared comparison without branches).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FirstOrderReading {
    pub bound: ExactInterval,
    pub unresolved: usize,
    pub terms: Vec<Option<ExactInterval>>,
    pub leading: Option<ExactInterval>,
}

/// A contribution's signed pairing `sign ⟨ĝ, Δz⟩`, enclosed, with its storage move.
fn signed_pairing(c: &Contribution, moved: &[Rat]) -> ExactInterval {
    let d = paired(&c.covector, moved);
    let (a, b) = (&d.lower * &c.sign, &d.upper * &c.sign);
    ExactInterval {
        lower: a.clone().min(b.clone()),
        upper: a.max(b),
    }
}

/// [definition; agent-inferred, September 30] **The first-order certificate of a carried move**
/// (module header): `Σ_terms sup_(α active) Df_α[Δ]`, each branch's covector enclosures paired with
/// its candidates' exact storage moves to the carried successor, a term straddling zero bounded by
/// `max(0, ·)`; the enclosure of the sum's bound (its upper end is the certificate), and the terms
/// whose active branches were not all resolved ([`FirstOrderReading`], with its receipts).
fn first_order(
    field: &Field,
    constitution: &Constitution,
    declared: &Refinement,
    requests: &[Request],
    proposal: &Proposal,
    successor: &Constitution,
) -> Result<FirstOrderReading, HnnError> {
    let mut sections: Vec<(usize, usize, Vec<Option<usize>>)> = Vec::new();
    for term in &proposal.terms {
        for branch in &term.branches {
            for c in branch {
                sections.push((c.request, c.station, c.cells.clone()));
            }
        }
    }
    // The leading branches' sections, after every branch's (a receipt: the proposal's own gradient
    // paired with the same exact storage moves).
    let leading_start = sections.len();
    for term in &proposal.terms {
        for c in &term.leading {
            sections.push((c.request, c.station, c.cells.clone()));
        }
    }
    let moves = storage_moves(field, constitution, successor, declared, requests, &sections)?;
    let mut cursor = 0;
    let mut total = ExactInterval::point(Rat::zero());
    let mut unresolved = 0;
    let mut terms = Vec::with_capacity(proposal.terms.len());
    for term in &proposal.terms {
        unresolved += usize::from(term.unresolved.is_some());
        let mut bound: Option<ExactInterval> = None;
        for branch in &term.branches {
            let mut derivative = ExactInterval::point(Rat::zero());
            for c in branch {
                let d = signed_pairing(c, &moves[cursor]);
                cursor += 1;
                derivative = ExactInterval {
                    lower: &derivative.lower + &d.lower,
                    upper: &derivative.upper + &d.upper,
                };
            }
            bound = Some(match bound {
                None => derivative,
                Some(b) => ExactInterval {
                    lower: b.lower.max(derivative.lower),
                    upper: b.upper.max(derivative.upper),
                },
            });
        }
        let Some(mut bound) = bound else {
            terms.push(None);
            continue;
        };
        if !term.positive {
            bound = positive_part(&bound);
        }
        total = ExactInterval {
            lower: &total.lower + &bound.lower,
            upper: &total.upper + &bound.upper,
        };
        terms.push(Some(bound));
    }
    let mut leading = ExactInterval::point(Rat::zero());
    let mut cursor = leading_start;
    for term in &proposal.terms {
        for c in &term.leading {
            let d = signed_pairing(c, &moves[cursor]);
            cursor += 1;
            leading = ExactInterval {
                lower: &leading.lower + &d.lower,
                upper: &leading.upper + &d.upper,
            };
        }
    }
    Ok(FirstOrderReading {
        bound: total,
        unresolved,
        terms,
        leading: Some(leading),
    })
}

/// [definition; agent-inferred, September 30] **Why a trial step is not adopted** (module header,
/// "The committed move"): each a commit guard.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TrialRefusal {
    /// An entry of `E` past [`entry_bound`].
    EntryBound(Rat),
    /// A candidate crossing past its signed form (the re-read refused).
    Admission,
    /// A lock's Floquet certificate refused (the release refused).
    Floquet,
    /// The first-order descent not certified on the carried move.
    FirstOrder(ExactInterval),
    /// `F` not strictly lower by disjoint enclosures.
    NotBelow(ExactInterval),
    /// The constitution's own guard (budget, storage growth).
    Constitution(String),
}

/// [definition; agent-inferred, September 30] **One trial of the committed move**: its step, the
/// carried move's largest entry change and the successor's largest entry, the first-order bound on
/// the carried move, the successor's declared comparison and its release comparison where they
/// were read, and its refusal, if any.
///
/// Receipts only (the move never reads them; the two counts' pin §5): `terms`, each term's
/// first-order bound on the carried move aligned with [`ExecutedMove::sites`], `leading`, the
/// leading branches' pairing on it, and `source`, the carried source step's reading
/// ([`SourceStep`]: the entries whose lattice coordinate moved, the released residuals), where
/// the trial reached them.
#[derive(Clone, Debug)]
pub struct Trial {
    pub step: Rat,
    pub modulus: Option<Rat>,
    pub moved: Rat,
    pub largest: Rat,
    pub first_order: Option<ExactInterval>,
    pub value: Option<ExactInterval>,
    pub after: Option<BatchComparison>,
    pub refusal: Option<TrialRefusal>,
    pub terms: Option<Vec<Option<ExactInterval>>>,
    pub leading: Option<ExactInterval>,
    pub source: Option<SourceStep>,
}

/// [definition; agent-inferred, September 30] **Why the move was refused as a whole**.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MoveRefusal {
    /// Every term already holds: nothing to descend.
    Nothing,
    /// The proposal's returns reached nothing.
    Unreached,
    /// The unit step's first-order slope is not certified negative.
    NoDescent(ExactInterval),
    /// Every trial step failed a guard, down to a move below the lattice.
    Guards,
}

/// [definition; agent-inferred, September 30] **The committed move's receipt**: the comparison
/// before, the proposal's size (contributions, returns, terms with branches, unresolved leading
/// branches), the unit step's first-order slope, every trial, and the adopted successor with its
/// carried step's reading, or the move's refusal.
#[derive(Clone, Debug)]
pub struct ExecutedMove {
    pub before: BatchComparison,
    pub contributions: usize,
    pub returns: usize,
    pub terms: usize,
    pub unresolved: Vec<CovectorRefusal>,
    pub unresolved_branches: usize,
    pub slope: Option<ExactInterval>,
    pub modulus_slope: Option<Rat>,
    /// The modulus's storage curvature `G_ρ = Σ_c |∂z_c/∂ρ|²` and its least-squares unit move
    /// `−γ_ρ/G_ρ` (zero upward at `ρ = 1`), where the modulus was read.
    pub modulus_curvature: Option<Rat>,
    pub modulus_unit: Option<Rat>,
    /// The modulus's slope split by term kind ([`SlopeSplit`]), where the modulus was read.
    pub split: Option<SlopeSplit>,
    pub trials: Vec<Trial>,
    pub adopted: Option<(Constitution, SourceStep)>,
    pub refusal: Option<MoveRefusal>,
    /// Receipts only (the two counts' pin §5): each term of the proposal's site, in the order of
    /// every trial's `terms`, and the unit move's largest entry change (the ladder's entry scale
    /// reads `½` over it).
    pub sites: Vec<TermSite>,
    pub unit_largest: Option<Rat>,
}

/// The source port's largest absolute entry.
fn largest_entry(matrix: &ExactRatMatrix) -> Rat {
    matrix
        .entries()
        .iter()
        .map(|x| x.abs())
        .max()
        .unwrap_or_else(Rat::zero)
}

/// [definition; agent-inferred, September 30] **What a declared comparison reads at a carried
/// successor**: its value enclosed, the release's comparison where it was read, and the guard that
/// refused it (admission, Floquet), if one did.
pub struct Reread {
    pub value: ExactInterval,
    pub comparison: Option<BatchComparison>,
    pub refusal: Option<TrialRefusal>,
}

/// [definition; agent-inferred, September 30] **The ladder's depth**: at most 8 trial steps a move,
/// from the first-order zero of the comparison down to `2^(−7)` of it. Every trial re-reads the whole
/// batch from the open section, so the depth bounds a move's work; a comparison that does not fall
/// within `2^(−7)` of its first-order zero along the proposal is refused there (typed), never
/// searched further. One depth for every declared comparison.
const LADDER_DEPTH: usize = 8;

/// The ladder's outcome: every trial, the adopted successor with its carried step, or the refusal.
type LadderOutcome = (Vec<Trial>, Option<(Constitution, SourceStep)>, Option<MoveRefusal>);

/// A carried move's first-order certificate: from the source port's move and the carried successor.
type FirstOrder<'a> =
    dyn Fn(&ExactRatMatrix, &Constitution) -> Result<FirstOrderReading, HnnError> + Sync + 'a;

/// [definition; agent-inferred, September 30] **The certified step's ladder, one law for every
/// declared comparison** (module header, "The committed move"): from the first-order zero of the
/// comparison (`F⁻ / (−slope)`, never past it), held so that no entry of `E` moves by more than the
/// founding's entry scale `½` in one move, halving until the carried move moves no lattice
/// coordinate; each carried successor adopted only when every commit guard holds on it: the entry
/// bound, the first-order certificate on the carried move (`first`, negative), the successor's
/// guards and value (`reread`), and a strict decrease by disjoint enclosures.
#[allow(clippy::too_many_arguments)]
fn ladder(
    constitution: &Constitution,
    ring: usize,
    samples: &[Sample],
    before: &ExactInterval,
    slope: &ExactInterval,
    unit_largest: &Rat,
    transport: Option<&Rat>,
    first: &FirstOrder<'_>,
    reread: &(dyn Fn(&Constitution) -> Result<Reread, HnnError> + Sync),
) -> Result<LadderOutcome, HnnError> {
    let source = constitution
        .source_port(ring)
        .ok_or(HnnError::MissingSourcePort { ring })?
        .clone();
    let polyak = &before.lower / -slope.upper.clone();
    let scale_cap = if unit_largest.is_positive() {
        Rat::new(BigInt::one(), BigInt::from(2)) / unit_largest
    } else {
        Rat::one()
    };
    let mut step = power_below(&polyak.min(scale_cap).max(Rat::zero()));
    let lattice_unit = constitution
        .lattice(crate::hnn::constitution::Locus::SourcePort(ring))?
        .unit();
    let two = Rat::from_integer(BigInt::from(2));
    let mut trials = Vec::new();
    loop {
        if step.is_zero()
            || &step * unit_largest * &two < lattice_unit
            || trials.len() >= LADDER_DEPTH
        {
            return Ok((trials, None, Some(MoveRefusal::Guards)));
        }
        let mut trial = Trial {
            step: step.clone(),
            modulus: None,
            moved: Rat::zero(),
            largest: Rat::zero(),
            first_order: None,
            value: None,
            after: None,
            refusal: None,
            terms: None,
            leading: None,
            source: None,
        };
        let stepped = match constitution.stepped_source(ring, samples, &step) {
            Ok(Some(stepped)) => stepped,
            Ok(None) => return Ok((trials, None, Some(MoveRefusal::Unreached))),
            Err(error @ (HnnError::ConstitutionBudget { .. } | HnnError::UncertifiedStorage)) => {
                trial.refusal = Some(TrialRefusal::Constitution(error.to_string()));
                trials.push(trial);
                step /= &two;
                continue;
            }
            Err(error) => return Err(error),
        };
        let (successor, reading) = stepped;
        trial.source = Some(reading.clone());
        // The transport modulus's part of the move (module header, "The committed move"): `ρ + ηΔρ`
        // held within `[ρ/2, 1]` (passive) and read on the source port's lattice, nearest.
        let (successor, modulus_moved) = match transport {
            Some(unit) if !unit.is_zero() => {
                let modulus = constitution.transport(ring);
                let target = (&modulus + &step * unit)
                    .max(&modulus / &two)
                    .min(Rat::one());
                let carried = ((&target / &lattice_unit)
                    + Rat::new(BigInt::one(), BigInt::from(2)))
                .floor()
                    * &lattice_unit;
                let carried = carried.min(Rat::one()).max(lattice_unit.clone());
                trial.modulus = Some(carried.clone());
                let moved_modulus = carried != modulus;
                (successor.with_transport(ring, carried)?, moved_modulus)
            }
            _ => (successor, false),
        };
        let moved = successor
            .source_port(ring)
            .ok_or(HnnError::MissingSourcePort { ring })?
            .subtract(&source)?;
        trial.moved = largest_entry(&moved);
        trial.largest = reading.largest.clone();
        if trial.moved.is_zero() && !modulus_moved {
            return Ok((trials, None, Some(MoveRefusal::Guards)));
        }
        if reading.largest > entry_bound() {
            trial.refusal = Some(TrialRefusal::EntryBound(reading.largest.clone()));
            trials.push(trial);
            step /= &two;
            continue;
        }
        let first_reading = first(&moved, &successor)?;
        let bound = first_reading.bound;
        trial.terms = Some(first_reading.terms);
        trial.leading = first_reading.leading;
        trial.first_order = Some(bound.clone());
        if !bound.upper.is_negative() {
            trial.refusal = Some(TrialRefusal::FirstOrder(bound));
            trials.push(trial);
            step /= &two;
            continue;
        }
        let read = reread(&successor)?;
        trial.value = Some(read.value.clone());
        trial.after = read.comparison;
        trial.refusal = match read.refusal {
            Some(refusal) => Some(refusal),
            None if read.value.upper < before.lower => None,
            None => Some(TrialRefusal::NotBelow(read.value.clone())),
        };
        let adopted = trial.refusal.is_none();
        trials.push(trial);
        if adopted {
            return Ok((trials, Some((successor, reading)), None));
        }
        step /= &two;
    }
}

/// The successor's release comparison as a reread: an inadmissible crossing and a refused lock
/// certificate are its guards.
fn executed_reread(
    field: &Field,
    successor: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
) -> Result<Reread, HnnError> {
    match compare(field, successor, requests, declared, bank, grain) {
        Ok(after) => {
            let floquet = after
                .requests
                .iter()
                .any(|r| r.generation.as_ref().is_some_and(|g| g.uncertified.is_some()));
            Ok(Reread {
                value: after.value.clone(),
                comparison: Some(after),
                refusal: floquet.then_some(TrialRefusal::Floquet),
            })
        }
        Err(HnnError::UncertifiedResonator { .. }) => Ok(Reread {
            value: ExactInterval::point(Rat::zero()),
            comparison: None,
            refusal: Some(TrialRefusal::Admission),
        }),
        Err(error) => Err(error),
    }
}

/// **The committed move of `E` on the release's own comparison** (module header, "The committed
/// move"): the batch read at `E` with every candidate's covector, the proposal and its returns, the
/// unit step's first-order slope, then the certified step's ladder ([`ladder`]), each carried
/// successor re-read from the open section and adopted only when every commit guard holds.
pub fn executed_move(
    field: &Field,
    constitution: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
) -> Result<ExecutedMove, HnnError> {
    use rayon::prelude::*;
    let ring = declared.ring();
    let alphabet = field.alphabet();
    let read = |amplitudes: &[crate::ratio::GaussianRat]| bank.read_turn_covector(amplitudes, grain);
    // The requests are co-present regions (the shared constitution at its cut, one reading each).
    #[allow(clippy::type_complexity)]
    let joined: Vec<(RequestComparison, (Vec<ContextRead<TurnCovector>>, Vec<(usize, usize, Term)>))> =
        requests
            .par_iter()
            .map(|request| {
                let (generation, contexts) =
                    read_contexts(field, constitution, request, declared, bank, grain, &read)?;
                let (comparison, terms) =
                    compare_request(request, generation, &contexts, alphabet)?;
                Ok((comparison, (contexts, terms)))
            })
            .collect::<Result<_, HnnError>>()?;
    let mut read_all = Vec::with_capacity(requests.len());
    let mut compared = Vec::with_capacity(requests.len());
    let mut value = ExactInterval::point(Rat::zero());
    let mut readings = 0;
    for (comparison, read) in joined {
        value = ExactInterval {
            lower: &value.lower + &comparison.value.lower,
            upper: &value.upper + &comparison.value.upper,
        };
        readings += comparison.readings;
        compared.push(comparison);
        read_all.push(read);
    }
    let before = BatchComparison {
        requests: compared,
        value,
        readings,
    };
    let proposal = propose(requests, &read_all, alphabet);
    let mut receipt = ExecutedMove {
        before: before.clone(),
        contributions: proposal.contributions.len(),
        returns: 0,
        terms: proposal.terms.len(),
        unresolved: proposal.unresolved.clone(),
        unresolved_branches: proposal
            .terms
            .iter()
            .filter(|t| t.unresolved.is_some())
            .count(),
        slope: None,
        modulus_slope: None,
        modulus_curvature: None,
        modulus_unit: None,
        split: None,
        trials: Vec::new(),
        adopted: None,
        refusal: None,
        sites: proposal.terms.iter().map(|t| t.site).collect(),
        unit_largest: None,
    };
    if proposal.contributions.is_empty() {
        receipt.refusal = Some(MoveRefusal::Nothing);
        return Ok(receipt);
    }
    let samples = returns(field, constitution, declared, requests, &proposal.contributions)?;
    receipt.returns = samples.len();
    let source = constitution
        .source_port(ring)
        .ok_or(HnnError::MissingSourcePort { ring })?
        .clone();
    let Some((unit, _)) = constitution.stepped_source(ring, &samples, &Rat::one())? else {
        receipt.refusal = Some(MoveRefusal::Unreached);
        return Ok(receipt);
    };
    let unit_move = unit
        .source_port(ring)
        .ok_or(HnnError::MissingSourcePort { ring })?
        .subtract(&source)?;
    let slope = first_order(field, constitution, declared, requests, &proposal, &unit)?.bound;
    receipt.unit_largest = Some(largest_entry(&unit_move));
    receipt.slope = Some(slope.clone());
    if !slope.upper.is_negative() {
        receipt.refusal = Some(MoveRefusal::NoDescent(slope));
        return Ok(receipt);
    }
    // The transport modulus's unit move (module header, "The committed move"): the least-squares
    // fit of its storage moves to the proposal's descent covectors, `Δρ = −γ_ρ / Σ_c |∂z_c/∂ρ|²`,
    // the port's normal-law principle on the modulus's one feature; none where it would leave
    // `(0, 1]` at `ρ = 1`.
    let (gamma, curvature) =
        modulus_normal(field, constitution, declared, requests, &proposal.contributions)?;
    receipt.modulus_slope = Some(gamma.clone());
    receipt.modulus_curvature = Some(curvature.clone());
    receipt.split = Some(slope_split(field, constitution, declared, requests, &proposal)?);
    let modulus_unit = if gamma.is_zero() || !curvature.is_positive() {
        Rat::zero()
    } else {
        let unit = -&gamma / &curvature;
        if unit.is_positive() && constitution.transport(ring).is_one() {
            Rat::zero()
        } else {
            unit
        }
    };
    receipt.modulus_unit = Some(modulus_unit.clone());
    // The joint unit move's first order: the port's bound and the modulus's `γ_ρ Δρ = −γ_ρ²/G`.
    let share = &gamma * &modulus_unit;
    let joint = ExactInterval {
        lower: &slope.lower + &share,
        upper: &slope.upper + &share,
    };
    let first = |_: &ExactRatMatrix, successor: &Constitution| {
        first_order(field, constitution, declared, requests, &proposal, successor)
    };
    let reread = |successor: &Constitution| {
        executed_reread(field, successor, requests, declared, bank, grain)
    };
    let (trials, adopted, refusal) = ladder(
        constitution,
        ring,
        &samples,
        &before.value,
        &joint,
        &largest_entry(&unit_move),
        Some(&modulus_unit),
        &first,
        &reread,
    )?;
    receipt.trials = trials;
    receipt.adopted = adopted;
    receipt.refusal = refusal;
    Ok(receipt)
}

/// The largest power of two at or below `x > 0`; zero at zero.
fn power_below(x: &Rat) -> Rat {
    if !x.is_positive() {
        return Rat::zero();
    }
    let e = crate::ratio::disk::floor_log2(x);
    if e >= 0 {
        Rat::from_integer(BigInt::one() << e as usize)
    } else {
        Rat::new(BigInt::one(), BigInt::one() << (-e) as usize)
    }
}

/// [definition; agent-inferred, September 30] **A carried move's pairing receipt** (the move's
/// requirement 3): for a candidate storage read at `E` and at the successor with the same section,
/// its member's `ln ρ` change enclosed exactly, and the covector paired with the exact storage move.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairingReading {
    pub request: usize,
    pub station: usize,
    pub cells: Vec<Option<usize>>,
    pub member: usize,
    pub actual: ExactInterval,
    pub predicted: ExactInterval,
}

/// **The pairing receipt of an adopted move** on the leading contributions of its first `count`
/// terms: each candidate's leading member read at `E` and at the successor on the same section, the
/// exact change of `ln ρ_m` against the covector paired with the carried storage move.
#[allow(clippy::too_many_arguments)]
pub fn pairing_receipt(
    field: &Field,
    before: &Constitution,
    after: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    count: usize,
) -> Result<Vec<PairingReading>, HnnError> {
    let alphabet = field.alphabet();
    let read = |amplitudes: &[crate::ratio::GaussianRat]| bank.read_turn_covector(amplitudes, grain);
    let mut read_all = Vec::new();
    for request in requests {
        let (_, contexts) = read_contexts(field, before, request, declared, bank, grain, &read)?;
        let (_, terms) = compare_request(request, None, &contexts, alphabet)?;
        read_all.push((contexts, terms));
    }
    let proposal = propose(requests, &read_all, alphabet);
    let chosen: Vec<&Contribution> = proposal.contributions.iter().take(2 * count).collect();
    let sections: Vec<(usize, usize, Vec<Option<usize>>)> =
        chosen.iter().map(|c| (c.request, c.station, c.cells.clone())).collect();
    let moves = storage_moves(field, before, after, declared, requests, &sections)?;
    let mut out = Vec::new();
    for (contribution, storage_move) in chosen.iter().zip(&moves) {
        let request = &requests[contribution.request];
        let at = |constitution: &Constitution| -> Result<TurnCovector, HnnError> {
            let placement =
                BankPlacement::of(field, constitution, &request.current, &request.moment, declared)?;
            bank.read_turn_covector(
                &crate::hnn::ring::turn(
                    &placement.storage(contribution.station, &contribution.cells),
                ),
                grain,
            )
        };
        let (old, new) = (at(before)?, at(after)?);
        let Ok(MemberCovector::Resolved { member, .. }) = leading_member(&old).cloned() else {
            continue;
        };
        let (a, b) = (ln_of(&old.reading.members[member])?, ln_of(&new.reading.members[member])?);
        out.push(PairingReading {
            request: contribution.request,
            station: contribution.station,
            cells: contribution.cells.clone(),
            member,
            actual: ExactInterval {
                lower: &b.lower - &a.upper,
                upper: &b.upper - &a.lower,
            },
            predicted: paired(&contribution.covector, storage_move),
        });
    }
    Ok(out)
}
