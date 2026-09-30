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
//! **The comparison.** For a request with locked partial section `S`, every open station `j` and
//! class `x`, the actual storage is
//! `z_(S,j,x) = z_request + ν̂(|S| + 1)(Σ_(k∈S) P^(r_k) E e_(S_k) + P^(r_j) E e_x)`
//! (`BankPlacement::storage`), and the reading is `a_(j,x) = max_m ρ(M_m(z))` with exact enclosure
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
//! on the returns and carries `ηD` onto its lattice (`Constitution::stepped_source`). `η` starts at
//! the first-order zero of `F` (`F⁻ / (−slope)`, never past it) held below the founding's entry
//! scale, and halves until the carried move moves no lattice coordinate. Each carried successor is
//! **re-read from the open section** (every context re-run: a changed branch or lock order is read,
//! never assumed) and adopted only when every commit guard holds on it:
//! - the entry bound, every entry of `E` at most [`ENTRY_BOUND`];
//! - every candidate crossing of every re-read refinement admissible (the signed form);
//! - every lock's Floquet certificate certified (a refused one refuses the release);
//! - the first-order descent certified on the carried move;
//! - `F` strictly lower by disjoint exact enclosures, `F(E′)⁺ < F(E)⁻`;
//! - the constitution's own guards (lattice, bit budget, committed storage growth).
//!
//! Otherwise the next step is tried, at most `LADDER_DEPTH` a move, and the move is refused,
//! typed, when none holds. **One ladder for every declared comparison**: the bank's face on the
//! same contexts moves by the same ladder and guards ([`face_move`], the matched control; its code
//! `Σ −log₂ θ_t` in place of `F`, its returns' exact pairing as its first order). The operands
//! are transient; nothing of the comparison is retained: the successor's `E` and its normal law's
//! statistic are the only change.
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
use crate::hnn::moment::PairPort;
use crate::hnn::moment::{PopulationChart, SourceMoment};
use crate::hnn::prediction::{
    BankGeneration, BankPlacement, BankRefinement, JointGrowth, Refinement, bank_release,
};
use crate::hnn::ring::{
    CovectorRefusal, Growth, MemberCovector, ReceivingBank, ResonatorMaterial, TurnCovector,
    TurnReading,
};
use crate::holon::deposition::significant;
use crate::ratio::algebraic::{ExactInterval, ln_enclosure};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::Rat;
use crate::compression::landmark::context::Landmarks;
use crate::receiver::population::PortPopulation;

/// [definition; agent-inferred, September 30] **The entry bound** `2³`: every entry of `E` at most
/// three binary orders above the founding's unit scale (the certified step's pins, acceptance 1;
/// every development read stayed below 2, the divergence it guards against passed 316). A commit
/// guard here, never a tally.
pub fn entry_bound() -> Rat {
    Rat::from_integer(BigInt::from(8))
}

/// Alias read by the module header.
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
                    read(&crate::hnn::ring::turn(&placement.storage(&cells)))
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

/// A constitution read with its source port replaced (a direction's placement: the storage is
/// linear in `E`, so the placement of a move `ΔE` is the storages' move).
struct SourceMove<'a, C: ConstitutionRead> {
    base: &'a C,
    ring: usize,
    source: ExactRatMatrix,
}

impl<C: ConstitutionRead> ConstitutionRead for SourceMove<'_, C> {
    fn standing(&self, ring: usize) -> &[Rat] {
        self.base.standing(ring)
    }
    fn passive_factor(&self, ring: usize) -> &ExactRatMatrix {
        self.base.passive_factor(ring)
    }
    fn contrast_port(&self, ring: usize) -> &ExactRatMatrix {
        self.base.contrast_port(ring)
    }
    fn slices(&self, ring: usize) -> &[(Vec<Rat>, Vec<Rat>)] {
        self.base.slices(ring)
    }
    fn source_port(&self, ring: usize) -> Option<&ExactRatMatrix> {
        if ring == self.ring {
            Some(&self.source)
        } else {
            self.base.source_port(ring)
        }
    }
    fn pair_port(&self, ring: usize, offset: usize) -> Option<&PairPort> {
        self.base.pair_port(ring, offset)
    }
    fn contact_storage(&self, contact: usize) -> &ExactRatMatrix {
        self.base.contact_storage(contact)
    }
    fn contact_stiffness(&self, contact: usize) -> &ExactRatMatrix {
        self.base.contact_stiffness(contact)
    }
    fn contact_dissipation(&self, contact: usize) -> &ExactRatMatrix {
        self.base.contact_dissipation(contact)
    }
    fn receiving_map(&self, ring: usize) -> Option<&ExactRatMatrix> {
        self.base.receiving_map(ring)
    }
    fn landmarks(&self, ring: usize) -> Option<&Landmarks> {
        self.base.landmarks(ring)
    }
    fn population(&self, ring: usize) -> Option<&PortPopulation> {
        self.base.population(ring)
    }
    fn contact_stiffness_signature(&self, contact: usize) -> Option<&[bool]> {
        self.base.contact_stiffness_signature(contact)
    }
    fn contact_surface_storage(&self, contact: usize) -> Option<&Rat> {
        self.base.contact_surface_storage(contact)
    }
    fn ring_resonator(&self, ring: usize) -> Option<&ResonatorMaterial> {
        self.base.ring_resonator(ring)
    }
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
/// section the candidate's storage was read at, its member's storage covector (enclosed) and the
/// term's sign on it (`+1` a rival, `−1` the target).
#[derive(Clone, Debug)]
struct Contribution {
    request: usize,
    cells: Vec<Option<usize>>,
    covector: Vec<ExactInterval>,
    sign: Rat,
}

/// [definition; agent-inferred, September 30] **A term's branches for the first-order
/// certificate**: every active rival/threshold branch crossed with the active members of the two
/// candidates it compares, each its storage covectors and sections; and whether the term is
/// positive (else it straddles zero).
#[derive(Clone, Debug)]
struct TermBranches {
    positive: bool,
    branches: Vec<Vec<Contribution>>,
    unresolved: Option<CovectorRefusal>,
}

/// The proposal: the leading branches' contributions and every positive or undecided term's
/// branches.
struct Proposal {
    contributions: Vec<Contribution>,
    terms: Vec<TermBranches>,
    unresolved: Vec<CovectorRefusal>,
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
            let contribution = |class: usize, member: &MemberCovector, sign: Rat| Contribution {
                request: request_index,
                cells: candidate_cells(refinement, station, class),
                covector: member.storage().expect("a resolved member"),
                sign,
            };
            // The leading branch's contribution.
            let target_member = leading_member(&chunk[target]);
            let leading = match (term.leading, &target_member) {
                (_, Err(refusal)) => Err(*refusal),
                (None, Ok(t)) => Ok(vec![contribution(target, t, -one.clone())]),
                (Some(x), Ok(t)) => leading_member(&chunk[x])
                    .map(|m| vec![contribution(x, m, one.clone()), contribution(target, t, -one.clone())]),
            };
            match leading {
                Ok(leading) => contributions.extend(leading),
                Err(refusal) => {
                    unresolved.push(refusal);
                    continue;
                }
            }
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
            });
        }
    }
    Proposal {
        contributions,
        terms: terms_out,
        unresolved,
    }
}

/// [definition; agent-inferred, September 30] **The proposal's returns at the source port**
/// (module header, "The covector"): one per phase of each request's moment (its feature the phase's
/// normalized counts, its covector the request's summed storage covector carried back through the
/// phase's rotation, `P^(c − τ)`), and one per class over the batch for the sections' placements
/// (feature `e_x` at the weight `Σ ν²`, covector their `ν`-weighted sum over it: the same unit step,
/// alignment and metric as one return a placement); each the descent covector.
fn returns(
    field: &Field,
    declared: &Refinement,
    requests: &[Request],
    contributions: &[Contribution],
) -> Result<Vec<Sample>, HnnError> {
    let ring = declared.ring();
    let geometry = field.ring(ring);
    let period = geometry.period() as usize;
    let width = geometry.width();
    let alphabet = field.alphabet();
    let chart = PopulationChart::of(field);
    let mut samples = Vec::new();
    let mut section_sums = vec![vec![Rat::zero(); width]; alphabet];
    let mut section_weights = vec![Rat::zero(); alphabet];
    for (index, request) in requests.iter().enumerate() {
        let lift = request.current.lift()[ring].clone();
        let mut shared = vec![Rat::zero(); width];
        for contribution in contributions.iter().filter(|c| c.request == index) {
            let covector: Vec<Rat> = contribution.covector.iter().map(face).collect();
            for (sum, value) in shared.iter_mut().zip(&covector) {
                *sum += value * &contribution.sign;
            }
            // The section's placements: each placed station's class at its phase, over ν̂(v).
            let phase = request.current.phase(field, ring)? as usize;
            let placed = contribution.cells.iter().filter(|c| c.is_some()).count() as u64;
            let nu = chart.value(placed);
            for (station, cell) in contribution.cells.iter().enumerate() {
                let Some(class) = cell else { continue };
                let at = (phase + 1 + station) % period;
                let rotated = geometry.rotate(&covector, &(BigInt::from(at) - &lift));
                for (sum, value) in section_sums[*class].iter_mut().zip(&rotated) {
                    *sum += value * &nu * &contribution.sign;
                }
                section_weights[*class] += &nu * &nu;
            }
        }
        if shared.iter().all(Zero::is_zero) {
            continue;
        }
        for c in 0..period {
            if request.moment.phase_counts(ring, c)?.iter().all(|&n| n == 0) {
                continue;
            }
            let feature = request.moment.normalized_counts(field, ring, c)?;
            let rotated = geometry.rotate(&shared, &(BigInt::from(c) - &lift));
            samples.push(Sample {
                weight: Rat::one(),
                feature,
                covector: rotated.into_iter().map(|x| -x).collect(),
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
) -> Result<(Vec<Sample>, Vec<(usize, Vec<Option<usize>>, Vec<Rat>, Rat)>), HnnError> {
    let read = |amplitudes: &[crate::ratio::GaussianRat]| bank.read_turn_covector(amplitudes, grain);
    let mut read_all = Vec::new();
    for request in requests {
        let (_, contexts) = read_contexts(field, constitution, request, declared, bank, grain, &read)?;
        let (_, terms) = compare_request(request, None, &contexts, field.alphabet())?;
        read_all.push((contexts, terms));
    }
    let proposal = propose(requests, &read_all, field.alphabet());
    let samples = returns(field, declared, requests, &proposal.contributions)?;
    Ok((
        samples,
        proposal
            .contributions
            .iter()
            .map(|c| {
                (
                    c.request,
                    c.cells.clone(),
                    c.covector.iter().map(face).collect(),
                    c.sign.clone(),
                )
            })
            .collect(),
    ))
}

/// The storage moves of every contribution's section under a move `ΔE` of the source port.
fn storage_moves(
    field: &Field,
    constitution: &Constitution,
    declared: &Refinement,
    requests: &[Request],
    moved: &ExactRatMatrix,
    sections: &[(usize, Vec<Option<usize>>)],
) -> Result<Vec<Vec<Rat>>, HnnError> {
    use rayon::prelude::*;
    let direction = SourceMove {
        base: constitution,
        ring: declared.ring(),
        source: moved.clone(),
    };
    let placements: Vec<BankPlacement> = requests
        .iter()
        .map(|r| BankPlacement::of(field, &direction, &r.current, &r.moment, declared))
        .collect::<Result<_, _>>()?;
    Ok(sections
        .par_iter()
        .map(|(request, cells)| placements[*request].storage(cells))
        .collect())
}

/// [definition; agent-inferred, September 30] **The first-order certificate of a carried move**
/// (module header): `Σ_terms sup_(α active) Df_α[ΔE]`, each branch's covector enclosures paired with
/// its candidates' exact storage moves, a term straddling zero bounded by `max(0, ·)`; the enclosure
/// of the sum's bound (its upper end is the certificate), and the terms whose active branches were
/// not all resolved.
fn first_order(
    field: &Field,
    constitution: &Constitution,
    declared: &Refinement,
    requests: &[Request],
    proposal: &Proposal,
    moved: &ExactRatMatrix,
) -> Result<(ExactInterval, usize), HnnError> {
    let mut sections: Vec<(usize, Vec<Option<usize>>)> = Vec::new();
    for term in &proposal.terms {
        for branch in &term.branches {
            for c in branch {
                sections.push((c.request, c.cells.clone()));
            }
        }
    }
    let moves = storage_moves(field, constitution, declared, requests, moved, &sections)?;
    let mut cursor = 0;
    let mut total = ExactInterval::point(Rat::zero());
    let mut unresolved = 0;
    for term in &proposal.terms {
        unresolved += usize::from(term.unresolved.is_some());
        let mut bound: Option<ExactInterval> = None;
        for branch in &term.branches {
            let mut derivative = ExactInterval::point(Rat::zero());
            for c in branch {
                let d = paired(&c.covector, &moves[cursor]);
                cursor += 1;
                let (a, b) = (&d.lower * &c.sign, &d.upper * &c.sign);
                derivative = ExactInterval {
                    lower: &derivative.lower + a.clone().min(b.clone()),
                    upper: &derivative.upper + a.max(b),
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
            continue;
        };
        if !term.positive {
            bound = positive_part(&bound);
        }
        total = ExactInterval {
            lower: &total.lower + &bound.lower,
            upper: &total.upper + &bound.upper,
        };
    }
    Ok((total, unresolved))
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
#[derive(Clone, Debug)]
pub struct Trial {
    pub step: Rat,
    pub moved: Rat,
    pub largest: Rat,
    pub first_order: Option<ExactInterval>,
    pub value: Option<ExactInterval>,
    pub after: Option<BatchComparison>,
    pub refusal: Option<TrialRefusal>,
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
    pub trials: Vec<Trial>,
    pub adopted: Option<(Constitution, SourceStep)>,
    pub refusal: Option<MoveRefusal>,
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
    first: &(dyn Fn(&ExactRatMatrix) -> Result<ExactInterval, HnnError> + Sync),
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
            moved: Rat::zero(),
            largest: Rat::zero(),
            first_order: None,
            value: None,
            after: None,
            refusal: None,
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
        let moved = successor
            .source_port(ring)
            .ok_or(HnnError::MissingSourcePort { ring })?
            .subtract(&source)?;
        trial.moved = largest_entry(&moved);
        trial.largest = reading.largest.clone();
        if trial.moved.is_zero() {
            return Ok((trials, None, Some(MoveRefusal::Guards)));
        }
        if reading.largest > entry_bound() {
            trial.refusal = Some(TrialRefusal::EntryBound(reading.largest.clone()));
            trials.push(trial);
            step /= &two;
            continue;
        }
        let bound = first(&moved)?;
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
        trials: Vec::new(),
        adopted: None,
        refusal: None,
    };
    if proposal.contributions.is_empty() {
        receipt.refusal = Some(MoveRefusal::Nothing);
        return Ok(receipt);
    }
    let samples = returns(field, declared, requests, &proposal.contributions)?;
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
    let (slope, _) = first_order(field, constitution, declared, requests, &proposal, &unit_move)?;
    receipt.slope = Some(slope.clone());
    if !slope.upper.is_negative() {
        receipt.refusal = Some(MoveRefusal::NoDescent(slope));
        return Ok(receipt);
    }
    let first = |moved: &ExactRatMatrix| {
        first_order(field, constitution, declared, requests, &proposal, moved).map(|(b, _)| b)
    };
    let reread = |successor: &Constitution| {
        executed_reread(field, successor, requests, declared, bank, grain)
    };
    let (trials, adopted, refusal) = ladder(
        constitution,
        ring,
        &samples,
        &before.value,
        &slope,
        &largest_entry(&unit_move),
        &first,
        &reread,
    )?;
    receipt.trials = trials;
    receipt.adopted = adopted;
    receipt.refusal = refusal;
    Ok(receipt)
}

/// [definition; agent-inferred, September 30] **The face's contexts and code at a constitution**
/// (the matched control of the bank's learning path, on the same contexts as the executed
/// comparison): for a partition, the readout's `stage_bank` with the targets placed; along the
/// machine's own trajectory, one `stage_bank` per refinement of the release the constitution
/// executes, its locked stations at the classes the machine locked and its open stations compared
/// with their targets. The code `Σ −log₂ θ_t` enclosed, the release comparisons where read, the
/// staged comparisons (for the returns), and whether every candidate crossing is admissible.
#[allow(clippy::type_complexity)]
fn face_read(
    field: &Field,
    constitution: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
) -> Result<(ExactInterval, Option<BatchComparison>, Vec<crate::hnn::prediction::BankStaged>, bool), HnnError>
{
    use crate::hnn::prediction::{BankImages, stage_bank};
    use rayon::prelude::*;
    let images = BankImages::of(field, constitution, declared, bank)?;
    let open = requests.iter().any(|r| matches!(r.context, Context::Open));
    let releases = if open {
        match compare(field, constitution, requests, declared, bank, grain) {
            Ok(batch) => Some(batch),
            Err(HnnError::UncertifiedResonator { .. }) => {
                return Ok((ExactInterval::point(Rat::zero()), None, Vec::new(), false));
            }
            Err(error) => return Err(error),
        }
    } else {
        None
    };
    let stations = declared.stations();
    let alphabet = field.alphabet();
    let staged: Vec<Vec<(crate::hnn::prediction::BankStaged, Vec<Option<usize>>)>> = requests
        .par_iter()
        .enumerate()
        .map(|(index, request)| {
            let sections: Vec<Vec<Option<usize>>> = match &request.context {
                Context::Partition(locked) => vec![
                    (0..stations)
                        .map(|j| locked[j].then_some(request.targets[j]))
                        .collect(),
                ],
                Context::Open => {
                    let generation = releases.as_ref().expect("the releases")
                        .requests[index]
                        .generation
                        .as_ref()
                        .expect("an open context's release");
                    let mut placed = vec![None; stations];
                    let mut sections = Vec::new();
                    for lock in &generation.locks {
                        sections.push(placed.clone());
                        for &station in lock {
                            placed[station] = Some(generation.release.classes[station]);
                        }
                    }
                    if placed.iter().any(Option::is_none) {
                        sections.push(placed);
                    }
                    sections
                }
            };
            sections
                .into_iter()
                .map(|placed| {
                    let targets: Vec<usize> = (0..stations)
                        .map(|j| placed[j].unwrap_or(request.targets[j]))
                        .collect();
                    let locked: Vec<bool> = placed.iter().map(Option::is_some).collect();
                    let staged = stage_bank(
                        field,
                        &request.current,
                        &request.moment,
                        declared,
                        &images,
                        &targets,
                        &locked,
                    )?;
                    Ok((staged, placed))
                })
                .collect::<Result<Vec<_>, HnnError>>()
        })
        .collect::<Result<_, HnnError>>()?;
    // Admission: every candidate crossing of every context the face compares.
    let admitted = requests
        .par_iter()
        .zip(&staged)
        .map(|(request, contexts)| {
            let placement =
                BankPlacement::of(field, constitution, &request.current, &request.moment, declared)?;
            for (_, placed) in contexts {
                for station in (0..stations).filter(|&j| placed[j].is_none()) {
                    for class in 0..alphabet {
                        let mut cells = placed.clone();
                        cells[station] = Some(class);
                        if !bank.admits(&crate::hnn::ring::turn(&placement.storage(&cells)))? {
                            return Ok(false);
                        }
                    }
                }
            }
            Ok(true)
        })
        .collect::<Result<Vec<bool>, HnnError>>()?
        .into_iter()
        .all(|a| a);
    let mut code = ExactInterval::point(Rat::zero());
    let mut all = Vec::new();
    for contexts in staged {
        for (staged, _) in contexts {
            code = crate::ratio::algebraic::interval_sum(&code, &staged.code)?;
            all.push(staged);
        }
    }
    Ok((code, releases, all, admitted))
}

/// **The committed move of `E` on the bank's face** (the matched control, one law with
/// [`executed_move`]): the face's code on the requests' contexts ([`face_read`]), its returns
/// (`hnn::prediction::bank_reach`), the unit step's alignment as its first-order slope, then the
/// same certified step's ladder, each successor's face code re-read on its own contexts and
/// adopted only when the code is strictly lower by disjoint enclosures and every guard holds.
pub fn face_move(
    field: &Field,
    constitution: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
) -> Result<ExecutedMove, HnnError> {
    use crate::hnn::prediction::{BankImages, bank_reach};
    let ring = declared.ring();
    let (code, releases, staged, admitted) =
        face_read(field, constitution, requests, declared, bank, grain)?;
    if !admitted {
        return Err(HnnError::UncertifiedResonator { ring, phase: 0 });
    }
    let before = match releases {
        Some(batch) => BatchComparison {
            value: code.clone(),
            ..batch
        },
        None => BatchComparison {
            requests: Vec::new(),
            value: code.clone(),
            readings: 0,
        },
    };
    let images = BankImages::of(field, constitution, declared, bank)?;
    let samples = bank_reach(&images, &staged).samples;
    let mut receipt = ExecutedMove {
        before,
        contributions: staged.iter().map(|s| s.stations.len()).sum(),
        returns: samples.len(),
        terms: staged.iter().map(|s| s.stations.len()).sum(),
        unresolved: Vec::new(),
        unresolved_branches: 0,
        slope: None,
        trials: Vec::new(),
        adopted: None,
        refusal: None,
    };
    if samples.is_empty() {
        receipt.refusal = Some(MoveRefusal::Nothing);
        return Ok(receipt);
    }
    // The face's first order along a carried move: `−Σ w ⟨g, ΔE f⟩`, its returns' descent
    // covectors paired exactly with the move, in nats, read in bits (over `ln 2` enclosed) as the
    // face's code is.
    let ln_two = ln_enclosure(&Rat::from_integer(BigInt::from(2)))?;
    let pairing = |moved: &ExactRatMatrix| -> Result<ExactInterval, HnnError> {
        let mut sum = Rat::zero();
        for sample in &samples {
            let image = moved.apply(&sample.feature)?;
            sum += &sample.weight
                * sample
                    .covector
                    .iter()
                    .zip(&image)
                    .map(|(g, m)| g * m)
                    .sum::<Rat>();
        }
        let nats = -sum;
        let (a, b) = (&nats / &ln_two.lower, &nats / &ln_two.upper);
        Ok(ExactInterval {
            lower: a.clone().min(b.clone()),
            upper: a.max(b),
        })
    };
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
    let slope = pairing(&unit_move)?;
    receipt.slope = Some(slope.clone());
    if !slope.upper.is_negative() {
        receipt.refusal = Some(MoveRefusal::NoDescent(slope));
        return Ok(receipt);
    }
    let reread = |successor: &Constitution| -> Result<Reread, HnnError> {
        let (code, releases, _, admitted) =
            face_read(field, successor, requests, declared, bank, grain)?;
        let floquet = releases.as_ref().is_some_and(|batch| {
            batch
                .requests
                .iter()
                .any(|r| r.generation.as_ref().is_some_and(|g| g.uncertified.is_some()))
        });
        let refusal = if !admitted {
            Some(TrialRefusal::Admission)
        } else if floquet {
            Some(TrialRefusal::Floquet)
        } else {
            None
        };
        Ok(Reread {
            value: code,
            comparison: releases,
            refusal,
        })
    };
    let (trials, adopted, refusal) = ladder(
        constitution,
        ring,
        &samples,
        &receipt.before.value.clone(),
        &slope,
        &largest_entry(&unit_move),
        &pairing,
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
    let ring = declared.ring();
    let alphabet = field.alphabet();
    let read = |amplitudes: &[crate::ratio::GaussianRat]| bank.read_turn_covector(amplitudes, grain);
    let mut read_all = Vec::new();
    for request in requests {
        let (_, contexts) = read_contexts(field, before, request, declared, bank, grain, &read)?;
        let (_, terms) = compare_request(request, None, &contexts, alphabet)?;
        read_all.push((contexts, terms));
    }
    let proposal = propose(requests, &read_all, alphabet);
    let moved = after
        .source_port(ring)
        .ok_or(HnnError::MissingSourcePort { ring })?
        .subtract(before.source_port(ring).ok_or(HnnError::MissingSourcePort { ring })?)?;
    let chosen: Vec<&Contribution> = proposal.contributions.iter().take(2 * count).collect();
    let sections: Vec<(usize, Vec<Option<usize>>)> =
        chosen.iter().map(|c| (c.request, c.cells.clone())).collect();
    let moves = storage_moves(field, before, declared, requests, &moved, &sections)?;
    let mut out = Vec::new();
    for (contribution, storage_move) in chosen.iter().zip(&moves) {
        let request = &requests[contribution.request];
        let at = |constitution: &Constitution| -> Result<TurnCovector, HnnError> {
            let placement =
                BankPlacement::of(field, constitution, &request.current, &request.moment, declared)?;
            bank.read_turn_covector(
                &crate::hnn::ring::turn(&placement.storage(&contribution.cells)),
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
