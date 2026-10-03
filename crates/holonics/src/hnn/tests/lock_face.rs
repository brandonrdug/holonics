//! Step 1b's gate A (the
//! [pin](../../../../../research/records/2026-09-30_STEP_1B_THE_CANDIDATE_COMPARISON_PINNED_BEFORE_ITS_RUNS.md)
//! §13; `hnn::executed`): the lock face and its normalization against its resting sheet; the zero
//! and unsupported targets and the declared input's validation; the first trial step and its
//! boundary cases; the two repaired refusals on every composition; active-face ties; the readings'
//! sites (the decisions along the key-consistent prefix on a release, a hold and a refused
//! certificate); the fixed incumbent mask; the conditions of adoption on every arm; and the
//! complete continuing state restored and continued over successive receptions. One test per stated
//! law and per boundary case.

use num_traits::{One, Signed, Zero};

use super::learning::{generic, moment};
use super::prediction::{executed_requests, joint, joint_bank};
use crate::hnn::HnnError;
use crate::hnn::constitution::{Constitution, ContinuingState, Locus};
use crate::hnn::executed::{
    Comparison, Composition, Context, Excess, LadderStart, MoveRefusal, Predicate, ProposalProbe,
    PlaneTerm, Reading, Request, TermSite, compare, executed_move, ladder_start, lock_face,
    mask_reread, proposal_returns, station_predicates, synthetic_batch, witness_form, witness_plane,
};
use crate::hnn::field::{ConstitutionRead, Field};
use crate::hnn::prediction::{BankRefinement, Refinement};
use crate::hnn::ring::{
    CovectorRefusal, DominantMultiplier, Growth, MemberCovector, TurnCovector, TurnReading,
};
use crate::ratio::algebraic::{ExactInterval, ln_enclosure};
use crate::ratio::disk::Disk;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer, rat};

fn growth(lower: Rat, upper: Rat) -> Growth {
    Growth { lower, upper }
}

fn at(x: Rat) -> Growth {
    growth(x.clone(), x)
}

/// A resolved member whose covector on a one-tick storage is `(re, im)` exactly.
fn resolved(member: usize, re: i64, im: i64) -> MemberCovector {
    MemberCovector::Resolved {
        member,
        multiplier: DominantMultiplier {
            disk: Disk::real(Rat::one()),
            pair: false,
            inner: Rat::zero(),
        },
        covector: vec![[
            ExactInterval::point(integer(re)),
            ExactInterval::point(integer(im)),
        ]],
    }
}

fn unresolved(member: usize) -> MemberCovector {
    MemberCovector::Unresolved {
        member,
        refusal: CovectorRefusal::Tie,
    }
}

/// A candidate read at `joint` (every member at the joint), with the given active members.
fn candidate(joint: Growth, active: Vec<MemberCovector>) -> TurnCovector {
    let count = active.iter().map(|m| m.member() + 1).max().unwrap_or(1);
    TurnCovector {
        reading: TurnReading {
            members: vec![joint.clone(); count],
            joint,
        },
        active,
    }
}

/// A one-station request's site at the open section.
fn site(station: usize, stations: usize) -> TermSite {
    TermSite {
        request: 0,
        station,
        cells: vec![None; stations],
        context: Some(0),
        post_error: false,
        held: false,
    }
}

/// One synthetic term of a one-station request (target `0`), its proposal probed.
fn probe(composition: Composition, candidates: Vec<TurnCovector>) -> (ProposalProbe, Rat) {
    let reads = vec![vec![candidates]];
    let batch = synthetic_batch(
        Comparison {
            composition,
            reading: Reading::Decisions,
        },
        &[vec![0]],
        vec![vec![site(0, 1)]],
        &reads,
        candidate_count(&reads) - 1,
    )
    .unwrap();
    (ProposalProbe::of(&batch, &reads), batch.excess.lower)
}

fn candidate_count(reads: &[Vec<Vec<TurnCovector>>]) -> usize {
    reads[0][0].len()
}

/// Each section's move: its first storage entry `m` (the one-tick covectors pair it with their real
/// part), class by class (the probe's sections are indexed class by class for one term).
fn moves(probe: &ProposalProbe, first: &[Rat]) -> Vec<Vec<Rat>> {
    probe
        .sections
        .iter()
        .map(|(_, station, cells)| {
            let class = cells[*station].expect("a candidate's section");
            vec![first[class].clone(), Rat::zero()]
        })
        .collect()
}

// -------------------------------------------------------------------------------------------
// the lock face

/// **The lock face reads the lock whole against its resting sheet** (Lean
/// `HNN/ExecutedComparison.{lockFace_lt_log_two_iff, lockFace_enclosure_sublevel,
/// lockFace_ge_log_two_of_rival}`; the pin §2.3, §13.2): at the flip exactly (`a_t = 1 + Σ a_x`) the
/// face reads `ln 2` and the station is not solved; the shares and the resting sheet's `1/Π` sum to
/// one; past the flip the rational test holds and the excess is exactly zero; the rational test is
/// strictly stronger than the release's per-rival predicates; the resting weight is the release's
/// threshold; a tie of every candidate lies above the level (where the hinge is zero); overlapping
/// enclosures leave the test undecided.
#[test]
fn the_lock_face_reads_the_lock_whole_against_its_resting_sheet() {
    let ln2 = ln_enclosure(&integer(2)).unwrap();
    let half = || at(rat(1, 2));
    // At the flip exactly: a_t = 3 = 1 + 4 · 1/2.
    let flip = [at(integer(3)), half(), half(), half(), half()];
    let face = lock_face(&flip, 0).unwrap();
    assert!(face.value.lower <= ln2.upper && ln2.lower <= face.value.upper);
    assert_eq!(face.solved, Predicate::Fails);
    assert!(!face.above);
    assert_eq!(face.kind(), Excess::Boundary);
    assert!(face.excess.lower.is_zero());
    assert_eq!(face.shares[0], ExactInterval::point(rat(1, 2)));
    for share in &face.shares[1..] {
        assert_eq!(*share, ExactInterval::point(rat(1, 12)));
    }
    let shares: Rat = face.shares.iter().map(|s| s.lower.clone()).sum();
    assert_eq!(shares + rat(1, 6), Rat::one());
    // Past the flip: a_t = 4 > 3.
    let solved = [at(integer(4)), half(), half(), half(), half()];
    let face = lock_face(&solved, 0).unwrap();
    assert_eq!(face.solved, Predicate::Holds);
    assert_eq!(face.kind(), Excess::Solved);
    assert_eq!(face.excess, ExactInterval::point(Rat::zero()));
    assert!(face.value.upper < ln2.lower);
    // Stronger than the per-rival predicates: 3 exceeds every rival and the unit, 1 + 3 ≥ 3.
    let per_rival = [at(integer(3)), at(Rat::one()), at(Rat::one()), half(), half()];
    let (_, class, threshold) = station_predicates(&per_rival, 0).unwrap();
    assert_eq!((class, threshold), (Predicate::Holds, Predicate::Holds));
    let face = lock_face(&per_rival, 0).unwrap();
    assert_eq!(face.solved, Predicate::Fails);
    assert_eq!(face.kind(), Excess::Above);
    // The resting sheet is the release's threshold: a target at the unit is never solved.
    let tiny = || at(rat(1, 1 << 20));
    let unit = [at(Rat::one()), tiny(), tiny(), tiny(), tiny()];
    assert_eq!(lock_face(&unit, 0).unwrap().solved, Predicate::Fails);
    // A tie of the five: ℓ = ln(11/2) > ln 5, above the level; the hinge's term is zero there.
    let tie: Vec<Growth> = (0..5).map(|_| at(integer(2))).collect();
    let face = lock_face(&tie, 0).unwrap();
    assert_eq!(face.kind(), Excess::Above);
    assert!(face.value.lower > ln_enclosure(&integer(5)).unwrap().upper);
    let (f, class, _) = station_predicates(&tie, 0).unwrap();
    assert!(!f.lower.is_positive() && !f.upper.is_negative());
    assert_eq!(class, Predicate::Fails);
    // Overlapping enclosures: 1 + 4 < 5 fails and 1 + 2 ≥ 6 fails.
    let rival = || growth(rat(1, 2), Rat::one());
    let overlap = [growth(integer(5), integer(6)), rival(), rival(), rival(), rival()];
    let face = lock_face(&overlap, 0).unwrap();
    assert_eq!(face.solved, Predicate::Undecided);
    assert_eq!(face.kind(), Excess::Boundary);
    assert!(face.excess.lower.is_zero());
}

/// **A zero or unsupported target is refused, typed, and the declared input is validated on every
/// arm** (the pin §13.4, §13.5): a target whose lower end is zero has no finite upper end of `ℓ` and
/// refuses the face (never solved, never divided by); a target outside the candidates and a
/// negative enclosure refuse; a zero rival is read. A request's targets must be one per station and
/// each a class of the chart, and a partition's mask one flag per station, before anything is read.
#[test]
fn a_zero_or_unsupported_target_is_refused_typed() {
    let zero = [growth(Rat::zero(), rat(1, 4)), at(Rat::one())];
    assert!(matches!(lock_face(&zero, 0), Err(HnnError::NonpositiveDeclaration)));
    let zero_rival = [at(integer(3)), at(Rat::zero())];
    assert_eq!(lock_face(&zero_rival, 0).unwrap().solved, Predicate::Holds);
    assert!(matches!(lock_face(&[at(Rat::one())], 1), Err(HnnError::Shape { .. })));
    let negative = [at(Rat::one()), growth(integer(-1), Rat::one())];
    assert!(matches!(lock_face(&negative, 0), Err(HnnError::NonpositiveDeclaration)));
    let field = joint();
    let theta = generic(&field, 94);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    for comparison in arms() {
        let mut requests = executed_requests(&field, &[(95, [0, 1, 2, 1])], Context::Open);
        requests[0].targets.pop();
        assert!(matches!(
            compare(&field, &theta, &requests, &refinement, &bank, 12, comparison),
            Err(HnnError::Shape { .. })
        ));
        assert!(matches!(
            executed_move(&field, &theta, &requests, &refinement, &bank, 12, comparison),
            Err(HnnError::Shape { .. })
        ));
        requests[0].targets = vec![0, 1, 3, 1];
        assert!(matches!(
            executed_move(&field, &theta, &requests, &refinement, &bank, 12, comparison),
            Err(HnnError::CellOutside { code: 3, alphabet: 3 })
        ));
        requests[0].targets = vec![0, 1, 2, 1];
        requests[0].context = Context::Partition(vec![true, false]);
        assert!(matches!(
            compare(&field, &theta, &requests, &refinement, &bank, 12, comparison),
            Err(HnnError::Shape { .. })
        ));
    }
}

// -------------------------------------------------------------------------------------------
// the first trial step

/// **The first trial step is the excess's first-order zero, and a zero excess or a nonnegative
/// slope never enters a division** (the pin §2.6, §13.5): `η₀ = 2^⌊log₂ min(X⁻/(−s_X⁺), ½/u)⌋`, the
/// entry scale alone when `X⁻ = 0` (with a station at exactly `ℓ = ln 2` still unsolved) or when
/// `s_X⁺ ≥ 0` (`X > 0` with a nonnegative derivative), and `1` in place of `½/u` at `u = 0`.
#[test]
fn the_ladder_starts_from_the_excess_and_never_divides_by_zero() {
    let u = rat(1, 4);
    assert_eq!(ladder_start(&Rat::zero(), &integer(-1), &u), (integer(2), LadderStart::ExcessZero));
    assert_eq!(ladder_start(&rat(1, 8), &Rat::zero(), &u), (integer(2), LadderStart::ExcessRising));
    assert_eq!(ladder_start(&rat(1, 8), &integer(3), &u), (integer(2), LadderStart::ExcessRising));
    assert_eq!(ladder_start(&rat(1, 8), &integer(-1), &u), (rat(1, 8), LadderStart::FirstOrderZero));
    assert_eq!(ladder_start(&rat(3, 16), &integer(-1), &u), (rat(1, 8), LadderStart::FirstOrderZero));
    assert_eq!(ladder_start(&integer(3), &rat(-1, 2), &u), (integer(2), LadderStart::EntryScale));
    assert_eq!(
        ladder_start(&Rat::zero(), &integer(-1), &Rat::zero()),
        (Rat::one(), LadderStart::ExcessZero)
    );
    // X = 0 with a station at exactly ln 2, beside a solved one: X⁻ = 0, the entry scale; the
    // station stays unsolved by the rational predicate.
    let half = || at(rat(1, 2));
    let flip = lock_face(&[at(integer(3)), half(), half(), half(), half()], 0).unwrap();
    let solved = lock_face(&[at(integer(4)), half(), half(), half(), half()], 0).unwrap();
    let excess = &flip.excess.lower + &solved.excess.lower;
    assert!(excess.is_zero());
    assert_eq!(ladder_start(&excess, &integer(-1), &u).1, LadderStart::ExcessZero);
    assert_eq!(flip.solved, Predicate::Fails);
}

// -------------------------------------------------------------------------------------------
// the repaired refusals

/// **An unresolved active member refuses the move on every composition** (the pin §13.4): the lock
/// face reads every candidate's active members, so an unresolved member of the target or of any
/// rival refuses; the hinge reads its active branches' members, so an unresolved member of its
/// target or of an active rival refuses, and one of a rival whose branch is not active is not read by
/// its certificate. A refused term is never bounded by its resolved members alone.
#[test]
fn an_unresolved_active_member_refuses_every_composition() {
    // Target 1/2 (below threshold: in every support); rival 1 active (its branch reads ln 2 as the
    // threshold does), rival 2 at 1/4 not active in the hinge's max.
    let growths = [at(rat(1, 2)), at(Rat::one()), at(rat(1, 4))];
    for composition in [Composition::Hinge, Composition::LockFace] {
        for unresolved_on in 0..3 {
            let candidates = growths
                .iter()
                .enumerate()
                .map(|(x, g)| {
                    let mut active = vec![resolved(0, 1, 0)];
                    if x == unresolved_on {
                        active.push(unresolved(1));
                    }
                    candidate(g.clone(), active)
                })
                .collect();
            let (probe, _) = probe(composition, candidates);
            let read = composition == Composition::LockFace || unresolved_on < 2;
            let first = probe.first_order(&moves(&probe, &[Rat::one(), Rat::one(), Rat::one()]));
            if read {
                assert_eq!(probe.unresolved_terms, 1, "{composition:?} {unresolved_on}");
                assert_eq!(probe.refusal(), Some(MoveRefusal::Unresolved(1)));
                assert_eq!(first.unresolved, 1);
            } else {
                assert_eq!(probe.unresolved_terms, 0);
                assert_eq!(probe.refusal(), None);
            }
        }
    }
}

/// **The slope is read on the joint direction** (the pin §13.4): on a lock-face term above its
/// level (every reading 1, `θ = 1/4` each), a port move that raises only the rivals' storages reads
/// a first-order bound `1/2 ≥ 0` and would refuse alone; joined by the modulus's storage move,
/// which raises the target's, the joint bound is `−1 < 0` and the move proceeds, its first trial
/// step at the excess's first-order zero from the joint derivative.
#[test]
fn the_slope_is_read_on_the_joint_direction() {
    let candidates = (0..3).map(|_| candidate(at(Rat::one()), vec![resolved(0, 1, 0)])).collect();
    let (probe, excess) = probe(Composition::LockFace, candidates);
    assert!(excess.is_positive());
    let port = probe.first_order(&moves(&probe, &[Rat::zero(), Rat::one(), Rat::one()]));
    assert_eq!(port.bound, ExactInterval::point(rat(1, 2)));
    assert!(matches!(ProposalProbe::slope_refusal(&port), Some(MoveRefusal::NoDescent(_))));
    // The modulus's part: +2 on the target's storage.
    let joint = probe.first_order(&moves(&probe, &[integer(2), Rat::one(), Rat::one()]));
    assert_eq!(joint.bound, ExactInterval::point(integer(-1)));
    assert_eq!(joint.excess, joint.bound);
    assert_eq!(ProposalProbe::slope_refusal(&joint), None);
    // X⁻ = ln 4 − ln 2 enclosed below; its first-order zero X⁻/1 ∈ [1/2, 1) under the entry scale 2.
    assert_eq!(
        ladder_start(&excess, &joint.excess.upper, &rat(1, 4)),
        (rat(1, 2), LadderStart::FirstOrderZero)
    );
    // The proposal's weights: θ_x = 1/4 on the rivals, θ_t − 1 = −3/4 on the target.
    let mut weights = probe.contributions.clone();
    weights.sort_by(|a, b| a.1.cmp(&b.1));
    assert_eq!(weights[0].1, rat(-3, 4));
    assert!(weights[1..].iter().all(|(_, w)| *w == rat(1, 4)));
}

/// **Active-face ties are read by every active member** (Lean
/// `HNN/ExecutedComparison.{lockFace_first_order, sup_upper_dini, sum_max_descends}`): a lock-face
/// term whose target has two active members (slopes `+1` and `−1`) and a rival with two (`−2`, `+3`)
/// is bounded by the rival's largest and the target's least,
/// `(1/4)(3) + (1/4)(0) + (−3/4)(−1) = 3/2`; a hinge term whose two rivals tie with its threshold
/// (every branch active) is bounded by its largest branch, `max(−1, 2 − 1, −5 − 1) = 1`.
#[test]
fn active_face_ties_are_read_by_every_active_member() {
    let lock = vec![
        candidate(at(Rat::one()), vec![resolved(0, 1, 0), resolved(1, -1, 0)]),
        candidate(at(Rat::one()), vec![resolved(0, -2, 0), resolved(1, 3, 0)]),
        candidate(at(Rat::one()), vec![resolved(0, 0, 0)]),
    ];
    let (probe_lock, _) = probe(Composition::LockFace, lock);
    let bound = probe_lock.first_order(&moves(&probe_lock, &[Rat::one(), Rat::one(), Rat::one()]));
    assert_eq!(bound.bound, ExactInterval::point(rat(3, 2)));
    let hinge = vec![
        candidate(at(rat(1, 2)), vec![resolved(0, 1, 0)]),
        candidate(at(Rat::one()), vec![resolved(0, 2, 0)]),
        candidate(at(Rat::one()), vec![resolved(0, -5, 0)]),
    ];
    let (probe_hinge, _) = probe(Composition::Hinge, hinge);
    let bound = probe_hinge.first_order(&moves(&probe_hinge, &[Rat::one(), Rat::one(), Rat::one()]));
    assert_eq!(bound.bound, ExactInterval::point(Rat::one()));
}

// -------------------------------------------------------------------------------------------
// the readings' sites

/// A synthetic refinement of the joint field's 4 stations and 3 classes: its placed section, its
/// open stations and the stations it locked.
fn refinement(placed: [Option<usize>; 4], locked: Vec<usize>) -> BankRefinement<()> {
    let open: Vec<(usize, usize)> = (0..4)
        .filter(|&s| placed[s].is_none())
        .flat_map(|s| (0..3).map(move |x| (s, x)))
        .collect();
    BankRefinement {
        placed: placed.to_vec(),
        read: vec![(); open.len()],
        open,
        tops: Vec::new(),
        eligible: Vec::new(),
        locked,
    }
}

/// `(context, station, held, post_error)` of each site.
fn read_sites(sites: &[TermSite]) -> Vec<(Option<usize>, usize, bool, bool)> {
    sites
        .iter()
        .map(|s| (s.context, s.station, s.held, s.post_error))
        .collect()
}

/// **The decisions read each station once along the key-consistent prefix, on a release, a hold
/// and a refused certificate** (the pin §2.4, §13.1, §13.4): `d(j)` is the refinement locking `j`
/// when that is before `r*`, else `r*`, the last refinement whose placed cells equal their targets;
/// every station has exactly one site (the obligations kept), the held stations are those read at a
/// refinement that did not lock them, and no decision is read after an error. The every-refinement
/// reading marks the refinements after `r*` post-error; the teacher-forced reading places the
/// earlier targets, at a refinement only where the release executed that section; a partition reads
/// its one refinement.
#[test]
fn the_decisions_read_each_station_once_along_the_consistent_prefix() {
    let sites_of = |request: &Request, refinements: &[BankRefinement<()>], reading: Reading| {
        crate::hnn::executed::sites_of(0, request, refinements, reading, 4, 3)
    };
    let field = joint();
    let request = executed_requests(&field, &[(95, [0, 1, 2, 1])], Context::Open).remove(0);
    // A release: station 2 locked right at 0, station 0 locked wrong (1 for 0) at 1, the rest at 2.
    let release = vec![
        refinement([None; 4], vec![2]),
        refinement([None, None, Some(2), None], vec![0]),
        refinement([Some(1), None, Some(2), None], vec![1, 3]),
    ];
    let (sites, consistent) = sites_of(&request, &release, Reading::Decisions);
    assert_eq!(consistent, Some(1));
    assert_eq!(
        read_sites(&sites),
        vec![
            (Some(1), 0, false, false),
            (Some(1), 1, true, false),
            (Some(0), 2, false, false),
            (Some(1), 3, true, false),
        ]
    );
    assert_eq!(sites[0].cells, vec![None, None, Some(2), None]);
    let (every, _) = sites_of(&request, &release, Reading::Every);
    assert_eq!(every.len(), 4 + 3 + 2);
    assert_eq!(every.iter().filter(|s| s.post_error).count(), 2);
    assert!(every.iter().filter(|s| s.post_error).all(|s| s.context == Some(2)));
    let (forced, _) = sites_of(&request, &release, Reading::TeacherForced);
    assert_eq!(
        forced.iter().map(|s| s.context).collect::<Vec<_>>(),
        vec![Some(0), None, None, None]
    );
    assert_eq!(forced[2].cells, vec![Some(0), Some(1), None, None]);
    assert!(forced.iter().all(|s| !s.post_error));
    // A hold at the open section: nothing eligible, every station read there, held.
    let hold = vec![refinement([None; 4], Vec::new())];
    let (sites, consistent) = sites_of(&request, &hold, Reading::Decisions);
    assert_eq!(consistent, Some(0));
    assert_eq!(
        read_sites(&sites),
        (0..4).map(|s| (Some(0), s, true, false)).collect::<Vec<_>>()
    );
    // A refused certificate at refinement 1 (nothing it would lock taken): r* = 1.
    let refused = vec![
        refinement([None; 4], vec![2]),
        refinement([None, None, Some(2), None], Vec::new()),
    ];
    let (sites, consistent) = sites_of(&request, &refused, Reading::Decisions);
    assert_eq!(consistent, Some(1));
    assert_eq!(
        read_sites(&sites),
        vec![
            (Some(1), 0, true, false),
            (Some(1), 1, true, false),
            (Some(0), 2, false, false),
            (Some(1), 3, true, false),
        ]
    );
    // A partition reads its one refinement's open stations.
    let mut partition = request.clone();
    partition.context = Context::Partition(vec![false, true, false, true]);
    let placed = refinement([None, Some(1), None, Some(1)], Vec::new());
    let (sites, consistent) = sites_of(&partition, &[placed], Reading::Decisions);
    assert_eq!(consistent, None);
    assert_eq!(
        read_sites(&sites),
        vec![(None, 0, false, false), (None, 2, false, false)]
    );
}

// -------------------------------------------------------------------------------------------
// the moves on the joint field

/// The arms of gate B: the lock face at the decisions, at every refinement and teacher-forced; the
/// hinge at the decisions and at every refinement.
fn arms() -> [Comparison; 10] {
    let arm = |composition, reading| Comparison {
        composition,
        reading,
    };
    [
        arm(Composition::LockFace, Reading::Decisions),
        arm(Composition::LockFace, Reading::Every),
        arm(Composition::Hinge, Reading::Decisions),
        arm(Composition::Hinge, Reading::Every),
        arm(Composition::LockFace, Reading::TeacherForced),
        arm(Composition::LockOrder, Reading::Decisions),
        arm(Composition::LockOrder, Reading::Every),
        arm(Composition::LockFace, Reading::Forced),
        arm(Composition::LockOrder, Reading::Forced),
        arm(Composition::LockOrder, Reading::ForcedDecisions),
    ]
}

/// The fixed mask of a batch's terms.
fn mask_of(batch: &crate::hnn::executed::BatchComparison) -> Vec<Vec<TermSite>> {
    batch
        .requests
        .iter()
        .map(|r| r.terms.iter().map(|t| t.site.clone()).collect())
        .collect()
}

/// **The fixed incumbent mask re-reads the incumbent's sections** (the pin §13.1): at the incumbent
/// itself the mask's composition and excess are the comparison's exactly and the own reading is the
/// comparison; on every arm.
#[test]
fn the_fixed_mask_rereads_the_incumbents_sections() {
    let field = joint();
    let theta = generic(&field, 94);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let requests =
        executed_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2])], Context::Open);
    for comparison in arms() {
        let batch = compare(&field, &theta, &requests, &refinement, &bank, 12, comparison).unwrap();
        let (value, excess, own, refusal) = mask_reread(
            &field,
            &theta,
            &requests,
            &refinement,
            &bank,
            12,
            comparison,
            &mask_of(&batch),
        )
        .unwrap();
        assert_eq!(value, batch.value);
        assert_eq!(excess, batch.excess);
        assert_eq!(own.as_ref(), Some(&batch));
        assert!(refusal.is_none());
    }
}

/// **A hold keeps every station obligation** (the pin §13.4): at `E = 0` every candidate of a
/// station reads one storage, nothing flips and the release holds at the open section; the
/// decisions and the teacher-forced readings read `m` terms a request, every one held, none absent.
#[test]
fn a_hold_keeps_every_station_obligation() {
    let field = joint();
    let base = generic(&field, 94);
    let port = base.source_port(0).unwrap();
    let theta = base
        .clone()
        .with_ports(0, None, Some(ExactRatMatrix::zero(port.rows(), port.columns()).unwrap()), None)
        .unwrap();
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let requests =
        executed_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2])], Context::Open);
    for comparison in arms() {
        let batch = compare(&field, &theta, &requests, &refinement, &bank, 12, comparison).unwrap();
        for request in &batch.requests {
            assert!(!request.generation.as_ref().unwrap().release.released());
        }
        let counts = batch.counts(4);
        assert_eq!(counts.obligations, 8);
        assert_eq!(counts.absent, 0);
        assert_eq!(counts.coverage, 8);
        if comparison.reading != Reading::Every {
            assert_eq!(counts.attempted, 8);
        }
        if comparison.reading == Reading::Decisions {
            assert_eq!(counts.held, 8);
            assert_eq!(counts.post_error, 0);
        }
    }
}

/// **The conditions of adoption hold the same on every arm** (the pin §13.4): on the joint field's
/// two requests, every arm's move either refuses by type (an unresolved member with its count and
/// no trial, a joint slope not negative, every trial refused by a named condition) or adopts a
/// successor whose fixed-mask composition is strictly lower by disjoint enclosures (its re-read at
/// the successor on the incumbent's sections), whose first order is certified negative on the
/// carried move, whose own release certifies every lock, and whose entries stay within the bound;
/// the first trial step is the stated one; the port's slope alone is only a receipt (equal to the
/// joint's where the modulus does not move); every station obligation is covered; the persistence
/// reads are consistent. The candidate arm (the lock face at the decisions) is adopted on this
/// instance.
#[test]
fn the_guards_hold_symmetrically_on_every_arm() {
    let field = joint();
    let theta = generic(&field, 94);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let requests =
        executed_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2])], Context::Open);
    for comparison in arms() {
        let moved =
            executed_move(&field, &theta, &requests, &refinement, &bank, 12, comparison).unwrap();
        assert_eq!(moved.comparison, comparison);
        assert_eq!(moved.sites.len(), moved.terms);
        assert_eq!(moved.counts.absent, 0);
        assert_eq!(moved.counts.coverage, 8);
        // Every refinement's open stations are read under the every-refinement and forced readings.
        if !matches!(comparison.reading, Reading::Every | Reading::Forced) {
            assert_eq!(moved.counts.attempted, 8);
        }
        let p = moved.persistence;
        assert_eq!(p.stay + p.fall, p.reread);
        assert_eq!(p.reversed + p.uncertified, p.fall);
        assert!(p.reread <= p.solved && p.solved <= p.locks);
        for trial in &moved.trials[..moved.trials.len().saturating_sub(1)] {
            assert!(trial.refusal.is_some());
        }
        if moved.modulus_unit.as_ref().is_some_and(Zero::is_zero) {
            assert_eq!(moved.port_slope, moved.slope);
        }
        match (&moved.adopted, &moved.refusal) {
            (Some((successor, step)), None) => {
                assert_eq!(moved.unresolved_branches, 0);
                assert!(moved.slope.as_ref().unwrap().upper.is_negative());
                let (start, _) = moved.start.clone().unwrap();
                assert_eq!(moved.trials[0].step, start);
                let last = moved.trials.last().unwrap();
                assert!(last.refusal.is_none());
                assert!(last.value.as_ref().unwrap().upper < moved.before.value.lower);
                assert!(last.first_order.as_ref().unwrap().upper.is_negative());
                assert!(step.largest <= crate::hnn::executed::entry_bound());
                let own = last.after.as_ref().unwrap();
                assert!(own
                    .requests
                    .iter()
                    .all(|r| r.generation.as_ref().unwrap().uncertified.is_none()));
                // The executed release's composition falls strictly too (the native direction
                // record's condition), and every earlier trial refused on the mask or the own
                // release carried its kind.
                assert!(own.value.upper < moved.before.value.lower);
                for trial in &moved.trials[..moved.trials.len() - 1] {
                    if let Some(crate::hnn::executed::TrialRefusal::OwnNotBelow(v)) = &trial.refusal {
                        assert!(trial.value.as_ref().unwrap().upper < moved.before.value.lower);
                        assert!(v.upper >= moved.before.value.lower);
                    }
                }
                // The mask's value at the successor is the incumbent's sections re-read there.
                let (value, _, reread_own, _) = mask_reread(
                    &field,
                    successor,
                    &requests,
                    &refinement,
                    &bank,
                    12,
                    comparison,
                    &mask_of(&moved.before),
                )
                .unwrap();
                assert_eq!(Some(&value), last.value.as_ref());
                assert_eq!(reread_own.as_ref(), Some(own));
                let change = last.change.as_ref().unwrap();
                assert_eq!(change.lower, &own.value.lower - &value.upper);
                assert_eq!(successor.commit(), theta.commit() + 1);
            }
            (None, Some(MoveRefusal::Unresolved(n))) => {
                assert_eq!(*n, moved.unresolved_branches);
                assert!(*n > 0 && moved.trials.is_empty());
            }
            (None, Some(MoveRefusal::NoDescent(bound))) => {
                assert_eq!(Some(bound), moved.slope.as_ref());
                assert!(!bound.upper.is_negative());
                assert!(moved.trials.is_empty());
            }
            (None, Some(MoveRefusal::Nothing)) => assert_eq!(moved.contributions, 0),
            (None, Some(_)) => assert!(moved.trials.iter().all(|t| t.refusal.is_some())),
            other => panic!("a move adopts or refuses, never both: {other:?}"),
        }
        if comparison == Comparison::LOCK_DECISIONS {
            assert!(moved.adopted.is_some(), "the candidate arm: {:?}", moved.refusal);
        }
    }
}

// -------------------------------------------------------------------------------------------
// the continuing state

/// Requests on the joint field whose span with the stations fills one turn (`n = 2` cells), so a
/// modulus below one reads them.
fn short_requests(field: &Field, cases: &[(u64, [usize; 4])]) -> Vec<Request> {
    cases
        .iter()
        .map(|&(seed, targets)| {
            let (current, moment) = moment(field, seed, 2);
            Request {
                current,
                moment,
                targets: targets.to_vec(),
                context: Context::Open,
            }
        })
        .collect()
}

/// **A restored checkpoint continues exactly, over successive receptions** (the pin §13.6): after one
/// adopted move of the candidate arm, the complete continuing state written as text and restored
/// onto the declared opening is the continued constitution exactly (the port, the carried Gram, the
/// chart, the remainders, the modulus, the clock, the commit and the storage product); then over
/// three successive receptions the restored and the continued constitutions return the same
/// observations (the comparisons), the same pullbacks (the returns at `E`) and deposits (every
/// trial, its first order, its re-reads and its carried source step), the same clock and section
/// behaviour, and the same subsequent state. A remount of `E` and `ρ` alone is partial: its text has
/// no state and is refused as a continuing state, its constitution loses the Gram, and its next
/// move deposits otherwise while it reads the same release.
#[test]
fn a_restored_checkpoint_continues_exactly_over_successive_receptions() {
    let field = joint();
    let opening = generic(&field, 94).with_transport(0, rat(3, 4)).unwrap();
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let comparison = Comparison::LOCK_DECISIONS;
    let receptions = [
        short_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2]), (97, [2, 0, 1, 1])]),
        short_requests(&field, &[(98, [1, 0, 2, 0]), (99, [0, 2, 1, 1]), (100, [2, 2, 0, 1])]),
        short_requests(&field, &[(101, [0, 0, 1, 2]), (102, [1, 2, 2, 0]), (103, [2, 1, 0, 0])]),
        short_requests(&field, &[(104, [1, 1, 1, 0]), (105, [0, 1, 0, 2]), (106, [2, 0, 2, 1])]),
    ];
    let step = |theta: &Constitution, requests: &[Request]| {
        executed_move(&field, theta, requests, &refinement, &bank, 12, comparison).unwrap()
    };
    let first = step(&opening, &receptions[0]);
    let (continued, _) = first.adopted.clone().expect("the first reception adopts a move");
    let locus = Locus::SourcePort(0);
    assert!(continued.clock(locus) >= 1);
    let text = continued.continuing_state(0).unwrap().to_text();
    let state = ContinuingState::from_text(&text).unwrap();
    assert_eq!(state, continued.continuing_state(0).unwrap());
    let restored = opening.clone().continued(&state).unwrap();
    assert_eq!(restored, continued);
    let (mut a, mut b) = (continued.clone(), restored);
    let mut adopted = 0;
    for requests in &receptions[1..] {
        let (ma, mb) = (step(&a, requests), step(&b, requests));
        assert_eq!(ma.before, mb.before);
        assert_eq!(
            proposal_returns(&field, &a, requests, &refinement, &bank, 12, comparison).unwrap(),
            proposal_returns(&field, &b, requests, &refinement, &bank, 12, comparison).unwrap()
        );
        assert_eq!((ma.slope.clone(), ma.start.clone()), (mb.slope.clone(), mb.start.clone()));
        assert_eq!(ma.trials.len(), mb.trials.len());
        for (ta, tb) in ma.trials.iter().zip(&mb.trials) {
            assert_eq!(
                (&ta.step, &ta.modulus, &ta.first_order, &ta.value, &ta.after, &ta.refusal),
                (&tb.step, &tb.modulus, &tb.first_order, &tb.value, &tb.after, &tb.refusal)
            );
            assert_eq!((&ta.terms, &ta.source), (&tb.terms, &tb.source));
        }
        assert_eq!(ma.refusal, mb.refusal);
        assert_eq!(ma.adopted, mb.adopted);
        if let (Some((sa, _)), Some((sb, _))) = (ma.adopted, mb.adopted) {
            assert_eq!(sa.clock(locus), sb.clock(locus));
            adopted += 1;
            a = sa;
            b = sb;
        }
        assert_eq!(a, b);
        let state = a.continuing_state(0).unwrap();
        assert_eq!(ContinuingState::from_text(&state.to_text()).unwrap(), state);
    }
    assert!(adopted >= 1, "a later reception adopts a move");
    // The partial remount: E and ρ alone.
    let rows = continued.source_port(0).unwrap().rows();
    let partial_text: String = text
        .lines()
        .take(rows + 2)
        .map(|line| format!("{line}\n"))
        .collect();
    assert!(matches!(
        ContinuingState::from_text(&partial_text),
        Err(HnnError::ContinuingState { .. })
    ));
    let partial = opening
        .clone()
        .with_ports(0, None, Some(continued.source_port(0).unwrap().clone()), None)
        .unwrap()
        .with_transport(0, continued.transport(0))
        .unwrap();
    assert_ne!(partial, continued);
    assert_ne!(
        partial.source_law(0).unwrap().gram(),
        continued.source_law(0).unwrap().gram()
    );
    let (from_partial, from_continued) = (step(&partial, &receptions[1]), step(&continued, &receptions[1]));
    assert_eq!(from_partial.before, from_continued.before);
    if let (Some((p, _)), Some((c, _))) = (&from_partial.adopted, &from_continued.adopted) {
        assert_ne!(p, c);
    }
    // A checkpoint is refused where another locus has moved or onto a constitution that is not the
    // declared opening.
    assert!(matches!(
        continued.clone().continued(&state_of(&continued)),
        Err(HnnError::ContinuingState { .. })
    ));
}

/// **A restored checkpoint authenticates the material it continues and refuses damage**: a state
/// carries the identity of its opening's material ([`Constitution::material_identity`]) and a check
/// over its text, so a state of the same shape and lattice is refused onto another opening (here
/// one founded from another seed), and a text damaged in one byte is refused before it mounts.
#[test]
fn a_checkpoint_is_refused_onto_foreign_material_and_when_damaged() {
    let field = joint();
    let opening = generic(&field, 94).with_transport(0, rat(3, 4)).unwrap();
    let foreign = generic(&field, 95).with_transport(0, rat(3, 4)).unwrap();
    assert_eq!(
        opening.source_port(0).map(|e| (e.rows(), e.columns())),
        foreign.source_port(0).map(|e| (e.rows(), e.columns()))
    );
    assert_ne!(opening.material_identity(0), foreign.material_identity(0));
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let requests = short_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2]), (97, [2, 0, 1, 1])]);
    let first = executed_move(&field, &opening, &requests, &refinement, &joint_bank(), 12, Comparison::LOCK_DECISIONS)
        .unwrap();
    let (continued, _) = first.adopted.expect("the reception adopts a move");
    // The move changes only the source port, so the identity is the opening's.
    assert_eq!(continued.material_identity(0), opening.material_identity(0));
    let text = state_of(&continued).to_text();
    let state = ContinuingState::from_text(&text).unwrap();
    assert_eq!(opening.clone().continued(&state).unwrap(), continued);
    assert!(matches!(
        foreign.clone().continued(&state),
        Err(HnnError::ContinuingState { what }) if what.contains("another opening")
    ));
    // One byte of the port's first row changed, still a well-formed rational: refused by the check.
    let row = text.lines().nth(1).expect("the port's first row");
    let at = text.find(row).expect("the row") + row.find(|c: char| c.is_ascii_digit()).expect("a digit");
    let mut damaged = text.clone().into_bytes();
    damaged[at] = if damaged[at] == b'7' { b'8' } else { b'7' };
    let damaged = String::from_utf8(damaged).unwrap();
    assert_ne!(damaged, text);
    assert!(matches!(
        ContinuingState::from_text(&damaged),
        Err(HnnError::ContinuingState { what }) if what.contains("damaged")
    ));
    // A changed material line is caught by the check as well.
    let material = format!("material {}", opening.material_identity(0));
    let relabelled = text.replace(&material, &format!("material {}", foreign.material_identity(0)));
    assert_ne!(relabelled, text);
    assert!(ContinuingState::from_text(&relabelled).is_err());
}

/// [the reception carry §2.4] **A continuing state carries the reception's end inside its check**:
/// a state written with a carried end reads back whole (every storage wave, arriving pair and
/// contact state, and the elapsed ticks), a state at rest writes no carry and reads back at rest
/// (every state written before the carry), the carry is resident motion that
/// [`Constitution::continued`] does not read, the stamp still replaces only what follows the storage
/// product, and one byte changed inside the carry is refused as damage.
#[test]
fn a_continuing_state_carries_the_receptions_end_inside_its_check() {
    use crate::hnn::word::{EndChange, ReceptionCarry};
    let field = joint();
    let opening = generic(&field, 94).with_transport(0, rat(3, 4)).unwrap();
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let requests = short_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2]), (97, [2, 0, 1, 1])]);
    let first = executed_move(&field, &opening, &requests, &refinement, &joint_bank(), 12, Comparison::LOCK_DECISIONS)
        .unwrap();
    let (continued, _) = first.adopted.expect("the reception adopts a move");
    let at_rest = state_of(&continued);
    assert!(at_rest.carry().is_none());
    assert!(!at_rest.to_text().contains("\ncarry "));
    // A carried end of the field's shape, every value a distinct exact rational.
    let mut k = 0i64;
    let mut wave = |n: usize| -> Vec<Rat> {
        (0..n)
            .map(|_| {
                k += 1;
                rat(if k % 2 == 0 { -k } else { k }, 2 * k + 1)
            })
            .collect()
    };
    let widths: Vec<usize> = field.rings().iter().map(|ring| ring.width()).collect();
    let storage = widths.iter().map(|n| wave(*n)).collect();
    let arrivals = field
        .contacts()
        .iter()
        .map(|contact| {
            let (a, b) = contact.ends();
            [wave(widths[a]), wave(widths[b])]
        })
        .collect();
    let states = field
        .contacts()
        .iter()
        .map(|contact| [wave(contact.width()), wave(contact.width())])
        .collect();
    let momenta = field.contacts().iter().map(|contact| wave(contact.width())).collect();
    let conductances = (0..field.contacts().len())
        .map(|a| rat(2 * a as i64 + 3, 4))
        .collect();
    let carry = ReceptionCarry {
        change: EndChange {
            storage,
            arrivals,
            states,
            resonators: vec![None, Some([wave(2), wave(2)])],
            resonator_phases: vec![None, Some(3)],
        },
        ticks: 27,
        conductances,
        momenta,
    };
    assert!(carry.fits(&field));
    let carried = at_rest.clone().with_carry(Some(carry.clone()));
    let text = carried.to_text();
    let read = ContinuingState::from_text(&text).unwrap();
    assert_eq!(read, carried);
    assert_eq!(read.carry(), Some(&carry));
    assert_eq!(opening.clone().continued(&read).unwrap(), continued);
    // The stamp replaces only what follows the storage product, so the carry stays inside it.
    let stamped = ContinuingState::stamped(&text, &opening).unwrap();
    assert_eq!(stamped, text);
    // One byte inside the carry changed: refused by the check.
    let at = text.find("\ncarry ").unwrap() + "\ncarry ".len();
    let mut damaged = text.clone().into_bytes();
    damaged[at] = if damaged[at] == b'7' { b'8' } else { b'7' };
    let damaged = String::from_utf8(damaged).unwrap();
    assert!(matches!(
        ContinuingState::from_text(&damaged),
        Err(HnnError::ContinuingState { what }) if what.contains("damaged")
    ));
}

fn state_of(theta: &Constitution) -> ContinuingState {
    theta.continuing_state(0).unwrap()
}

// -------------------------------------------------------------------------------------------
// the move's metric is its witness's

/// A plane term on the lock's own normalized reading at point readings `a`.
fn to_vecs(along: &[Vec<[Rat; 2]>]) -> Vec<Vec<Vec<Rat>>> {
    along.iter().map(|t| t.iter().map(|d| d.to_vec()).collect()).collect()
}

fn term(target: usize, readings: &[Rat], along: &[[Rat; 2]]) -> PlaneTerm {
    let joints: Vec<Growth> = readings.iter().cloned().map(at).collect();
    PlaneTerm {
        target,
        sheets: lock_face(&joints, target).unwrap().sheets,
        along: along.iter().map(|d| d.to_vec()).collect(),
    }
}

/// **The witness's form is the lock's normalized Jacobian pulled back** (the witness's metric
/// record): one lock with readings `a = (1, 2)` has sheets `(1, 1, 2)/4` (the resting sheet `1/4`),
/// so `θ = (1/4, 1/2)`; the form is `Σ θ δδᵀ − (Σ θ δ)(Σ θ δ)ᵀ`, the gradient `Σ (θ − q) δ`, and the
/// step solves `G s = −g` exactly, its Gauss–Newton change `−½ gᵀG⁻¹g < 0`. A lock whose candidates
/// all move alike along both directions sees a plane direction it cannot read: the step is refused.
#[test]
fn the_witness_form_is_the_locks_normalized_jacobian_pulled_back() {
    let w = witness_form(&[term(
        0,
        &[integer(1), integer(2)],
        &[[integer(2), integer(1)], [integer(-1), integer(3)]],
    )])
    .unwrap();
    assert_eq!(
        (w.form.at(0, 0), w.form.at(0, 1), w.form.at(1, 1)),
        (&rat(3, 2), &integer(-1), &(rat(19, 4) - rat(49, 16)))
    );
    assert_eq!(w.gradient, vec![integer(-2), rat(3, 4)]);
    let (a, b) = { let v = w.step().unwrap(); (v[0].clone(), v[1].clone()) };
    assert_eq!(w.form.at(0, 0) * &a + w.form.at(0, 1) * &b, integer(2));
    assert_eq!(w.form.at(0, 1) * &a + w.form.at(1, 1) * &b, rat(-3, 4));
    assert!(w.predicted().unwrap().is_negative());
    let flat = witness_form(&[term(
        0,
        &[integer(1), integer(2)],
        &[[integer(1), integer(1)], [integer(1), integer(1)]],
    )])
    .unwrap();
    assert!(flat.step().is_none());
}

/// **One lock reading for the comparison, the covector and the metric** (Astra's review), through
/// the actual proposal: three candidates whose growth enclosures are `[1, 9]` have share
/// enclosures `[1/20, 3/4]`, whose independent midpoints `17/40` sum to `51/40 > 1`; the normalized
/// face's Jacobian refuses that face. The lock face's one reading takes every candidate at its
/// enclosure's face `5`: sheets `(1, 5, 5, 5)/16`, each common share `5/16` inside its enclosure.
/// The proposal's covector weights are `θ_x − [x = t]` on exactly that reading, the witness's form
/// on it is positive semidefinite (`G_EE = Var(0, 1, 1, 1) = 15/256`), and a plane direction no
/// candidate's reading moves (`ρ` here) is the form's kernel: the step is refused.
#[test]
fn one_lock_reading_serves_the_comparison_the_covector_and_the_metric() {
    use crate::ratio::linear::inertia::inertia;
    use crate::receiver::face::softmax_jacobian;
    let wide = || growth(integer(1), integer(9));
    let joints = [wide(), wide(), wide()];
    let lock = lock_face(&joints, 0).unwrap();
    for share in &lock.shares {
        assert_eq!(*share, ExactInterval { lower: rat(1, 20), upper: rat(3, 4) });
    }
    let midpoints = vec![rat(17, 40); 3];
    assert!(softmax_jacobian(&midpoints).is_err());
    assert_eq!(lock.sheets, vec![rat(1, 16), rat(5, 16), rat(5, 16), rat(5, 16)]);
    assert!(lock.within());
    let (probe, _) = probe(
        Composition::LockFace,
        joints.iter().map(|g| candidate(g.clone(), vec![resolved(0, 1, 0)])).collect(),
    );
    let weights: Vec<Rat> = probe.contributions.iter().map(|(_, w)| w.clone()).collect();
    assert_eq!(weights, vec![rat(-11, 16), rat(5, 16), rat(5, 16)]);
    for (x, w) in weights.iter().enumerate() {
        assert_eq!(*w, lock.weight(x, 0));
    }
    let along = vec![vec![[integer(1), integer(0)]; 3]];
    let w = probe.plane(&to_vecs(&along)).unwrap();
    assert_eq!(w.form.at(0, 0), &rat(15, 256));
    assert_eq!(inertia(&w.form).negative, 0);
    assert!(w.step().is_none());
    let seen = vec![vec![
        [integer(1), integer(0)],
        [integer(1), integer(1)],
        [integer(1), integer(-1)],
    ]];
    assert!(probe.plane(&to_vecs(&seen)).unwrap().step().is_some());
}

/// **The witness's step is chart-free; the coordinate control is not** (Astra's `z′ = 2z`
/// example): rechart the storage by `B = 2` (`ĝ′ = ĝ/2`, `Δz′ = 2Δz`, `∂z′/∂ρ = 2∂z/∂ρ`). Every
/// `δ = ⟨ĝ, ·⟩` is unchanged, so the witness's form, gradient and step are unchanged, while the
/// control `−γ_ρ/Σ|∂z/∂ρ|²` is divided by 4. Rescaling the plane's `ρ` direction by `k` divides
/// `δ_ρ` by `k` and multiplies the step's `ρ` coordinate by `k`: the same move.
#[test]
fn the_witness_step_is_chart_free_and_the_coordinate_control_is_not() {
    let readings = [integer(1), integer(2)];
    let covectors = [[integer(3), integer(-1)], [integer(1), integer(2)]];
    let moves_e = [[integer(1), integer(1)], [integer(-1), integer(2)]];
    let moves_rho = [[integer(2), integer(-1)], [integer(1), integer(1)]];
    let weights = [rat(-3, 4), rat(1, 2)];
    let read = |scale: &Rat| {
        let pair = |x: usize, m: &[Rat; 2]| -> Rat {
            covectors[x].iter().zip(m).map(|(g, d)| (g / scale) * (d * scale)).sum()
        };
        let along: Vec<[Rat; 2]> =
            (0..2).map(|x| [pair(x, &moves_e[x]), pair(x, &moves_rho[x])]).collect();
        let gamma: Rat = weights.iter().zip(&along).map(|(c, d)| c * &d[1]).sum();
        let curvature: Rat = moves_rho
            .iter()
            .flat_map(|m| m.iter().map(|d| (d * scale) * (d * scale)))
            .sum();
        (witness_form(&[term(0, &readings, &along)]).unwrap(), -gamma / curvature)
    };
    let (w1, control1) = read(&Rat::one());
    let (w2, control2) = read(&integer(2));
    assert_eq!(w1, w2);
    assert_eq!(control2, control1 / integer(4));
    let k = integer(3);
    let along: Vec<[Rat; 2]> = (0..2)
        .map(|x| {
            let pair = |m: &[Rat; 2]| -> Rat { covectors[x].iter().zip(m).map(|(g, d)| g * d).sum() };
            [pair(&moves_e[x]), pair(&moves_rho[x]) / &k]
        })
        .collect();
    let (a, b) = { let v = w1.step().unwrap(); (v[0].clone(), v[1].clone()) };
    let (a3, b3) = { let v = witness_form(&[term(0, &readings, &along)]).unwrap().step().unwrap(); (v[0].clone(), v[1].clone()) };
    assert_eq!((a3, b3), (a, b * &k));
}

/// **Dropping the cross term is the negative control**: where `G_Eρ ≠ 0` the decoupled steps
/// `−g_i/G_ii` differ from the witness's step; where no lock couples the two directions they
/// coincide.
#[test]
fn dropping_the_cross_term_changes_the_step_only_where_the_witness_couples_the_plane() {
    let readings = [integer(1), integer(2)];
    let coupled = witness_form(&[term(
        0,
        &readings,
        &[[integer(2), integer(1)], [integer(-1), integer(3)]],
    )])
    .unwrap();
    assert!(!coupled.form.at(0, 1).is_zero());
    let (a, b) = { let v = coupled.step().unwrap(); (v[0].clone(), v[1].clone()) };
    assert_ne!(coupled.decoupled(), vec![Some(a), Some(b)]);
    let apart = witness_form(&[
        term(0, &readings, &[[integer(2), integer(0)], [integer(-1), integer(0)]]),
        term(0, &readings, &[[integer(0), integer(1)], [integer(0), integer(-1)]]),
    ])
    .unwrap();
    assert!(apart.form.at(0, 1).is_zero());
    let (a, b) = { let v = apart.step().unwrap(); (v[0].clone(), v[1].clone()) };
    assert_eq!(apart.decoupled(), vec![Some(a), Some(b)]);
}

/// **The machine's plane reading agrees with its move, and the witness's metric moves under the
/// same conditions of adoption** (the witness's metric record): on the candidate arm at a generic
/// constitution, the plane reading forms the move's own unit step (the same `γ_ρ`, `G_ρ` and
/// `−γ_ρ/G_ρ`) over the same terms, and its form is positive semidefinite. The move under the
/// witness's metric carries the witness's form, takes the witness's `α` (or the entry scale) as its
/// first trial step, moves `ρ` by `β/α` per unit of `E`'s step, and adopts only under every
/// condition the coordinate move keeps.
#[test]
fn the_machines_plane_reading_agrees_with_its_move() {
    use crate::hnn::executed::{LadderStart, MoveMetric, executed_move_in};
    use crate::ratio::linear::inertia::inertia;
    let field = joint();
    let theta = generic(&field, 94).with_transport(0, rat(3, 4)).unwrap();
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let requests =
        short_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2]), (97, [2, 0, 1, 1])]);
    let comparison = Comparison::LOCK_DECISIONS;
    let moved = executed_move(&field, &theta, &requests, &refinement, &bank, 12, comparison).unwrap();
    let plane = witness_plane(&field, &theta, &requests, &refinement, &bank, 12, comparison).unwrap();
    assert_eq!(plane.refusal, None);
    assert_eq!(plane.modulus_slope, moved.modulus_slope);
    assert_eq!(plane.modulus_curvature, moved.modulus_curvature);
    assert_eq!(plane.modulus_unit, moved.modulus_unit);
    assert_eq!(plane.terms, moved.terms);
    let form = plane.witness.unwrap();
    assert_eq!(inertia(&form.form).negative, 0);
    let witnessed = executed_move_in(
        &field,
        &theta,
        &requests,
        &refinement,
        &bank,
        12,
        comparison,
        MoveMetric::Witness,
    )
    .unwrap();
    assert_eq!(witnessed.metric, MoveMetric::Witness);
    assert_eq!(witnessed.witness.as_ref(), Some(&form));
    assert_eq!(witnessed.modulus_slope, moved.modulus_slope);
    match (form.step().and_then(|v| <[Rat; 2]>::try_from(v).ok()), &witnessed.refusal) {
        (None, Some(MoveRefusal::Invisible)) => {}
        (Some([a, _]), Some(MoveRefusal::Reversed(_))) => assert!(!a.is_positive()),
        (Some([a, b]), _) => {
            assert!(a.is_positive());
            // The trials carry the witness's exact step at the face grain, toward zero.
            let grain = Rat::new(1.into(), num_bigint::BigInt::from(1) << 63usize);
            let near = |held: &Rat, exact: &Rat| {
                held.abs() <= exact.abs() && (exact - held).abs() <= exact.abs() * &grain
            };
            assert!(near(witnessed.modulus_unit.as_ref().unwrap(), &(&b / &a)));
            let (start, kind) = witnessed.start.clone().unwrap();
            match kind {
                LadderStart::Witness => assert!(near(&start, &a)),
                LadderStart::WitnessEntryScale => assert!(start < a),
                other => panic!("the witness's first trial step is its own step: {other:?}"),
            }
            if let Some((successor, _)) = &witnessed.adopted {
                let last = witnessed.trials.last().unwrap();
                assert!(last.refusal.is_none());
                assert!(last.value.as_ref().unwrap().upper < witnessed.before.value.lower);
                assert!(last.after.as_ref().unwrap().value.upper < witnessed.before.value.lower);
                assert_eq!(successor.commit(), theta.commit() + 1);
            }
        }
        other => panic!("the witness's move: {other:?}"),
    }
}

// -------------------------------------------------------------------------------------------
// the order as a term of the comparison

/// One request of three stations read at the open section, its candidates at the given point
/// growths (each candidate one resolved member), under the given composition.
fn three_stations(
    composition: Composition,
    growths: [[Rat; 3]; 3],
) -> (crate::hnn::executed::BatchComparison, ProposalProbe) {
    let reads = vec![
        growths
            .iter()
            .map(|g| g.iter().map(|a| candidate(at(a.clone()), vec![resolved(0, 1, 0)])).collect())
            .collect::<Vec<Vec<TurnCovector>>>(),
    ];
    let batch = synthetic_batch(
        Comparison {
            composition,
            reading: Reading::Decisions,
        },
        &[vec![0, 1, 2]],
        vec![(0..3).map(|s| site(s, 3)).collect()],
        &reads,
        2,
    )
    .unwrap();
    let probe = ProposalProbe::of(&batch, &reads);
    (batch, probe)
}

/// **The order term reads the release's first lock as a lock over the stations** (the order's
/// pin): station 0's top is its target with gap `5 − 2 = 3`, station 1's top is wrong with gap
/// `9 − 2 = 7`, station 2's top is right with gap `3 − 1/2 = 5/2`. The right station of the largest
/// gap is 0; the sheets are `{0, 1}`, `ℓ_o = ln(10/3)`, not solved (`3 ≤ 7`: the release would lock
/// the wrong station 1 first). Each sheet returns through its top and runner,
/// `((θ − [x = r])/g)(a_top du_top − a_runner du_runner)`; the lock face's terms are unchanged.
#[test]
fn the_order_term_reads_the_first_lock_as_a_lock_over_the_stations() {
    let growths = [
        [integer(5), integer(2), integer(1)],
        [integer(9), integer(2), integer(1)],
        [rat(1, 2), rat(1, 4), integer(3)],
    ];
    let (face, face_probe) = three_stations(Composition::LockFace, growths.clone());
    let (batch, probe) = three_stations(Composition::LockOrder, growths);
    let order = batch.requests[0].order_terms[0].clone();
    let stations: Vec<(usize, usize, Rat)> =
        order.sheets.iter().map(|s| (s.station, s.top, s.gap.clone())).collect();
    assert_eq!(stations, vec![(0, 0, integer(3)), (1, 0, integer(7))]);
    assert_eq!(
        order.sheets.iter().map(|s| s.weight.clone()).collect::<Vec<_>>(),
        vec![rat(-7, 10), rat(7, 10)]
    );
    assert_eq!(order.solved, Predicate::Fails);
    assert_eq!(order.kind, Excess::Above);
    let ln = ln_enclosure(&rat(10, 3)).unwrap();
    assert_eq!(order.value, ln);
    assert_eq!(batch.value, plus_interval(&face.value, &ln));
    // The lock face's 9 contributions, then the order's top and runner for each sheet.
    assert_eq!(face_probe.contributions.len(), 9);
    assert_eq!(probe.contributions[..9], face_probe.contributions[..]);
    let order_weights: Vec<(usize, Rat)> = probe.contributions[9..].to_vec();
    assert_eq!(
        order_weights,
        vec![
            (0, rat(-7, 6)),
            (0, rat(7, 15)),
            (1, rat(9, 10)),
            (1, rat(-1, 5)),
        ]
    );
}

/// **The order is solved exactly when the right station's gap exceeds every wrong one's together**,
/// and absent where no eligible station's top is its target.
#[test]
fn the_order_is_solved_past_the_wrong_gaps_and_absent_without_a_right_top() {
    let solved = [
        [integer(20), integer(2), integer(1)],
        [integer(9), integer(2), integer(1)],
        [rat(1, 2), rat(1, 4), integer(3)],
    ];
    let (batch, _) = three_stations(Composition::LockOrder, solved);
    let order = batch.requests[0].order_terms[0].clone();
    assert_eq!(order.solved, Predicate::Holds);
    assert_eq!(order.kind, Excess::Solved);
    assert_eq!(order.excess, ExactInterval::point(Rat::zero()));
    let wrong = [
        [integer(1), integer(5), integer(1)],
        [integer(9), integer(2), integer(1)],
        [integer(3), rat(1, 4), rat(1, 2)],
    ];
    let (batch, _) = three_stations(Composition::LockOrder, wrong);
    assert!(batch.requests[0].order_terms.is_empty());
}

/// **The order term reads each wrong sheet at its upper end, the end the lock rule compares**: station
/// 0 is right with enclosure `[5, 6]` over its rivals' `2` and `1` (certain gap `3`, upper end `4`);
/// station 1's top is wrong with `[4, 6]` (certain gap `2`, upper end `4`); station 2 is right with
/// certain gap `5/2`. The certain gaps alone would call the order solved (`3 > 2`), yet the release
/// locks the wrong station 1 with station 0 (its upper end `4` meets the largest certain gap `3`). The
/// term reads `ℓ_o = ln((3 + 4)/3)`, not solved, in agreement with the lock rule. Narrowing station
/// 1's top to `[4, 9/2]` (upper end `5/2 < 3`) solves the order, and the release locks station 0 alone.
#[test]
fn the_order_term_reads_the_wrong_sheets_at_the_upper_end_the_lock_rule_compares() {
    use crate::hnn::executed::GapEnd;
    use crate::hnn::prediction::uncertified_largest;
    let batch_of = |top: Growth| {
        let growths = [
            [growth(integer(5), integer(6)), at(integer(2)), at(integer(1))],
            [top, at(integer(2)), at(integer(1))],
            [at(rat(1, 2)), at(rat(1, 4)), at(integer(3))],
        ];
        let reads = vec![
            growths
                .iter()
                .map(|g| g.iter().map(|a| candidate(a.clone(), vec![resolved(0, 1, 0)])).collect())
                .collect::<Vec<Vec<TurnCovector>>>(),
        ];
        synthetic_batch(
            Comparison {
                composition: Composition::LockOrder,
                reading: Reading::Decisions,
            },
            &[vec![0, 1, 2]],
            vec![(0..3).map(|s| site(s, 3)).collect()],
            &reads,
            2,
        )
        .unwrap()
    };
    let gaps = [(0, 0, integer(3)), (1, 0, integer(2)), (2, 2, rat(5, 2))];
    let batch = batch_of(growth(integer(4), integer(6)));
    let order = batch.requests[0].order_terms[0].clone();
    let sheets: Vec<(usize, usize, GapEnd, Rat)> =
        order.sheets.iter().map(|s| (s.station, s.runner, s.end, s.gap.clone())).collect();
    assert_eq!(
        sheets,
        vec![(0, 1, GapEnd::Lower, integer(3)), (1, 1, GapEnd::Upper, integer(4))]
    );
    assert_eq!(
        order.sheets.iter().map(|s| s.weight.clone()).collect::<Vec<_>>(),
        vec![rat(-4, 7), rat(4, 7)]
    );
    assert_eq!(order.value, ln_enclosure(&rat(7, 3)).unwrap());
    assert_eq!(order.solved, Predicate::Fails);
    assert_eq!(order.kind, Excess::Above);
    assert_eq!(uncertified_largest(&gaps, &[integer(4), integer(4), rat(5, 2)]), vec![0, 1]);
    let batch = batch_of(growth(integer(4), rat(9, 2)));
    let order = batch.requests[0].order_terms[0].clone();
    assert_eq!(order.sheets[1].gap, rat(5, 2));
    assert_eq!(order.solved, Predicate::Holds);
    assert_eq!(order.kind, Excess::Solved);
    assert_eq!(uncertified_largest(&gaps, &[integer(4), rat(5, 2), rat(5, 2)]), vec![0]);
}

fn plus_interval(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: &a.lower + &b.lower,
        upper: &a.upper + &b.upper,
    }
}

/// **The forced release reads every decision along the right trajectory** (the forced release's
/// record): under the forced reading every term's section holds only target cells (each earlier lock
/// placed at its target), every refinement's open stations are read, and the release itself (its
/// sections and receipts) is the release's own, the same as under the decisions reading.
#[test]
fn the_forced_release_reads_every_decision_along_the_right_trajectory() {
    let field = joint();
    let theta = generic(&field, 94);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let requests =
        executed_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2])], Context::Open);
    let forced = Comparison {
        composition: Composition::LockFace,
        reading: Reading::Forced,
    };
    let batch = compare(&field, &theta, &requests, &refinement, &bank, 12, forced).unwrap();
    let native =
        compare(&field, &theta, &requests, &refinement, &bank, 12, Comparison::LOCK_DECISIONS).unwrap();
    for ((request, own), r) in batch.requests.iter().zip(&native.requests).zip(&requests) {
        assert_eq!(request.generation, own.generation);
        assert!(!request.terms.is_empty());
        for term in &request.terms {
            for (cell, target) in term.site.cells.iter().zip(&r.targets) {
                if let Some(class) = cell {
                    assert_eq!(class, target);
                }
            }
        }
        // Every refinement's open stations: the first refinement reads every station.
        let first: Vec<usize> = request
            .terms
            .iter()
            .filter(|t| t.site.context == Some(0))
            .map(|t| t.site.station)
            .collect();
        assert_eq!(first, (0..r.targets.len()).collect::<Vec<_>>());
    }
}

// -------------------------------------------------------------------------------------------
// the receiver's minimum-energy move over all of E

/// **Each reading's gradient in `E` is its storage move's pairing, and the returns sum them**: at
/// the machine's opening and a move `ΔE` of every entry, each leading member's `⟨G, ΔE⟩` equals its
/// covector's pairing with its section's exact storage move, and `Σ c_m G_m` is the returns'
/// pullback with its sign reversed (`−Σ_t w_t g_t f_tᵀ`): one gradient for the solve and the normal
/// law.
#[test]
fn each_readings_gradient_in_e_is_its_storage_moves_pairing() {
    use crate::hnn::executed::reading_gradient_probe;
    let field = joint();
    let theta = generic(&field, 94).with_transport(0, rat(3, 4)).unwrap();
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let requests =
        short_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2]), (97, [2, 0, 1, 1])]);
    let port = theta.source_port(0).unwrap();
    let delta = ExactRatMatrix::new(
        (0..port.rows())
            .map(|i| {
                (0..port.columns())
                    .map(|j| rat(((7 * i + 3 * j) % 11) as i64 - 5, 1024))
                    .collect()
            })
            .collect(),
    )
    .unwrap();
    for comparison in [
        Comparison::LOCK_DECISIONS,
        Comparison { composition: Composition::LockOrder, reading: Reading::Decisions },
    ] {
        let (pairs, weighted, pullback) = reading_gradient_probe(
            &field, &theta, &requests, &refinement, &bank, 12, comparison, &delta,
        )
        .unwrap();
        assert!(!pairs.is_empty());
        for (gradient, storage) in &pairs {
            assert_eq!(gradient, storage);
        }
        assert!(pairs.iter().any(|(g, _)| !g.is_zero()));
        for (w, p) in weighted.iter().zip(&pullback) {
            assert_eq!(w, &-p.clone());
        }
    }
}

/// **The solve is the kinetic face's least-energy lift of the witness's Newton change**: one
/// candidate at `θ = ½` against its resting sheet wants its log-reading raised by `−F⁻¹c = 2`; read
/// along two entries of `E` with the mass's inverse `diag(1, 3)`, the lift spends it where the mass
/// is lighter, `v = (½, 3/2)`, not the coordinate split `(1, 1)`. Two candidates at
/// `θ = (¼, ¼)` over a resting `½` couple through the witness: the target's reading rises by `4`
/// and the rival's stays, `v = (4, 0, 0)`.
#[test]
fn the_solve_lifts_the_witnesss_newton_change_at_least_energy() {
    use crate::hnn::executed::{KineticStop, kinetic_lift_probe};
    let lighter = kinetic_lift_probe(
        &[(vec![rat(1, 2)], 0, vec![vec![(0, Rat::one())]])],
        &[vec![Rat::one(), Rat::one()]],
        &[vec![Rat::one(), Rat::zero()], vec![Rat::zero(), integer(3)]],
        2,
    )
    .unwrap();
    assert_eq!(lighter.stop, KineticStop::Converged);
    assert_eq!(lighter.moved.entries(), &[rat(1, 2), rat(3, 2)]);
    assert_eq!(lighter.predicted, rat(-1, 2));
    let identity: Vec<Vec<Rat>> =
        (0..3).map(|i| (0..3).map(|j| if i == j { Rat::one() } else { Rat::zero() }).collect()).collect();
    let coupled = kinetic_lift_probe(
        &[(
            vec![rat(1, 4), rat(1, 4)],
            0,
            vec![vec![(0, Rat::one())], vec![(1, Rat::one())]],
        )],
        &[
            vec![Rat::one(), Rat::zero(), Rat::zero()],
            vec![Rat::zero(), Rat::one(), Rat::zero()],
        ],
        &identity,
        3,
    )
    .unwrap();
    assert_eq!(coupled.stop, KineticStop::Converged);
    // Exact up to the recurrence's grain (every value held at 128 significant bits toward zero).
    let grain = Rat::new(1.into(), num_bigint::BigInt::from(1) << 120usize);
    for (v, expected) in coupled.moved.entries().iter().zip([integer(4), Rat::zero(), Rat::zero()]) {
        assert!((v - &expected).abs() <= grain);
    }
}

/// **The kinetic move deposits the solve through the normal law and keeps every condition of
/// adoption**: on the machine's opening, the move under the kinetic metric carries its solve, holds
/// `ρ`, starts at the Gauss–Newton step or the entry scale, its unit move's largest entry is the
/// solve's within `2^(−16)` of it (the chart's and the recurrence's grains), and an adopted trial
/// lowers the comparison.
#[test]
fn the_kinetic_move_deposits_the_solve_and_keeps_every_guard() {
    use crate::hnn::executed::{MoveMetric, executed_move_in};
    let field = joint();
    let theta = generic(&field, 94).with_transport(0, rat(3, 4)).unwrap();
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let requests =
        short_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2]), (97, [2, 0, 1, 1])]);
    let moved = executed_move_in(
        &field,
        &theta,
        &requests,
        &refinement,
        &bank,
        12,
        Comparison::LOCK_DECISIONS,
        MoveMetric::Kinetic,
    )
    .unwrap();
    assert_eq!(moved.metric, MoveMetric::Kinetic);
    let solve = moved.kinetic.as_ref().expect("the solve");
    assert!(solve.predicted.is_negative());
    assert_eq!(moved.modulus_unit, Some(Rat::zero()));
    let (_, kind) = moved.start.clone().unwrap();
    assert!(matches!(kind, LadderStart::Kinetic | LadderStart::KineticEntryScale));
    let largest = solve.moved.entries().iter().map(|x| x.abs()).max().unwrap();
    let unit = moved.unit_largest.clone().unwrap();
    assert!((&unit - &largest).abs() <= &largest / integer(1 << 16));
    if let Some((successor, _)) = &moved.adopted {
        let last = moved.trials.last().unwrap();
        assert!(last.value.as_ref().unwrap().upper < moved.before.value.lower);
        assert_eq!(successor.transport(0), theta.transport(0));
    }
}

/// **A release run ends at its close, a refusal, or its declared cap, never at a count of its own**
/// ([`crate::hnn::executed::release_run`]; the run-end record §2, §4). On the kinetic fixture with a
/// cap of two adopted moves: a negative `σ` is refused before any reading; the first move is the
/// guarded move with the excursion unchecked; a close reads the adopted trial's own release strictly
/// below the opening's lower end less `σ`; a run that neither closes nor is refused within the cap is
/// incomplete with exactly the cap's moves, and is never reported refused.
#[test]
fn the_release_run_ends_at_its_close_a_refusal_or_its_declared_cap() {
    use crate::hnn::executed::{
        MoveMetric, ReleaseExcursion, RunEnd, executed_move_guarded, release_run,
    };
    let field = joint();
    let theta = generic(&field, 94).with_transport(0, rat(3, 4)).unwrap();
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let requests =
        short_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2]), (97, [2, 0, 1, 1])]);
    let comparison = Comparison::LOCK_DECISIONS;
    let metric = MoveMetric::Kinetic;
    let cap = std::num::NonZeroUsize::new(2);
    assert_eq!(
        release_run(
            &field, &theta, &requests, &refinement, &bank, 12, comparison, metric, &rat(-1, 2),
            cap, |_, _| true,
        ),
        Err(HnnError::WindowDecrease { decrease: rat(-1, 2) })
    );
    let unchecked = ReleaseExcursion { checkpoint: None, height: None };
    let first = executed_move_guarded(
        &field, &theta, &requests, &refinement, &bank, 12, comparison, metric, &unchecked,
    )
    .unwrap();
    let decrease = rat(1, 16);
    let mut seen = Vec::new();
    let ran = release_run(
        &field, &theta, &requests, &refinement, &bank, 12, comparison, metric, &decrease, cap,
        |k, moved| {
            seen.push((k, moved.adopted.is_some()));
            if k == 0 {
                let steps = |m: &crate::hnn::executed::ExecutedMove| {
                    m.trials.iter().map(|t| (t.step.clone(), format!("{:?}", t.refusal))).collect::<Vec<_>>()
                };
                assert_eq!(steps(moved), steps(&first));
                assert_eq!(moved.refusal, first.refusal);
            }
            true
        },
    )
    .unwrap();
    assert_eq!(ran.opening, first.before.value);
    match &ran.end {
        RunEnd::Closed { moves, end, .. } => {
            assert!(*moves >= 1 && *moves <= 2);
            assert!(end.upper < &ran.opening.lower - &decrease);
            assert_eq!(seen.len(), *moves);
        }
        RunEnd::Refused { moves, refusal } => {
            assert!(*moves < 2);
            assert!(refusal.is_some());
            assert_eq!(seen.len(), moves + 1);
            assert!(!seen.last().unwrap().1);
        }
        RunEnd::Incomplete { moves, .. } => {
            assert_eq!(*moves, 2);
            assert_eq!(seen, vec![(0, true), (1, true)]);
        }
    }
}

/// **The joined solve spends the readings' change at least storage energy across `E` and `ρ`**
/// ([`ModulusCoupling`]): one candidate at `θ = ½` wants its log-reading raised by `2`.
/// - Where no entry of `E` moves the reading and `ρ` moves it by `2` a unit, `Δρ = 1` and `E` stays.
/// - Where one entry of mass `1` and `ρ` of mass `3` each move it by `1`, the change splits in
///   inverse proportion to the masses: `(ΔE, Δρ) = (3/2, 1/2)`.
/// - Where `ρ` moves no reading but its storage change couples to `E`'s (`M = [[1, ½], [½, 1]]`),
///   the least-energy move turns `ρ` against `E`'s storage change: `(ΔE, Δρ) = (2, −1)`.
#[test]
fn the_joined_solve_splits_the_readings_change_at_least_storage_energy() {
    use crate::hnn::executed::{KineticStop, ModulusCoupling, kinetic_lift_joined_probe};
    let grain = Rat::new(1.into(), num_bigint::BigInt::from(1) << 120usize);
    let close = |x: &Rat, y: Rat| (x - &y).abs() <= grain;
    let term = vec![(vec![rat(1, 2)], 0, vec![vec![(0, Rat::one())]])];
    let alone = kinetic_lift_joined_probe(
        &term,
        &[vec![Rat::zero(), Rat::zero()]],
        &[vec![Rat::one(), Rat::zero()], vec![Rat::zero(), Rat::one()]],
        2,
        &ModulusCoupling {
            columns: vec![integer(2)],
            coupling: vec![Rat::zero(), Rat::zero()],
            schur: integer(4),
        },
    )
    .unwrap();
    assert_eq!(alone.stop, KineticStop::Converged);
    assert!(close(alone.modulus.as_ref().unwrap(), Rat::one()));
    assert!(alone.moved.entries().iter().all(Zero::is_zero));
    assert!(close(&alone.predicted, rat(-1, 2)));
    let split = kinetic_lift_joined_probe(
        &term,
        &[vec![Rat::one()]],
        &[vec![Rat::one()]],
        1,
        &ModulusCoupling { columns: vec![Rat::one()], coupling: vec![Rat::zero()], schur: integer(3) },
    )
    .unwrap();
    assert!(close(&split.moved.entries()[0], rat(3, 2)));
    assert!(close(split.modulus.as_ref().unwrap(), rat(1, 2)));
    // The readings' own ask along `ρ` carries it all: `Δρ = (3/2 − 0)/3`.
    let (own, supplied) = split.modulus_drive.clone().unwrap();
    assert!(close(&own, rat(3, 2)) && supplied.is_zero());
    let coupled = kinetic_lift_joined_probe(
        &term,
        &[vec![Rat::one()]],
        &[vec![Rat::one()]],
        1,
        &ModulusCoupling {
            columns: vec![Rat::zero()],
            coupling: vec![rat(1, 2)],
            schur: rat(3, 4),
        },
    )
    .unwrap();
    assert!(close(&coupled.moved.entries()[0], integer(2)));
    assert!(close(coupled.modulus.as_ref().unwrap(), integer(-1)));
    // No reading asks along `ρ`; `E`'s move supplies `3/4` through the coupling, and `ρ` turns
    // against it: `Δρ = (0 − 3/4)/(3/4)`.
    let (own, supplied) = coupled.modulus_drive.clone().unwrap();
    assert!(own.is_zero() && close(&supplied, rat(3, 4)));
}

/// **The joined move carries `ρ` with `E` and keeps every condition of adoption**: on the machine's
/// opening at `ρ = 3/4`, the move under `KineticModulus` joins the modulus, carries its solve's
/// `Δρ` (negative here: the comparison asks for a shorter reach) as its modulus unit, starts at the
/// Gauss–Newton step or the entry scale, never carries `ρ` past `max(ρ₀, 3/4)`, and an adopted
/// trial lowers the comparison with `ρ` below `3/4`.
#[test]
fn the_joined_move_carries_the_modulus_and_keeps_every_guard() {
    use crate::hnn::executed::{MoveMetric, executed_move_in};
    let field = joint();
    let theta = generic(&field, 94).with_transport(0, rat(3, 4)).unwrap();
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let requests =
        short_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2]), (97, [2, 0, 1, 1])]);
    let moved = executed_move_in(
        &field,
        &theta,
        &requests,
        &refinement,
        &bank,
        12,
        Comparison::LOCK_DECISIONS,
        MoveMetric::KineticModulus,
    )
    .unwrap();
    assert_eq!(moved.metric, MoveMetric::KineticModulus);
    let solve = moved.kinetic.as_ref().expect("the solve");
    assert!(solve.predicted.is_negative());
    let ceiling = theta.founding_transport(&field, 0).unwrap().max(rat(3, 4));
    // On this opening the modulus joins and the comparison asks for a shorter reach.
    let delta = solve.modulus.as_ref().expect("the modulus joins");
    assert!(delta.is_negative());
    assert_eq!(moved.modulus_unit.as_ref(), Some(delta));
    let (_, kind) = moved.start.clone().unwrap();
    assert!(matches!(kind, LadderStart::Kinetic | LadderStart::KineticEntryScale));
    for trial in &moved.trials {
        if let Some(modulus) = &trial.modulus {
            assert!(modulus <= &ceiling);
        }
    }
    if let Some((successor, _)) = &moved.adopted {
        let last = moved.trials.last().unwrap();
        assert!(last.value.as_ref().unwrap().upper < moved.before.value.lower);
        assert!(successor.transport(0) <= ceiling);
        assert!(successor.transport(0) < rat(3, 4), "the adopted move shortens the reach");
    }
}

/// The joined move from `generic(seed)` at its founded `ρ₀` on the fixture's three requests.
fn joined_at_the_founding(seed: u64) -> (Rat, crate::hnn::executed::ExecutedMove) {
    use crate::hnn::executed::{MoveMetric, executed_move_in};
    let field = joint();
    let base = generic(&field, seed);
    let founding = base.founding_transport(&field, 0).unwrap();
    let theta = base.with_transport(0, founding.clone()).unwrap();
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let requests =
        short_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2]), (97, [2, 0, 1, 1])]);
    let moved = executed_move_in(
        &field,
        &theta,
        &requests,
        &refinement,
        &joint_bank(),
        12,
        Comparison::LOCK_DECISIONS,
        MoveMetric::KineticModulus,
    )
    .unwrap();
    (founding, moved)
}

/// **At the bound an upward ask is held, and the move is `E`'s alone** (the sign the main line's
/// `w16` walk reads): from `generic(92)` at its founded `ρ₀` the comparison's slope asks for a longer
/// memory (`γ_ρ < 0`), the joined solve asks `Δρ > 0` with the readings' ask exceeding what `E`
/// supplies, the bound holds it (the refused solve on the receipt), and the adopted successor keeps
/// `ρ₀`.
#[test]
fn the_bound_holds_an_upward_ask_and_the_move_is_e_alone() {
    let (founding, moved) = joined_at_the_founding(92);
    assert!(moved.modulus_slope.as_ref().unwrap().is_negative());
    let solve = moved.kinetic.as_ref().expect("the solve over E");
    assert!(solve.modulus.is_none() && solve.modulus_drive.is_none());
    let held = moved.modulus_held.as_ref().expect("the held ask");
    assert!(held.modulus.as_ref().unwrap().is_positive());
    let (own, supplied) = held.modulus_drive.clone().unwrap();
    assert!(own > supplied);
    assert_eq!(moved.modulus_unit.as_ref(), Some(&Rat::zero()));
    for trial in &moved.trials {
        assert!(trial.modulus.as_ref().is_none_or(|m| m == &founding));
    }
    let (successor, _) = moved.adopted.as_ref().expect("an adopted move");
    assert_eq!(successor.transport(0), founding);
}

/// **The joined direction is not the slope's sign** (`KineticSolve::modulus_drive`): from
/// `generic(99)` at its founded `ρ₀` the slope asks for a longer memory (`γ_ρ < 0`) and so do the
/// readings at the solve (`own > 0`), but `E`'s move already supplies more of that change through the
/// coupling (`supplied > own`), so the joined move shortens the memory (`Δρ < 0`).
#[test]
fn e_can_supply_more_than_the_readings_ask_and_turn_the_modulus() {
    let (_, moved) = joined_at_the_founding(99);
    assert!(moved.modulus_slope.as_ref().unwrap().is_negative());
    assert!(moved.modulus_held.is_none());
    let solve = moved.kinetic.as_ref().unwrap();
    assert!(solve.modulus.as_ref().unwrap().is_negative());
    let (own, supplied) = solve.modulus_drive.clone().unwrap();
    assert!(own.is_positive() && supplied > own);
}

/// **The coordinate and witness metrics keep `ρ` within its founding bound**: from `generic(92)` at
/// its founded `ρ₀` the comparison's slope asks for a longer memory (`γ_ρ < 0`), so the coordinate
/// law's `Δρ = −γ_ρ/G_ρ` and the witness's `β/α` would raise `ρ` past the one-turn alias bound; every
/// carried trial holds it at `max(ρ₀, ρ) = ρ₀`.
#[test]
fn the_founding_bound_holds_the_coordinate_and_witness_moduli() {
    use crate::hnn::executed::{MoveMetric, executed_move_in};
    let field = joint();
    let base = generic(&field, 92);
    let founding = base.founding_transport(&field, 0).unwrap();
    let theta = base.with_transport(0, founding.clone()).unwrap();
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let requests =
        short_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2]), (97, [2, 0, 1, 1])]);
    for metric in [MoveMetric::Coordinate, MoveMetric::Witness] {
        let moved = executed_move_in(
            &field,
            &theta,
            &requests,
            &refinement,
            &joint_bank(),
            12,
            Comparison::LOCK_DECISIONS,
            metric,
        )
        .unwrap();
        assert!(moved.modulus_slope.as_ref().unwrap().is_negative());
        for trial in &moved.trials {
            assert!(trial.modulus.as_ref().is_none_or(|m| m <= &founding), "{metric:?}");
        }
        if let Some((successor, _)) = &moved.adopted {
            assert!(successor.transport(0) <= founding);
        }
    }
}
