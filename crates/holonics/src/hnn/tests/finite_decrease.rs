//! The finite-decrease landing's laws (Refs #73 #62; the medium-of-joints record §7): the first
//! reach read from the owner's own split, the declared-step producer against the native one, the
//! reading-identity witness, the admission and the binding. Exact expectations only; the 0279
//! fixture's admission is a measurement, never forced.

use std::sync::Arc;

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::support::{contact, encoded, ring};
use crate::compression::landmark::context::{BaseMeasure, StopPrior};
use crate::hnn::chart::Charts;
use crate::hnn::constitution::{
    Carrier, Constitution, DeclaredExponents, DeclaredStepRefusal,
    FactorGradient, Family, FirstReach, Lattice, Locus, first_reach_scan,
};
use crate::hnn::encoding::Encoded;
use crate::hnn::field::{
    CribDeclaration, Current, Field, FieldDeclaration, FieldMaterial, ReceiverDeclaration,
};
use crate::hnn::moment::SourceMoment;
use crate::hnn::port::Deposit;
use crate::hnn::prediction::DamagedSection;
use crate::hnn::propagation::Operands;
use crate::hnn::ratio::{Faces, HolonRatio, TargetPhases};
use crate::hnn::receiving::{ReceivingPhases, ReceivingRead};
use crate::hnn::word::continuation::{
    AdmissionRefusal, Admitted, BindingRefusal, ContactCut, FiniteDecrease, Landing,
    LandingCandidate, LandingRefusal, admit, decide, reading_identity,
};
use crate::hnn::word::finite_gain::FiniteContactSpans;
use crate::hnn::HnnError;
use crate::hnn::word::{Absorption, EndChange, Word, WordOpening};
use crate::holon::deposition::dyadic;
use crate::ratio::algebraic::ExactInterval;
use crate::ratio::disk::floor_log2;
use crate::ratio::{Rat, integer, rat};

// -------------------------------------------------------------------------------------------
// 0279's own fixture (`tests/physical_communication.rs`: `receiver`, `field`, `contact_material`),
// declared before any observation.

fn receiver() -> ReceiverDeclaration {
    ReceiverDeclaration {
        ring: 0,
        aperture: 3,
        tolerance: rat(1, 16),
        depth: 1,
        prior: StopPrior::half(),
        mass: 1,
        base: BaseMeasure::Even,
        receiving_prior: 0,
    }
}

fn field() -> Field {
    Field::declare(
        FieldDeclaration {
            rings: vec![ring(4, (0..4).collect()), ring(3, Vec::new())],
            contacts: vec![contact(0, 1, 3, 0)],
            loops: Vec::new(),
            sources: vec![0],
            offsets: Vec::new(),
            alphabet: 4,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![receiver()],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 16,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap()
}

fn contact_material(field: &Field) -> Constitution {
    let reads = crate::hnn::retention::loci(field).into_iter().collect();
    super::learning::generic(field, 81)
        .rebased(Locus::Channel(0), 7, &reads)
        .unwrap()
}

/// 0279's W0 flow up to its comparison, without a resident: the same damaged section, source
/// moment, exact Word opened at rest, and junction steps as `communicate_contact`.
fn opened<'f>(
    field: &'f Field,
    theta: &Constitution,
    current: &Current,
    source: &[usize],
) -> (Arc<SourceMoment>, Word<'f>) {
    let declared = receiver();
    let chart = encoded(field, source);
    let section =
        DamagedSection::of_runs(declared.aperture, &chart, vec![(0, chart.clone())]).unwrap();
    let phases = ReceivingPhases::declare(field, theta, current, &declared).unwrap();
    section.admit(field, theta, &phases).unwrap();
    let mut moment = SourceMoment::open_with(field, current, theta).unwrap();
    for &g in field.sources() {
        moment = moment
            .station_section(field, current, g, &section.placed())
            .unwrap();
    }
    let moment = Arc::new(moment);
    let (mut word, _) = Word::open_source_exact_received(
        field,
        theta,
        current,
        Arc::clone(&moment),
        &WordOpening::Rest,
    )
    .unwrap();
    word.run(phases.junction_steps()).unwrap();
    (moment, word)
}

/// One comparison of 0279 (source `[0, 1]`, observed `[0, 1, 3]`, station 2 compared) with the
/// landing it issues.
struct Issued {
    moment: Arc<SourceMoment>,
    targets: Encoded,
    compared: Vec<bool>,
    ratio: HolonRatio,
    cut: ContactCut,
    deposit: Deposit,
    landing: Landing,
}

fn issued(field: &Field, theta: &Constitution, current: &Current) -> Issued {
    let (moment, word) = opened(field, theta, current, &[0, 1]);
    let targets = encoded(field, &[0, 1, 3]);
    let compared = vec![false, false, true];
    let (ratio, returned, landing) = word
        .compare_contacts_landing(0, &targets, &compared, &WordOpening::Rest)
        .unwrap();
    let cut = returned.forward.into_present().unwrap();
    let deposit = returned.deposit.into_present().unwrap();
    Issued {
        moment,
        targets,
        compared,
        ratio,
        cut,
        deposit,
        landing,
    }
}

/// The finite contact spans of the producing Word's operands (exact, opened at rest).
fn spans(
    field: &Field,
    theta: &Constitution,
    current: &Current,
    deposit: &Deposit,
) -> FiniteContactSpans {
    let operands = Operands::exact_at_cut(field, theta, current).unwrap();
    FiniteContactSpans::of(&operands, 0, deposit.reach().unwrap()).unwrap()
}

/// The exact remainder a carrier holds at an entry of the channel (zero where none is stored).
fn carried(constitution: &Constitution, carrier: Carrier, entry: usize) -> Rat {
    constitution
        .carried_remainders()
        .into_iter()
        .filter(|(l, c, i, _)| *l == Locus::Channel(0) && *c == carrier && *i == entry)
        .map(|(_, _, _, r)| r)
        .sum::<Rat>()
}

/// A contact family's Gram-factor descent direction `G` from the deposit.
fn gradient(deposit: &Deposit, family: Family) -> &crate::ratio::linear::ExactRatMatrix {
    let step = deposit
        .factors()
        .iter()
        .find(|s| s.gradient.locus() == Locus::Channel(0) && s.gradient.family() == family)
        .expect("the deposit returns the family");
    match &step.gradient {
        FactorGradient::Storage { gradient, .. }
        | FactorGradient::Stiffness { gradient, .. }
        | FactorGradient::Dissipation { gradient, .. } => gradient,
        _ => unreachable!("a contact family returns a Gram-factor gradient"),
    }
}

fn factor(constitution: &Constitution, family: usize) -> &crate::ratio::linear::ExactRatMatrix {
    match family {
        0 => constitution.contact_storage(0),
        1 => constitution.contact_stiffness(0),
        _ => constitution.contact_dissipation(0),
    }
}

/// The carry identity at a declared step, entry by entry for every contact family:
/// `2^k G_i / h′ + r_prior = ΔF_i + r_next` (factor carriers release nothing), `h′` the
/// successor's statistic; a family with no declared exponent has no step.
fn carry_identity(
    before: &Constitution,
    after: &Constitution,
    deposit: &Deposit,
    declared: &DeclaredExponents,
) {
    for f in 0..3 {
        let family = Family::Factor(f);
        let step = declared
            .exponent(Locus::Channel(0), family)
            .map_or_else(Rat::zero, dyadic);
        let statistic = &after.contact_scales(0)[f];
        let entries = gradient(deposit, family)
            .entries()
            .iter()
            .zip(factor(before, f).entries())
            .zip(factor(after, f).entries());
        for (i, ((g, old), new)) in entries.enumerate() {
            let proposed = &step * g / statistic;
            assert_eq!(
                proposed + carried(before, Carrier::Factor(f), i),
                (new - old) + carried(after, Carrier::Factor(f), i),
                "family {f} entry {i}: proposal + r_prior = applied + r_next"
            );
        }
    }
}

// -------------------------------------------------------------------------------------------
// the first reach

/// The split at a declared lattice, read entry by entry (`first_reach_scan`). At `L = 4` the unit is
/// `u = 1/16` and the half-unit `1/32`; `q(x) = ⌊16x + ½⌋`.
#[test]
fn the_first_reach_is_read_from_the_owner_split_entry_by_entry() {
    let lattice = Lattice::new(4);
    let half = rat(1, 32);
    // The split read: d = 1, r = 0. q(2^k) ≠ 0 exactly from 2^k = 1/32 (the tie goes up), so
    // k_f = −5; k_max = ⌊log₂(u / 1)⌋ + 1 = −3, the endpoint max(−10, −3).
    assert_eq!(
        first_reach_scan(&lattice, -10, &[(integer(1), Rat::zero())]).unwrap(),
        Some(FirstReach {
            exponent: -5,
            certified: -10,
            endpoint: -3,
            reached: vec![(0, BigInt::from(1))],
        })
    );
    assert_eq!(lattice.div_rem(&dyadic(-6)).0, BigInt::zero(), "2^-6 stays in its cell");
    // The invariant −u/2 ≤ r < u/2: the lower end is a remainder, the upper end is not.
    assert!(first_reach_scan(&lattice, -10, &[(integer(1), -half.clone())]).is_ok());
    assert!(first_reach_scan(&lattice, -10, &[(integer(1), half.clone())]).is_err());
    // A certificate above k_max: the scan starts and ends at k_cert, q(1) = 16.
    assert_eq!(
        first_reach_scan(&lattice, 0, &[(integer(1), Rat::zero())]).unwrap(),
        Some(FirstReach {
            exponent: 0,
            certified: 0,
            endpoint: 0,
            reached: vec![(0, BigInt::from(16))],
        })
    );
    // The endpoint with the remainder that delays the most, r = −u/2: 2^-4 − 1/32 = 1/32 reaches
    // (q = 1) while 2^-5 − 1/32 = 0 does not, so k_f = −4 ≤ k_max = −3.
    let delayed = first_reach_scan(&lattice, -10, &[(integer(1), -half.clone())])
        .unwrap()
        .unwrap();
    assert_eq!((delayed.exponent, delayed.endpoint), (-4, -3));
    assert_eq!(delayed.reached, vec![(0, BigInt::from(1))]);
    // No direction: the family is not in the candidate.
    assert_eq!(
        first_reach_scan(&lattice, -10, &[(Rat::zero(), Rat::zero()), (Rat::zero(), rat(1, 64))])
            .unwrap(),
        None
    );
}

/// Signed remainders decide, not `max |η d|`. Entry 0 is the widest (`d = 2`) with `r = −1/32`;
/// entry 1 has `d = 1` and `r = 31/1024`. At `k = −10`, entry 1 is `1/1024 + 31/1024 = 1/32`, the
/// tie, so `q = 1`; entry 0 is `2/1024 − 32/1024`, `q = 0`. At `k = −11` entry 1 is `63/2048` and
/// entry 0 `−31/1024`: both stay. So `k_f = −10`, reached by the narrower entry, while
/// `max |η d| = 2^-9` lies 4 binary orders below the half-unit and a half-unit rule on `max |η d|`
/// would name `k = −6`.
#[test]
fn a_signed_remainder_moves_the_first_reach_off_the_widest_entry() {
    let lattice = Lattice::new(4);
    let entries = [(integer(2), -rat(1, 32)), (integer(1), rat(31, 1024))];
    let reach = first_reach_scan(&lattice, -20, &entries).unwrap().unwrap();
    assert_eq!(
        reach,
        FirstReach {
            exponent: -10,
            certified: -20,
            // k_max = ⌊log₂((1/16) / 2)⌋ + 1 = −4.
            endpoint: -4,
            reached: vec![(1, BigInt::from(1))],
        }
    );
    let widest = dyadic(-10) * integer(2);
    assert_eq!(lattice.div_rem(&(&widest - rat(1, 32))).0, BigInt::zero());
    assert!(widest < rat(1, 32), "max |η d| is below the half-unit at the first reach");
    // The half-unit rule on the widest entry alone: the least k with 2^k · 2 ≥ 1/32.
    assert!(dyadic(-6) * integer(2) >= rat(1, 32) && dyadic(-7) * integer(2) < rat(1, 32));
}

// -------------------------------------------------------------------------------------------
// the declared-step producer on 0279's own deposit

/// With the CERTIFIED exponents declared, the declared-step producer is the native deposit: the
/// successor (material and carries, as one value) and the publication are equal, and no reach is
/// claimed. Only the exponent source differs.
#[test]
fn the_certified_exponents_declared_reproduce_the_native_deposit() {
    let field = field();
    let theta = contact_material(&field);
    let current = Current::at_rest(&field);
    let issued = issued(&field, &theta, &current);
    let spans = spans(&field, &theta, &current, &issued.deposit);
    let (native, reading) = theta
        .deposited_with_contact_spans(&issued.deposit, &spans)
        .unwrap();
    let declared = DeclaredExponents::certified(&reading);
    let (successor, publication, committed) = theta
        .deposited_with_contact_spans_at(&issued.deposit, &spans, &declared)
        .unwrap()
        .unwrap();
    assert_eq!(successor, native, "the same successor, material and carries");
    assert_eq!(successor.carried_remainders(), native.carried_remainders());
    assert_eq!(publication, reading, "the same publication");
    assert!(committed.families.is_empty(), "no reach is claimed at the certified exponents");
    carry_identity(&theta, &successor, &issued.deposit, &declared);
}

/// The first reach is read from the native pass's own state: the test re-reads it from the
/// published statistics `h′` and the prior remainders, checks that no exponent in
/// `[k_cert, k_f)` leaves any cell, and then reads the producer: a candidate whose committed reach
/// is its proposed reach, entry by entry, with the carry identity at `2^(k_f)`; or, measured, the
/// typed refusal of a first reach above the covector-scale bound.
#[test]
fn the_first_reach_commits_its_proposed_reach_or_refuses_typed() {
    let field = field();
    let theta = contact_material(&field);
    let current = Current::at_rest(&field);
    let issued = issued(&field, &theta, &current);
    let spans = spans(&field, &theta, &current, &issued.deposit);
    let (native, certified) = theta
        .deposited_with_contact_spans(&issued.deposit, &spans)
        .unwrap();
    // A deposit at the same commit and reach with no stepping family: nothing can reach.
    let unreached = Deposit::new(theta.commit(), vec![], vec![], vec![])
        .with_reach(issued.deposit.reach().unwrap().clone());
    assert_eq!(
        theta.first_reach(&unreached, &spans).unwrap(),
        Err(DeclaredStepRefusal::NoReach)
    );
    let declared = theta
        .first_reach(&issued.deposit, &spans)
        .unwrap()
        .expect("0279's reached families have certified steps, so each has a first reach");
    let locus = Locus::Channel(0);
    let lattice = theta.lattice(locus).unwrap();
    for (&(at, family), step) in declared.families_with_steps() {
        let Family::Factor(f) = family else {
            panic!("a contact family")
        };
        assert_eq!(at, locus);
        let reach = step
            .reach
            .as_ref()
            .expect("the first-reach read claims each family it declares");
        assert_eq!(step.exponent, reach.exponent);
        let k_cert = certified
            .steps
            .iter()
            .find(|(l, r)| *l == locus && r.family == family)
            .map(|(_, r)| r.step.exponent)
            .expect("the family's certified step");
        assert_eq!(reach.certified, k_cert);
        let statistic = &native.contact_scales(0)[f];
        let entries: Vec<(Rat, Rat)> = gradient(&issued.deposit, family)
            .entries()
            .iter()
            .enumerate()
            .map(|(i, g)| (g / statistic, carried(&theta, Carrier::Factor(f), i)))
            .collect();
        assert_eq!(
            first_reach_scan(&lattice, k_cert, &entries).unwrap().as_ref(),
            Some(reach),
            "the read used the pass's own h′ and remainders"
        );
        for k in k_cert..reach.exponent {
            assert!(
                entries
                    .iter()
                    .all(|(d, r)| lattice.div_rem(&(dyadic(k) * d + r)).0.is_zero()),
                "family {f}: no entry leaves its cell below the first reach (k = {k})"
            );
        }
        println!(
            "first reach family {f}: k_cert={k_cert} k_f={} endpoint={} reached={:?}",
            reach.exponent, reach.endpoint, reach.reached
        );
    }
    match theta
        .deposited_with_contact_spans_at(&issued.deposit, &spans, &declared)
        .unwrap()
    {
        Ok((candidate, publication, committed)) => {
            assert_eq!(candidate.commit(), theta.commit() + 1);
            carry_identity(&theta, &candidate, &issued.deposit, &declared);
            for (key, step) in declared.families_with_steps() {
                let reach = step.reach.as_ref().expect("claimed");
                assert_eq!(
                    committed.families.get(key),
                    Some(&reach.reached),
                    "the committed reach is the proposed reach"
                );
            }
            assert!(publication.vanished.is_empty(), "every claimed family moved");
            println!("first reach committed: {:?}", committed.families);
        }
        Err(DeclaredStepRefusal::CovectorScale {
            locus: at,
            family,
            exponent,
        }) => {
            let covector = certified
                .steps
                .iter()
                .find(|(l, r)| *l == at && r.family == family)
                .map(|(_, r)| r.step.covector.clone())
                .expect("the refused family's reading");
            assert_eq!(declared.exponent(at, family), Some(exponent));
            assert!(dyadic(exponent) * covector > Rat::one());
            println!("first reach refused at the covector-scale bound: {family:?} k={exponent}");
        }
        Err(other) => panic!("the first reach refused otherwise: {other:?}"),
    }
}

/// A declared exponent past the covector-scale bound refuses, typed: one family one exponent above
/// `⌊log₂(1/c)⌋`, every other family at its certified exponent.
#[test]
fn a_declared_exponent_past_the_covector_scale_refuses_typed() {
    let field = field();
    let theta = contact_material(&field);
    let current = Current::at_rest(&field);
    let issued = issued(&field, &theta, &current);
    let spans = spans(&field, &theta, &current, &issued.deposit);
    let (_, certified) = theta
        .deposited_with_contact_spans(&issued.deposit, &spans)
        .unwrap();
    let (locus, reading) = certified.steps.first().expect("a certified family").clone();
    let covector = reading.step.covector.clone();
    assert!(covector.is_positive(), "a reached nonzero direction has a nonzero covector");
    let exponent = floor_log2(&(Rat::one() / &covector)) + 1;
    assert!(dyadic(exponent) * &covector > Rat::one());
    let declared = DeclaredExponents::declare(certified.steps.iter().map(|(l, r)| {
        let k = if (*l, r.family) == (locus, reading.family) {
            exponent
        } else {
            r.step.exponent
        };
        ((*l, r.family), k)
    }));
    match theta
        .deposited_with_contact_spans_at(&issued.deposit, &spans, &declared)
        .unwrap()
    {
        Err(refusal) => assert_eq!(
            refusal,
            DeclaredStepRefusal::CovectorScale {
                locus,
                family: reading.family,
                exponent,
            }
        ),
        Ok(_) => panic!("a step past the covector-scale bound was produced"),
    }
}

// -------------------------------------------------------------------------------------------
// the witness and the admission

/// One compared station at grain 1 (each class's cell `(⌊Re⌋, 0)`, phase `Im/2` turns), its
/// target class 0 at target phase 0 and branch 0.
fn station(logits: Vec<Rat>) -> HolonRatio {
    let read = ReceivingRead::of_logits(logits, 1);
    let faces = Faces::of_reads(&[read], 1).unwrap();
    HolonRatio::compare_partition(
        faces,
        &[0],
        &TargetPhases {
            branch: BigInt::zero(),
            phases: vec![Rat::zero()],
        },
        &[true],
    )
    .unwrap()
}

/// Cells `(0, −1)` (`Z = 3/2`) with the target's phase `1/2` (`X = 1/8`).
fn producing_station() -> HolonRatio {
    station(vec![integer(0), integer(1), integer(-1), integer(0)])
}

#[test]
fn the_reading_identity_reads_gauge_normalized_cells_never_endpoints() {
    let producing = producing_station();
    assert_eq!(producing.excess(), rat(1, 8));
    // Equal inputs.
    assert!(reading_identity(&producing, &producing_station()));
    // A common carry shift: cells (5, 4) normalize to the same (0, −1).
    let shifted = station(vec![integer(5), integer(1), integer(4), integer(0)]);
    assert!(reading_identity(&producing, &shifted));
    assert_eq!(shifted.code_length().unwrap(), producing.code_length().unwrap());
    // One differing cell: (0, −2).
    let differing = station(vec![integer(0), integer(1), integer(-2), integer(0)]);
    assert!(!reading_identity(&producing, &differing));
    // Equal endpoints without equal inputs: cells (0, −1, −2, −2) and (0, −2, −1, −2) both have
    // Z = 2, so both code lengths are the point 1; the cells differ, so there is no witness.
    let left = station(vec![
        integer(0),
        integer(1),
        integer(-1),
        integer(0),
        integer(-2),
        integer(0),
        integer(-2),
        integer(0),
    ]);
    let right = station(vec![
        integer(0),
        rat(1, 2),
        integer(-2),
        integer(0),
        integer(-1),
        integer(0),
        integer(-2),
        integer(0),
    ]);
    let point = ExactInterval::point(integer(1));
    assert_eq!(left.code_length().unwrap(), point);
    assert_eq!(right.code_length().unwrap(), point);
    assert!(!reading_identity(&left, &right));
    // Even with X′ = 1/32 < X = 1/8, equal endpoints are not equal codes.
    assert_eq!(right.excess(), rat(1, 32));
    assert_eq!(
        admit(&left, &right),
        Err(LandingRefusal::Admission(AdmissionRefusal::EqualEndpoints))
    );
}

#[test]
fn the_admission_is_an_exact_strict_improvement_and_refuses_typed() {
    let interval = |lower: Rat, upper: Rat| ExactInterval::new(lower, upper).unwrap();
    let (low, high) = (interval(integer(1), integer(2)), interval(integer(3), integer(4)));
    let one = integer(1);
    // Classical: upper(L′) = 2 < lower(L) = 3 and X′ ≤ X.
    assert_eq!(decide(&high, &one, &low, &one, false), Ok(Admitted::Classical));
    assert_eq!(decide(&high, &one, &low, &rat(1, 2), false), Ok(Admitted::Classical));
    // Phase: the witness and X′ < X.
    assert_eq!(decide(&low, &one, &low, &rat(1, 2), true), Ok(Admitted::Phase));
    // Refusals.
    assert_eq!(
        decide(&high, &one, &low, &integer(2), false),
        Err(AdmissionRefusal::PhaseWorse)
    );
    assert_eq!(decide(&low, &one, &high, &one, false), Err(AdmissionRefusal::CodeWorse));
    assert_eq!(
        decide(&low, &one, &low, &rat(1, 2), false),
        Err(AdmissionRefusal::EqualEndpoints)
    );
    assert_eq!(
        decide(&interval(integer(1), integer(3)), &one, &interval(integer(2), integer(4)), &one, false),
        Err(AdmissionRefusal::Overlap)
    );
    // Touching endpoints are not separated.
    assert_eq!(
        decide(&interval(integer(2), integer(3)), &one, &low, &one, false),
        Err(AdmissionRefusal::Overlap)
    );
    assert_eq!(decide(&low, &one, &low, &one, true), Err(AdmissionRefusal::Unchanged));
    assert_eq!(decide(&low, &one, &low, &integer(2), true), Err(AdmissionRefusal::PhaseWorse));
    // On faces: (0, −2) has Z = 5/4 against (0, −1)'s 3/2, so log₂(5/4) < log₂(3/2) strictly, with
    // the same phases; and the target's phase 1/4 in place of 1/2 keeps every cell.
    let producing = producing_station();
    let sharper = station(vec![integer(0), integer(1), integer(-2), integer(0)]);
    let aligned = station(vec![integer(0), rat(1, 2), integer(-1), integer(0)]);
    assert_eq!(admit(&producing, &sharper), Ok(Admitted::Classical));
    assert_eq!(
        admit(&sharper, &producing),
        Err(LandingRefusal::Admission(AdmissionRefusal::CodeWorse))
    );
    assert_eq!(aligned.excess(), rat(1, 32));
    assert_eq!(admit(&producing, &aligned), Ok(Admitted::Phase));
    assert_eq!(
        admit(&aligned, &producing),
        Err(LandingRefusal::Admission(AdmissionRefusal::PhaseWorse))
    );
    assert_eq!(
        admit(&producing, &producing_station()),
        Err(LandingRefusal::Admission(AdmissionRefusal::Unchanged))
    );
}

// -------------------------------------------------------------------------------------------
// the issue site and the binding

/// A received opening issues no candidate, and the comparison and deposit are exactly
/// `compare_contacts`'s on the same Word.
#[test]
fn a_received_opening_issues_no_candidate() {
    let field = field();
    let theta = contact_material(&field);
    let current = Current::at_rest(&field);
    let targets = encoded(&field, &[0, 1, 3]);
    let compared = vec![false, false, true];
    let (_, word) = opened(&field, &theta, &current, &[0, 1]);
    let (_, ended) = opened(&field, &theta, &current, &[0, 1]);
    let received = WordOpening::Received {
        carry: ended.reception_end().unwrap(),
        absorption: Absorption::Nothing,
    };
    let (ratio, returned, landing) = word
        .compare_contacts_landing(0, &targets, &compared, &received)
        .unwrap();
    assert!(landing.declared.is_none() && landing.candidate.is_none());
    assert_eq!(landing.outcome.err(), Some(LandingRefusal::ReceivedOpening));
    let (_, plain) = opened(&field, &theta, &current, &[0, 1]);
    let (plain_ratio, plain_returned) = plain.compare_contacts(0, &targets, &compared).unwrap();
    assert_eq!(ratio, plain_ratio);
    assert_eq!(
        returned.deposit.into_present(),
        plain_returned.deposit.into_present()
    );
}

/// A binding-law fixture: an admission built from the cut's own bindings (the certified exponents
/// declared, the producing ratio as the candidate's, `Phase` claimed). Its decision does not
/// re-read (the witness holds with `X′ = X`, `Unchanged`), so it is refused at the decision unless a
/// binding refuses first. It exercises the binding; it is never an admission.
fn forged(field: &Field, theta: &Constitution, current: &Current, issued: &Issued) -> FiniteDecrease {
    let spans = spans(field, theta, current, &issued.deposit);
    let (_, certified) = theta
        .deposited_with_contact_spans(&issued.deposit, &spans)
        .unwrap();
    let declared = DeclaredExponents::certified(&certified);
    let (successor, publication, committed) = theta
        .deposited_with_contact_spans_at(&issued.deposit, &spans, &declared)
        .unwrap()
        .unwrap();
    FiniteDecrease {
        producing: theta.clone(),
        source: Arc::clone(&issued.moment),
        opening: WordOpening::Rest,
        support: issued.cut.opening_support().to_vec(),
        change: issued.cut.change().clone(),
        opened_at: 0,
        next_tick: issued.cut.next_tick(),
        deposit: issued.deposit.clone(),
        receiver: 0,
        declaration: receiver(),
        targets: issued.targets.clone(),
        compared: issued.compared.clone(),
        ratio: issued.ratio.clone(),
        candidate: LandingCandidate {
            declared,
            theta: successor,
            publication,
            committed,
            ratio: issued.ratio.clone(),
            support: issued.cut.opening_support().to_vec(),
            end: issued.cut.change().clone(),
            tick: issued.cut.next_tick(),
        },
        admitted: Admitted::Phase,
    }
}

/// Continue a fresh cut of 0279 with an admission modified by `change`, and return its refusal.
fn refused(
    field: &Field,
    theta: &Constitution,
    current: &Current,
    change: impl FnOnce(&mut FiniteDecrease, &Issued),
) -> Option<LandingRefusal> {
    let issued = issued(field, theta, current);
    let mut admission = forged(field, theta, current, &issued);
    change(&mut admission, &issued);
    let Issued {
        moment,
        cut,
        deposit,
        ..
    } = issued;
    cut.continue_admitted(field, current, &moment, &deposit, &admission, &mut Charts::new())
        .err()
}

#[test]
fn an_admission_binds_its_own_cut_by_equality() {
    let field = field();
    let theta = contact_material(&field);
    let current = Current::at_rest(&field);
    let binding = |refusal| Some(LandingRefusal::Binding(refusal));
    // Every binding equal: the forged decision is what refuses.
    assert_eq!(
        refused(&field, &theta, &current, |_, _| {}),
        binding(BindingRefusal::Decision)
    );
    // A different θ′ with the same commit counter: the certified exponents with one family a step
    // lower move the same commit to different carries.
    assert_eq!(
        refused(&field, &theta, &current, |admission, issued| {
            let spans = spans(&field, &theta, &current, &issued.deposit);
            let (_, certified) = theta
                .deposited_with_contact_spans(&issued.deposit, &spans)
                .unwrap();
            let (first, _) = certified.steps.first().expect("a certified family").clone();
            let lower = DeclaredExponents::declare(certified.steps.iter().enumerate().map(
                |(index, (l, r))| {
                    let k = r.step.exponent - i64::from(index == 0);
                    ((*l, r.family), k)
                },
            ));
            let (other, _, _) = theta
                .deposited_with_contact_spans_at(&issued.deposit, &spans, &lower)
                .unwrap()
                .unwrap();
            assert_eq!(first, Locus::Channel(0));
            assert_eq!(other.commit(), admission.candidate.theta.commit());
            assert_ne!(other, admission.candidate.theta);
            admission.candidate.theta = other;
        }),
        binding(BindingRefusal::Candidate)
    );
    // A different producing θ.
    assert_eq!(
        refused(&field, &theta, &current, |admission, _| {
            admission.producing = admission.candidate.theta.clone();
        }),
        binding(BindingRefusal::Producing)
    );
    // A different Arc with the same moment value.
    assert_eq!(
        refused(&field, &theta, &current, |admission, issued| {
            admission.source = Arc::new((*issued.moment).clone());
        }),
        binding(BindingRefusal::Source)
    );
    // Different targets, and a different mask.
    assert_eq!(
        refused(&field, &theta, &current, |admission, _| {
            admission.targets = encoded(&field, &[0, 1, 2]);
        }),
        binding(BindingRefusal::Targets)
    );
    assert_eq!(
        refused(&field, &theta, &current, |admission, _| {
            admission.compared = vec![false, true, true];
        }),
        binding(BindingRefusal::Mask)
    );
    // A foreign cut: the same comparison issued by `compare_contacts`, which binds no landing.
    let issued_here = issued(&field, &theta, &current);
    let admission = forged(&field, &theta, &current, &issued_here);
    let (moment, word) = opened(&field, &theta, &current, &[0, 1]);
    let (_, returned) = word
        .compare_contacts(0, &issued_here.targets, &issued_here.compared)
        .unwrap();
    let foreign = returned.forward.into_present().unwrap();
    let deposit = returned.deposit.into_present().unwrap();
    assert_eq!(
        foreign
            .continue_admitted(&field, &current, &moment, &deposit, &admission, &mut Charts::new())
            .err(),
        binding(BindingRefusal::ForeignCut)
    );
}

/// A post-admission refusal never consumes the cut. The binding-law admission (`forged`) is given a
/// candidate ratio that compares no station, so its code is the point 0 and its excess 0: with the
/// producing code's lower endpoint positive, `upper(L′) = 0 < lower(L)` and `X′ = 0 ≤ X`, and the
/// decision re-reads as `Classical`. Its candidate end has the wrong shape, so the prepared
/// continuation runs every law at θ′ and refuses at `e` with the native shape refusal, typed as the
/// post-admission `Continuation`; the certified continuation then runs on the same cut and
/// publishes the certified successor, with no `e`.
#[test]
fn a_post_admission_refusal_keeps_the_cut_for_the_certified_continuation() {
    let field = field();
    let theta = contact_material(&field);
    let current = Current::at_rest(&field);
    let issued = issued(&field, &theta, &current);
    let mut admission = forged(&field, &theta, &current, &issued);
    let code = issued.ratio.code_length().unwrap();
    assert!(
        code.lower.is_positive(),
        "the producing comparison is not certain at its compared station"
    );
    let none = HolonRatio::compare_partition(
        issued.ratio.faces().clone(),
        &[0, 0, 0],
        &TargetPhases {
            branch: BigInt::zero(),
            phases: vec![Rat::zero(); 3],
        },
        &[false, false, false],
    )
    .unwrap();
    assert_eq!(none.code_length().unwrap(), ExactInterval::point(Rat::zero()));
    assert_eq!(none.excess(), Rat::zero());
    assert_eq!(admit(&issued.ratio, &none), Ok(Admitted::Classical));
    admission.candidate.ratio = none;
    admission.admitted = Admitted::Classical;
    admission.candidate.end = EndChange::default();
    let spans = spans(&field, &theta, &current, &issued.deposit);
    let (native, reading) = theta
        .deposited_with_contact_spans(&issued.deposit, &spans)
        .unwrap();
    let Issued {
        moment,
        cut,
        deposit,
        ..
    } = issued;
    let mut charts = Charts::new();
    let refusal = cut
        .prepare_admitted(&field, &current, &moment, &deposit, &admission, &charts)
        .err();
    assert_eq!(
        refusal,
        Some(LandingRefusal::Continuation {
            admitted: Admitted::Classical,
            reason: HnnError::Shape {
                what: "a landing difference reads two ends of one field at one pump phase",
                expected: 0,
                found: 1,
            },
        })
    );
    let (successor, returned) = cut
        .continue_deposited(&field, &current, &moment, &deposit, &mut charts)
        .unwrap();
    assert_eq!(successor, native, "the certified continuation runs on the same cut");
    assert_eq!(returned.deposit.present(), Some(&reading));
    assert!(returned.receipt.landing.is_none());
}

/// 0279's own landing, read whole: the outcome is a measurement. Admitted, the admission's own
/// readings re-read and its continuation carries `e` at the cut's tick; refused, the refusal is
/// typed and the certified continuation is today's.
#[test]
fn the_landing_on_0279_is_a_measured_outcome() {
    let field = field();
    let theta = contact_material(&field);
    let current = Current::at_rest(&field);
    let issued = issued(&field, &theta, &current);
    println!(
        "0279 landing: declared={:?} outcome={:?}",
        issued.landing.declared,
        issued.landing.outcome.as_ref().map(FiniteDecrease::admitted)
    );
    let Issued {
        moment,
        cut,
        deposit,
        landing,
        ratio,
        ..
    } = issued;
    let next_tick = cut.next_tick();
    match &landing.outcome {
        Ok(admission) => {
            let candidate = landing.candidate.as_ref().expect("an admitted candidate was read");
            assert_eq!(candidate, admission.candidate());
            assert_eq!(admission.ratio(), &ratio);
            assert_eq!(admit(&ratio, candidate.ratio()), Ok(admission.admitted()));
            assert_eq!(candidate.tick(), next_tick);
            // As the W0 flow does: prepare the admitted continuation without consuming the cut.
            match cut.prepare_admitted(&field, &current, &moment, &deposit, admission, &Charts::new())
            {
                Ok(prepared) => {
                    let (successor, returned) = cut.finish(prepared, &mut Charts::new());
                    assert_eq!(&successor, candidate.theta());
                    let receipt = returned.receipt;
                    let difference = receipt.landing.expect("the admitted continuation reads e");
                    assert_eq!(difference.tick, next_tick);
                    println!("0279 landing e={:?}", difference.difference);
                }
                // The admission binds its own cut, so only a law of the continuation at θ′ (the
                // held law, a shape or work check) can refuse here: the typed post-admission
                // refusal, a measurement, never retried; the same cut continues certified.
                Err(refusal) => {
                    assert!(
                        matches!(refusal, LandingRefusal::Continuation { .. }),
                        "an admission issued on this cut binds it: {refusal:?}"
                    );
                    println!("0279 admitted continuation refused after admission: {refusal:?}");
                    let spans = spans(&field, &theta, &current, &deposit);
                    let (native, _) = theta.deposited_with_contact_spans(&deposit, &spans).unwrap();
                    let (successor, returned) = cut
                        .continue_deposited(&field, &current, &moment, &deposit, &mut Charts::new())
                        .unwrap();
                    assert_eq!(successor, native, "the same cut continues on the certified step");
                    assert!(returned.receipt.landing.is_none());
                }
            }
        }
        Err(refusal) => {
            println!("0279 landing refused: {refusal:?}");
            let spans = spans(&field, &theta, &current, &deposit);
            let (native, _) = theta.deposited_with_contact_spans(&deposit, &spans).unwrap();
            let (successor, returned) = cut
                .continue_deposited(&field, &current, &moment, &deposit, &mut Charts::new())
                .unwrap();
            assert_eq!(successor, native, "a refused landing continues on the certified step");
            assert!(returned.receipt.landing.is_none());
        }
    }
}
