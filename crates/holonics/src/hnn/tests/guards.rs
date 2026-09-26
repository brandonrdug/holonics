//! The forward guards of design (g) at run time. Their type constructions are `compile_fail`
//! doctests on the types themselves: a rotation transport has no ingest port ([`SourceMoment`]); a
//! word is not `Clone` and its field has no lifetime ([`Word`]); a current has no wave or contact
//! field and no lifetime ([`Current`]), and a word only borrows it, so no change outlives its word
//! (guards 2 and 16: the borrow checker and the type's fields are the proof, and no run-time test
//! adds to them); a ring has no exponent ([`RingDeclaration`]). Guard 12 (no float in a law) is
//! `#![deny(clippy::float_arithmetic)]` on `hnn`, with every value a `Rat` or an exact integer.
//!
//! [`SourceMoment`]: crate::hnn::SourceMoment
//! [`Word`]: crate::hnn::Word
//! [`Current`]: crate::hnn::Current
//! [`RingDeclaration`]: crate::hnn::RingDeclaration

use super::support::Draw;
use crate::hnn::HnnError;
use crate::hnn::field::{Current, Field};
use crate::hnn::moment::{SourceMoment, capacity};
use crate::hnn::receiving::GrainCell;
use crate::ratio::{Rat, rat};

/// Guard 1: the moment is sized once from the field, and ingest never grows it (on the chain
/// control: ring 0's two phases, each `|A|` phase counts and `|A|²` offset counts, and the offset
/// window); `log₂N(n)` per source bit is at least 1 below `n*` and below 1 past it (the count, not
/// one slot's bits). The refusal of a population below `n*` is the field's own law
/// (`tests/field.rs`, `a_population_below_capacity_is_refused`).
#[test]
fn guard_one_the_moment_is_sized_once_and_lossy_past_its_capacity() {
    let field = chain();
    let mut current = Current::at_rest(&field);
    let mut moment = SourceMoment::open(&field, &current);
    let sized = |moment: &SourceMoment| {
        (0..2)
            .map(|phase| {
                moment.phase_counts(0, phase).unwrap().len()
                    + moment.offset_counts(0, 1, phase).unwrap().len()
            })
            .sum::<usize>()
            + moment.window().len()
    };
    let before = sized(&moment);
    let mut draw = Draw::new(71);
    let cells: Vec<usize> = (0..64).map(|_| draw.below(4)).collect();
    let mut fed = 0;
    while fed < cells.len() {
        fed += moment
            .ingest(&field, &mut current, &cells[fed..])
            .unwrap()
            .cells;
    }
    assert_eq!(sized(&moment), before);
    assert_eq!(before, 2 * (4 + 4 * 4) + 1);
    let control = capacity(&[3, 4, 5], &[0, 1, 2], 2, &[]).unwrap();
    for n in [2u64, 64, 136, 137, 512, 4096] {
        let per_source_bit_below_one = control.state_bits(n) <= n;
        assert_eq!(per_source_bit_below_one, n >= 137, "n = {n}");
    }
}

/// Guard 9: the codec is not the architecture. Changing the exterior alphabet leaves the ring count
/// and widths, the contacts and the complex unchanged; it moves only the capacity.
#[test]
fn guard_nine_the_alphabet_does_not_fix_the_architecture() {
    let bytes = chain();
    let mut declared = chain_declaration(1 << 20);
    declared.alphabet = 2;
    let bits = Field::declare(declared).unwrap();
    let widths = |field: &Field| field.rings().iter().map(|r| r.width()).collect::<Vec<_>>();
    let channels = |field: &Field| {
        field
            .contacts()
            .iter()
            .map(|c| c.width())
            .collect::<Vec<_>>()
    };
    assert_eq!(widths(&bits), widths(&bytes));
    assert_eq!(channels(&bits), channels(&bytes));
    assert_eq!(bits.complex(), bytes.complex());
    assert_ne!(bits.capacity().n_star(), bytes.capacity().n_star());
}

/// Guard 15: the only grain reading returns the carry, the phase class and the fibre, and the value
/// is recovered from them exactly; nothing is committed.
#[test]
fn guard_fifteen_the_grain_reading_rounds_nothing() {
    let mut draw = Draw::new(73);
    for _ in 0..50 {
        let value = draw.rational() * rat(97, 13) + draw.rational();
        let cell = GrainCell::of(&value, 16);
        assert_eq!(cell.representative(16) + &cell.fibre, value);
        assert!(cell.fibre >= Rat::from_integer(0.into()));
    }
}

// -------------------------------------------------------------------------------------------
// the learning half's guards: no journal, no path from refine to the constitution, the collapse
// only at the carry-out, and the budget refused, never rounded. Their type constructions are
// `compile_fail` doctests: a constitution has no journal field (`Constitution`); a pending ratio
// takes no face and has no lifetime (`PendingRatio`); the return accepts only a covector a Holon
// ratio built (`Word::pull_back`, `RatioCovector`); a port return has no lifetime (`InteractionReturn`).

use super::learning::{OPEN_BUDGET, chain, chain_declaration, generic};
use crate::hnn::constitution::{
    Constitution, FactorGradient, FactorStep, HarmonicStep, LinearLocus, LinearStep, Locus, Sample,
    Steps,
};
use crate::hnn::field::ConstitutionRead;
use crate::hnn::port::{Deposit, ExecutionPort};
use crate::hnn::reference::{Reference, one_hot};
use crate::ratio::linear::ExactRatMatrix;
use num_traits::{One, Zero};

/// Guard 4: the constitution holds the current parameters and their statistics, never a list of
/// deposits. Three deposits whose every update is zero, one naming no step, one naming every
/// linear locus with zero-feature samples and every factor family with a zero direction, and one
/// naming them with zero-weight samples, leave three constitutions equal field by field (the
/// derived equality reads every private field): each is the initial one advanced three commits,
/// with no trace of which steps its deposits named.
#[test]
fn guard_four_the_constitution_keeps_no_journal() {
    let field = chain();
    let initial = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET).unwrap();
    let zero = |rows: usize, columns: usize| vec![vec![Rat::zero(); columns]; rows];
    let zeros = |n: usize| vec![Rat::zero(); n];
    let matrix = |rows: usize, columns: usize| ExactRatMatrix::zero(rows, columns).unwrap();
    let named = |weight: Rat, feature: Rat| -> (Vec<LinearStep>, Vec<FactorStep>) {
        let sample = |features: usize, covectors: usize| Sample {
            weight: weight.clone(),
            feature: vec![feature.clone(); features],
            covector: vec![Rat::one(); covectors],
            target: None,
        };
        let alphabet = field.alphabet();
        let mut linear = vec![
            LinearStep {
                locus: LinearLocus::SourcePort(0),
                samples: vec![sample(alphabet, field.ring(0).width())],
            },
            LinearStep {
                locus: LinearLocus::Receiving(2),
                samples: vec![Sample {
                    target: Some(zeros(2 * alphabet)),
                    ..sample(field.ring(2).width(), 2 * alphabet)
                }],
            },
        ];
        let mut factors = Vec::new();
        for g in 0..field.rings().len() {
            let n = field.ring(g).width();
            linear.push(LinearStep {
                locus: LinearLocus::Contrast(g),
                samples: vec![sample(n, n)],
            });
            let passive = initial.passive_factor(g);
            for gradient in [
                FactorGradient::Passive {
                    ring: g,
                    gradient: matrix(passive.rows(), passive.columns()),
                },
                FactorGradient::Slices {
                    ring: g,
                    gradient: vec![(zeros(n), zeros(n)); n],
                },
                FactorGradient::Standing {
                    ring: g,
                    gradient: zeros(n),
                },
            ] {
                factors.push(FactorStep {
                    gradient,
                    energy: Rat::zero(),
                });
            }
        }
        let pair = initial.pair_port(0, 1).unwrap();
        factors.push(FactorStep {
            gradient: FactorGradient::PairPort {
                ring: 0,
                offset: 1,
                outputs: zero(pair.rank(), field.ring(0).width()),
                current: zero(pair.rank(), alphabet),
                earlier: zero(pair.rank(), alphabet),
            },
            energy: Rat::zero(),
        });
        for a in 0..field.contacts().len() {
            let k = field.contact(a).width();
            for gradient in [
                FactorGradient::Storage {
                    contact: a,
                    gradient: matrix(k, k),
                },
                FactorGradient::Stiffness {
                    contact: a,
                    gradient: matrix(k, k),
                },
                FactorGradient::Dissipation {
                    contact: a,
                    gradient: matrix(k, k),
                },
            ] {
                factors.push(FactorStep {
                    gradient,
                    energy: Rat::zero(),
                });
            }
        }
        (linear, factors)
    };
    let run = |steps: &dyn Fn() -> (Vec<LinearStep>, Vec<FactorStep>)| {
        let mut theta = initial.clone();
        for _ in 0..3 {
            let (linear, factors) = steps();
            let harmonic = HarmonicStep {
                ring: 2,
                gradient: vec![Rat::zero(); field.ring(2).width()],
                energy: Rat::zero(),
            };
            let deposit = Deposit::new(theta.commit(), linear, factors, Vec::new())
                .with_harmonic(vec![harmonic]);
            let (next, reading) = theta.deposited(&deposit).unwrap();
            assert!(reading.released.is_empty() && reading.stepped == 0);
            theta = next;
        }
        theta
    };
    let empty = run(&|| (Vec::new(), Vec::new()));
    let unfed = run(&|| named(Rat::one(), Rat::zero()));
    let unweighted = run(&|| named(Rat::zero(), Rat::one()));
    assert_eq!(empty.commit(), 3);
    assert_eq!(unfed, empty);
    assert_eq!(unweighted, empty);
    assert_eq!(empty.bits_by_locus(), initial.bits_by_locus());
    assert!(empty.carried_remainders().is_empty());
}

/// Guard 11: `refine` has no path to the constitution and `compare` only stages; the constitution,
/// the standings included, changes only by `deposit`.
#[test]
fn guard_eleven_refine_and_compare_leave_the_constitution() {
    let field = chain();
    let reference = Reference::campaign_one();
    let mut resident = reference
        .mount_with(&field, &Current::at_rest(&field), generic(&field, 92))
        .unwrap();
    let published = resident.constitution().clone();
    let (moment, _) = reference
        .ingest(&mut resident, None, &one_hot(&[2, 2, 1]))
        .unwrap();
    let phases = resident.admitted()[0].clone();
    reference.refine(&mut resident, &moment, &phases).unwrap();
    let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    assert_eq!(resident.constitution(), &published);
    reference
        .compare(&mut resident, pending, &one_hot(&[1, 2]))
        .unwrap();
    assert_eq!(resident.constitution(), &published);
}

/// Guard 5: the collapse runs only at the joint clock's carry-out.
#[test]
fn guard_five_the_collapse_runs_only_at_the_carry_out() {
    let field = chain();
    let reference = Reference::campaign_one();
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let admitted = resident.admitted().to_vec();
    assert_eq!(
        reference.close_aeon(&mut resident, &admitted).unwrap_err(),
        HnnError::NotAtCarryOut
    );
    reference
        .ingest(&mut resident, None, &one_hot(&[1, 3]))
        .unwrap();
    assert_eq!(
        reference.close_aeon(&mut resident, &admitted).unwrap_err(),
        HnnError::NotAtCarryOut
    );
}

/// Guard 15: a successor over the budget is a typed refusal that names the loci that grew; the
/// predecessor is untouched and nothing is rounded to fit.
#[test]
fn guard_fifteen_the_budget_is_refused_never_rounded() {
    let field = chain();
    let loose = generic(&field, 93);
    let budget = loose.exact_bits();
    let theta = Constitution::initial(&field, Steps::campaign_one(), budget)
        .unwrap()
        .with_channel(
            0,
            loose.contact_storage(0).clone(),
            loose.contact_stiffness(0).clone(),
            loose.contact_dissipation(0).clone(),
        )
        .unwrap();
    let k = field.contact(0).width();
    let mut draw = Draw::new(94);
    let deposit = Deposit::new(
        0,
        Vec::new(),
        vec![FactorStep {
            gradient: FactorGradient::Storage {
                contact: 0,
                gradient: draw.matrix(k, k).scaled(&rat(1, 997)),
            },
            energy: rat(3, 7),
        }],
        Vec::new(),
    );
    let generous = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET)
        .unwrap()
        .with_channel(
            0,
            loose.contact_storage(0).clone(),
            loose.contact_stiffness(0).clone(),
            loose.contact_dissipation(0).clone(),
        )
        .unwrap();
    let (grown, _) = generous.deposited(&deposit).unwrap();
    assert!(grown.exact_bits() > theta.exact_bits());
    let tight = Constitution::initial(&field, Steps::campaign_one(), theta.exact_bits())
        .unwrap()
        .with_channel(
            0,
            loose.contact_storage(0).clone(),
            loose.contact_stiffness(0).clone(),
            loose.contact_dissipation(0).clone(),
        )
        .unwrap();
    let before = tight.clone();
    match tight.deposited(&deposit) {
        Err(HnnError::ConstitutionBudget {
            bits,
            budget,
            commit,
            loci,
        }) => {
            assert!(bits > budget);
            assert_eq!(commit, 0);
            assert_eq!(loci[0], Locus::Channel(0));
        }
        other => panic!("a typed refusal: {other:?}"),
    }
    assert_eq!(tight, before);
    let _ = budget;
}
