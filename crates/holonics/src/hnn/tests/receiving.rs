//! The receiving phases: the grain derived from the receiver, the observability refusal, the exact
//! grain reading and its integer comparison; the receiving parametron's landmark tree declared from
//! the receiver and coded in the description; the active suffix address and each phase's causal
//! address; the combined read of the tree's face and the wave through `R P_R^(τ_R)`; the compare's
//! landmark steps and their deposit; and the maps' openings (Decision 28: `R_0 = 0`, `E_0` the sign
//! generator times ½), with the deadlock they avoid.

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use super::learning::{OPEN_BUDGET, chain, chain_declaration, moment, phases};
use super::support::{Draw, Medium, Parts, lift, small_field};
use crate::hnn::HnnError;
use crate::hnn::constitution::{CAMPAIGN_ONE_BUDGET, Constitution, Locus, Steps};
use crate::hnn::field::{ConstitutionRead, Current, Field, FieldDeclaration, ReceiverDeclaration};
use crate::hnn::landmark::{Landmarks, Letter, Widths, address};
use crate::hnn::pending::PendingRatio;
use crate::hnn::port::{ExecutionPort, Handle, ReceiptDetail};
use crate::hnn::ratio::{HolonRatio, log2_enclosure, target_phases};
use crate::hnn::receiving::{
    ActiveAddress, GrainCell, ReceivingPhases, ReceivingRead, grain_exponent, grain_logits,
    landmark_declaration, tree_code_length,
};
use crate::hnn::reference::{Reference, compose, one_hot};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer, rat};

/// `L_R = ⌈1/ε_bits⌉` (R2 M2): the chain control's tolerance of 1/16 bit (campaign 1's) gives 16,
/// and 3/40 gives 14; the first epoch is the front's hop distance, and the observability rank is
/// reported and covers `A`.
#[test]
fn the_grain_is_derived_from_the_receivers_code_tolerance() {
    let field = &chain();
    let medium = Medium::initial(field, 4);
    let current = Current::at_rest(field);
    let phases = ReceivingPhases::declare(field, &medium, &current, &field.receivers()[0]).unwrap();
    assert_eq!(phases.grain(), 16);
    assert_eq!(phases.first_epoch(), 2);
    assert_eq!(phases.epochs(), 2..4);
    assert_eq!(phases.depth(), 2);
    assert!(phases.rank() >= phases.aperture());
    let coarse = ReceiverDeclaration {
        ring: 2,
        aperture: 2,
        tolerance: rat(3, 40),
        depth: 2,
    };
    assert_eq!(
        ReceivingPhases::declare(field, &medium, &current, &coarse)
            .unwrap()
            .grain(),
        14
    );
    let none = ReceiverDeclaration {
        tolerance: Rat::zero(),
        ..coarse
    };
    assert!(matches!(
        ReceivingPhases::declare(field, &medium, &current, &none),
        Err(HnnError::Tolerance { .. })
    ));
}

/// Review C7: an aperture beyond the receiving ring's observability rank over the word is refused,
/// and the rank is reported. A period-2 source ring injects at most 4 directions.
#[test]
fn an_aperture_beyond_the_observability_rank_is_refused() {
    let field = small_field(&[2, 3], vec![super::support::contact(0, 1, 1, 0)], 1);
    let medium = Medium::generic(&field, 7, Parts::default());
    let current = Current::at_rest(&field);
    let wide = ReceiverDeclaration {
        ring: 1,
        aperture: 5,
        tolerance: rat(1, 16),
        depth: 2,
    };
    match ReceivingPhases::declare(&field, &medium, &current, &wide) {
        Err(HnnError::Observability { aperture, rank }) => {
            assert_eq!(aperture, 5);
            assert!(rank <= 4);
        }
        other => panic!("expected an observability refusal, found {other:?}"),
    }
}

/// Guard 15, and Lean `HNN/Ratio.face_constant_on_fibre`: an exponent read at a grain is its carry,
/// its phase class and its fibre, exactly, with `0 ≤ ε < 1/L`; reading it down to its cell's
/// representative moves it by less than `1/L`, and every value of a cell has one representative.
#[test]
fn the_grain_reading_is_a_carry_a_phase_class_and_a_fibre() {
    let values = [
        rat(-37, 7),
        rat(5, 3),
        integer(-2),
        rat(1, 16),
        rat(-1, 1000),
        Rat::zero(),
    ];
    for value in &values {
        for grain in [1u64, 2, 16, 7] {
            let cell = GrainCell::of(value, grain);
            let grain_rat = Rat::from_integer(BigInt::from(grain));
            assert!(cell.phase < grain);
            assert!(cell.fibre >= Rat::zero() && cell.fibre < grain_rat.recip());
            assert_eq!(cell.representative(grain) + &cell.fibre, *value);
            assert!(value - cell.representative(grain) < grain_rat.recip());
            let inside = cell.representative(grain) + &cell.fibre / integer(2);
            assert_eq!(
                GrainCell::of(&inside, grain).representative(grain),
                cell.representative(grain)
            );
        }
    }
    let cell = GrainCell::of(&rat(-37, 7), 16);
    assert_eq!(cell.carry, BigInt::from(-6));
    assert_eq!(cell.phase, 11);
}

/// `2^k ≤ p^L < 2^(k+1)`, checked over ℚ.
fn brackets(p: &Rat, grain: u64, k: &BigInt) -> bool {
    let mut read = Rat::one();
    for _ in 0..grain {
        read *= p;
    }
    let two = |k: &BigInt| {
        let magnitude = usize::try_from(k.magnitude().clone()).unwrap();
        let value = Rat::from_integer(BigInt::one() << magnitude);
        if k.sign() == num_bigint::Sign::Minus {
            value.recip()
        } else {
            value
        }
    };
    two(k) <= read && read < two(&(k + 1))
}

fn grain_of(p: &Rat, grain: u64) -> BigInt {
    grain_exponent(
        &p.numer().to_biguint().unwrap(),
        &p.denom().to_biguint().unwrap(),
        grain,
    )
    .unwrap()
}

/// Lean `HNN/RegionCounts.{grainExponent_spec, grain_log_iff_pow_bounds, grain_face_residual,
/// grain_fixture}`: the grain exponent is the unique `k` with `2^k ≤ (a/b)^L < 2^(k+1)`, from integer
/// comparisons, and `k/L ≤ log₂(a/b) < (k+1)/L`; at `L = 1` it is `⌊log₂(a/b)⌋`; an exact power of
/// two reads its own exponent; `5/8 → −11`, `3/8 → −23` at `L = 16`; a zero is refused.
#[test]
fn the_grain_exponent_is_the_integer_comparison() {
    for p in [
        rat(5, 8),
        rat(3, 8),
        rat(1, 1),
        rat(1, 256),
        rat(3, 7),
        rat(255, 256),
        rat(1, 3),
        rat(9, 2),
        rat(1023, 1025),
    ] {
        for grain in [1u64, 2, 7, 16] {
            let k = grain_of(&p, grain);
            assert!(brackets(&p, grain, &k), "{p} at {grain}");
            let log = log2_enclosure(&p).unwrap();
            let grain_rat = Rat::from_integer(BigInt::from(grain));
            assert!(Rat::from_integer(k.clone()) / &grain_rat <= log.upper);
            assert!(log.lower < Rat::from_integer(&k + 1) / &grain_rat);
        }
    }
    assert_eq!(grain_of(&rat(1, 256), 16), BigInt::from(-128));
    assert_eq!(grain_of(&rat(9, 2), 1), BigInt::from(2));
    assert_eq!(grain_of(&rat(5, 8), 16), BigInt::from(-11));
    assert_eq!(grain_of(&rat(3, 8), 16), BigInt::from(-23));
    assert!(grain_exponent(&BigUint::zero(), &BigUint::one(), 16).is_err());
}

/// **The active suffix address and each phase's causal address** (module header of
/// `hnn::receiving`): the register shifted at every cell holds the last `D` cells newest first,
/// `Boundary` before the first; at a window opening at `p` with its targets known, phase `j`'s
/// address is `hnn::landmark::address(cells, p + j, D)` exactly, so no two phases of a window pool
/// their lags; with no target known (a release) every phase reads the opening address.
#[test]
fn the_phase_address_is_the_trees_causal_address() {
    let mut draw = Draw::new(71);
    let cells: Vec<usize> = (0..40).map(|_| draw.below(5)).collect();
    for depth in [0usize, 1, 3, 4] {
        for aperture in [1usize, 2, 3] {
            let mut register = ActiveAddress::boundary(depth);
            let mut p = 0;
            while p + aperture <= cells.len() {
                let targets = &cells[p..p + aperture];
                for j in 0..aperture {
                    assert_eq!(
                        register.phase(targets, j),
                        address(&cells, p + j, depth),
                        "depth {depth}, aperture {aperture}, cell {}",
                        p + j
                    );
                    assert_eq!(register.phase(&[], j), address(&cells, p, depth));
                }
                for &cell in targets {
                    register.receive(cell);
                }
                p += aperture;
            }
            assert_eq!(register.letters(), address(&cells, p, depth).as_slice());
        }
    }
    let mut register = ActiveAddress::boundary(3);
    register.receive(7);
    assert_eq!(
        register.letters(),
        &[Letter::Cell(7), Letter::Boundary, Letter::Boundary]
    );
    assert_eq!(register.truncated(1).unwrap().letters(), &[Letter::Cell(7)]);
    assert!(register.truncated(4).is_err());
    // Three letters over 256 cells and the boundary: 9 bits each.
    assert_eq!(register.bits(256), 27);
}

/// **The receiver declares its tree, and the field codes it** (guard 13): the tree's declaration
/// is the field's `|A|` and population, the receiver's depth and grain, the cell emitted as its odometer digits, with
/// no forced split; campaign 1 declares `D = 4`, and at `n* = 6,148 = 2²·29·53`, `L_R = 16`, `B = 8`
/// the owner derives the path lattice `M_p = 39` and the β carrier `W = 28`. A change of depth changes the field's code; the initial
/// constitution carries a tree on the receiving ring only, empty, and its receiving map `R_0 = 0`
/// and source port `E_0` the declared sign generator times ½ (entries `±½`).
#[test]
fn the_field_declares_the_tree_and_codes_it() {
    let steps = Steps::campaign_one();
    let deep = chain();
    let mut shallow = chain_declaration(1 << 20);
    shallow.receivers[0].depth = 1;
    let shallow = Field::declare(shallow).unwrap();
    assert_ne!(
        deep.describe(&steps, OPEN_BUDGET, 64),
        shallow.describe(&steps, OPEN_BUDGET, 64)
    );
    let campaign = Field::declare(FieldDeclaration::campaign_one(6_148)).unwrap();
    assert_eq!(campaign.receivers()[0].depth, 4);
    assert_eq!(campaign.capacity().n_star(), 6_148);
    let declared = landmark_declaration(&campaign, &campaign.receivers()[0]).unwrap();
    assert_eq!(
        (declared.alphabet, declared.depth, declared.forced),
        (256, 4, 0)
    );
    assert_eq!((declared.population, declared.grain), (6_148, 16));
    let widths = Widths::derived(&declared);
    assert_eq!((widths.digits, widths.face, widths.carrier), (8, 39, 28));
    let theta = Constitution::initial(&campaign, steps, CAMPAIGN_ONE_BUDGET).unwrap();
    let tree = theta.landmarks(2).unwrap();
    assert_eq!(tree.declaration(), &declared);
    assert_eq!((tree.nodes(), tree.passed()), (0, 0));
    assert!(theta.landmarks(0).is_none());
    let map = theta.receiving_map(2).unwrap();
    assert!(map.entries().iter().all(Zero::is_zero));
    let source = theta.source_port(0).unwrap();
    assert!(
        source
            .entries()
            .iter()
            .all(|x| *x == rat(1, 2) || *x == rat(-1, 2))
    );
    assert!(source.entries().iter().any(|x| *x == rat(1, 2)));
    assert!(source.entries().iter().any(|x| *x == rat(-1, 2)));
}

/// The read is `f_j = k(a_j)/L_R + R · P_R^(τ_R) v_R` (the combined face): the wave rotated to the
/// receiving ring's phase, plus the tree face's grain logits at phase `j`'s address, read after the
/// window's earlier targets (cell order); each class's
/// real logit read at the grain, its imaginary logit (the wave's alone) halved into turns. The
/// tree logits lie on the grain, so each cell is the wave's shifted by `k_c/L_R` exactly and keeps
/// the wave's fibre; the tree's face sums to one exactly and its grain logits alone code each class
/// within one grain of `−log₂ q(c)` (`grain_code_residual`).
#[test]
fn the_read_adds_the_trees_face_to_the_rotated_wave() {
    let field = &chain();
    let mut medium = Medium::encoding(field, 12);
    // A tree that received a short passage, so its face differs from address to address; the
    // window's two cells are not yet deposited.
    let declared = landmark_declaration(field, &field.receivers()[0]).unwrap();
    let mut tree = Landmarks::new(declared).unwrap();
    let passage = [1usize, 1, 3, 0, 1, 2, 1, 1, 3, 0, 1];
    for position in 0..9 {
        tree.receive(&address(&passage, position, 2), passage[position])
            .unwrap();
    }
    medium.trees[2] = Some(tree.clone());
    // The phases are declared at rest; the read rotates by the receiving ring's phase at its cut.
    let phases = ReceivingPhases::declare(
        field,
        &medium,
        &Current::at_rest(field),
        &field.receivers()[0],
    )
    .unwrap();
    let mut register = ActiveAddress::boundary(2);
    for &cell in &passage[..9] {
        register.receive(cell);
    }
    let targets = [passage[9], passage[10]];
    let faces = phases.tree_faces(&medium, &register, &targets).unwrap();
    assert_eq!(faces.len(), 2);
    // Phase j reads the tree after the window's earlier targets (cell order).
    let mut deposited = tree.clone();
    for (j, face) in faces.iter().enumerate() {
        let here = address(&passage, 9 + j, 2);
        assert_eq!(face, &deposited.face(&here, 16).unwrap());
        deposited.deposit(&here, passage[9 + j]).unwrap();
        assert_eq!(face.probabilities.iter().sum::<Rat>(), Rat::one());
        for (class, p) in face.probabilities.iter().enumerate() {
            let code = tree_code_length(face, class).unwrap();
            let exact = log2_enclosure(&p.recip()).unwrap();
            let grain = rat(1, 16);
            assert!(code.lower < &exact.upper + &grain && exact.lower < &code.upper + &grain);
        }
    }
    assert_ne!(faces[0], faces[1], "two phases read two addresses");
    let current = Current::at(field, lift(&[0, 0, 3])).unwrap();
    let anchor = Draw::new(13).vector(4);
    let wave_read = phases.read(field, &medium, &current, &anchor).unwrap();
    let map = medium.receiving_map(2).unwrap();
    let rotated = field.ring(2).rotate(&anchor, &BigInt::from(3));
    let wave = map.apply(&rotated).unwrap();
    assert_eq!(wave_read.logits, wave);
    let stored = grain_logits(&faces[0]);
    let read = ReceivingRead::combined(wave.clone(), &faces[0], 16).unwrap();
    let combined: Vec<Rat> = wave.iter().zip(&stored).map(|(w, k)| w + k).collect();
    assert_eq!(read.logits, combined);
    assert_eq!(read.logits.len(), 2 * field.alphabet());
    for (class, cell) in read.cells.iter().enumerate() {
        assert_eq!(
            cell.representative(16) + &cell.fibre,
            read.logits[2 * class]
        );
        let alone = GrainCell::of(&wave[2 * class], 16);
        assert_eq!(cell.fibre, alone.fibre);
        assert_eq!(
            cell.representative(16),
            alone.representative(16) + &stored[2 * class]
        );
        assert_eq!(read.phases[class], &wave[2 * class + 1] / integer(2));
    }
    assert!(phases.read(field, &medium, &current, &anchor[..2]).is_err());
    // A tree face of another grain, or a register of another depth, is refused.
    let coarse = tree.face(&address(&passage, 9, 2), 8).unwrap();
    assert!(ReceivingRead::combined(wave, &coarse, 16).is_err());
    assert!(
        phases
            .tree_faces(&medium, &ActiveAddress::boundary(3), &targets)
            .is_err()
    );
}

/// **The compare deposits its targets into the tree on their own addresses** (Decision 28): the
/// compare's landmark steps are one per phase, in cell order, each at its phase's causal address;
/// the constitution's deposit applies them (the tree passes `A` cells and every face at a
/// deposited address moves toward its target), and no other locus's material carries them.
#[test]
fn the_compare_deposits_its_targets_on_their_own_addresses() {
    let field = chain();
    let theta = super::learning::generic(&field, 81);
    let (current, open) = moment(&field, 82, 9);
    let phases = phases(&field, &theta, &current);
    let mut register = ActiveAddress::boundary(2);
    for cell in [2usize, 3] {
        register.receive(cell);
    }
    let pending = PendingRatio::produce(&current, &open, &register, &phases, 0).unwrap();
    let targets = [1usize, 1];
    let (word, wave) = pending.read(&field, &theta).unwrap();
    let against = pending.against(&theta, &wave, &targets).unwrap();
    let scored = pending.scored(&theta, &against, &targets).unwrap();
    let anchors = target_phases(&field, pending.anchor(), 2, &targets).unwrap();
    let ratio = HolonRatio::compare(against.faces, &targets, &anchors).unwrap();
    let back = word
        .pull_back(
            &ratio.covector().unwrap(),
            theta.receiving_map(2).unwrap(),
            &current.lift()[2],
            &phases,
        )
        .unwrap();
    let (_, deposit) = compose(&field, &theta, &pending, &back, &targets, &scored.steps).unwrap();
    assert_eq!(deposit.mixture(), &scored.steps[..]);
    let steps = deposit.landmarks();
    assert_eq!(steps.len(), 2);
    assert_eq!(
        steps[0].address,
        vec![Letter::Cell(3), Letter::Cell(2)],
        "phase 0 reads the register"
    );
    assert_eq!(
        steps[1].address,
        vec![Letter::Cell(1), Letter::Cell(3)],
        "phase 1 reads its own lag-one cell, the window's first target"
    );
    assert!(steps.iter().all(|step| step.ring == 2 && step.class == 1));
    assert!(deposit.loci().contains(&Locus::ReceivingMap(2)));
    let before = theta
        .landmarks(2)
        .unwrap()
        .face(&steps[1].address, 16)
        .unwrap();
    let (next, reading) = theta.deposited(&deposit).unwrap();
    assert_eq!(reading.landmarks, 2);
    let tree = next.landmarks(2).unwrap();
    assert_eq!(tree.passed(), 2);
    let after = tree.face(&steps[1].address, 16).unwrap();
    assert!(after.probabilities[1] > before.probabilities[1]);
}

/// **With every map at zero the wave never learns** (the deadlock `R_0 = 0` alone would meet): with
/// `E = 0`, the pair port's outputs `e_ρ = 0` and `R = 0`, the source moment, the open and every
/// feature `f = P_R^(τ_R) v_R` are zero, so `R`'s step `G = Σ γ g fᵀ` is zero and the covector
/// `Rᵀ g` reaching every upstream locus is zero: after a compare and its deposit, `R` and `E` are
/// unchanged, and the model's face is the tree's exactly.
#[test]
fn the_wave_is_inert_when_every_map_opens_at_zero() {
    let field = chain();
    let a = field.alphabet();
    let initial = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET).unwrap();
    let silent = initial
        .with_ports(0, None, Some(ExactRatMatrix::zero(4, a).unwrap()), None)
        .unwrap();
    let reference = Reference::campaign_one();
    let mut resident = reference
        .mount_with(&field, &Current::at_rest(&field), silent)
        .unwrap();
    let mut draw = Draw::new(91);
    let cells: Vec<usize> = (0..12).map(|_| draw.below(a)).collect();
    let (moment_id, _) = reference
        .ingest(&mut resident, None, &one_hot(&cells[..6]))
        .unwrap();
    let phases = resident.admitted()[0].clone();
    let (pending, _) = reference
        .refine(&mut resident, &moment_id, &phases)
        .unwrap();
    let (staged, compared) = reference
        .compare(&mut resident, pending, &one_hot(&cells[6..8]))
        .unwrap();
    let pullback = compared.pullback.present().unwrap();
    assert!(
        pullback.rings[0]
            .source
            .as_ref()
            .unwrap()
            .entries()
            .iter()
            .all(Zero::is_zero)
    );
    assert!(pullback.receiving.1.entries().iter().all(Zero::is_zero));
    let before = resident.constitution().clone();
    reference.deposit(&mut resident, staged).unwrap();
    assert_eq!(
        resident.constitution().receiving_map(2),
        before.receiving_map(2)
    );
    assert_eq!(
        resident.constitution().source_port(0),
        before.source_port(0)
    );
    // The tree learned; the wave did not.
    assert_eq!(resident.constitution().landmarks(2).unwrap().passed(), 2);
}

/// **`R` opens at zero and learns from the first deposit** (Decision 28's declared openings): at
/// the declared initial constitution (`R_0 = 0`, `E_0` the sign generator times ½) the first
/// compare's combined face is the tree's at the grain exactly (its code length equals the tree's
/// grain face alone's), its
/// covector reaches no upstream locus (`Rᵀ g = 0`), and its deposit moves `R`; the second compare's
/// covector reaches `E`, which its deposit moves. So the first commit at which an upstream locus
/// moves is the second.
#[test]
fn r_opens_at_zero_and_learns_from_the_first_deposit() {
    let field = chain();
    let a = field.alphabet();
    let reference = Reference::campaign_one();
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let mut draw = Draw::new(92);
    let cells: Vec<usize> = (0..14).map(|_| draw.below(a)).collect();
    let (moment_id, _) = reference.ingest(&mut resident, None, &[]).unwrap();
    let phases = resident.admitted()[0].clone();
    // The cells in order, each aeon closed at the joint clock's carry-out.
    let feed = |resident: &mut crate::hnn::Resident, cells: &[usize]| {
        let mut fed = 0;
        while fed < cells.len() {
            let (_, ingested) = reference
                .ingest(resident, Some(&moment_id), &one_hot(&cells[fed..]))
                .unwrap();
            let ingested = ingested.forward.into_present().unwrap();
            fed += ingested.cells;
            if ingested.carry_out {
                let family = resident.admitted().to_vec();
                reference.close_aeon(resident, &family).unwrap();
            }
        }
    };
    feed(&mut resident, &cells[..6]);
    let window = |resident: &mut crate::hnn::Resident, at: usize| {
        let (pending, _) = reference.refine(resident, &moment_id, &phases).unwrap();
        let (staged, compared) = reference
            .compare(resident, pending, &one_hot(&cells[at..at + 2]))
            .unwrap();
        let tree = match &compared.receipt.detail {
            ReceiptDetail::Compare { tree_grain, .. } => tree_grain.clone(),
            _ => panic!("a compare's receipt"),
        };
        let holon = compared.forward.present().unwrap().clone();
        let pullback = compared.pullback.present().unwrap().clone();
        let before = resident.constitution().clone();
        reference.deposit(resident, staged).unwrap();
        feed(resident, &cells[at..at + 2]);
        (holon, tree, pullback, before)
    };
    let (holon, tree, pullback, before) = window(&mut resident, 6);
    for (phase, tree) in holon.phases().iter().zip(&tree) {
        assert_eq!(
            &phase.code_length, tree,
            "the first combined face is the tree's at the grain"
        );
    }
    let zero = |matrix: &ExactRatMatrix| matrix.entries().iter().all(Zero::is_zero);
    assert!(zero(pullback.rings[0].source.as_ref().unwrap()));
    assert!(
        !zero(&pullback.receiving.1),
        "R's own gradient is g fᵀ, f ≠ 0"
    );
    assert!(zero(before.receiving_map(2).unwrap()));
    assert!(!zero(resident.constitution().receiving_map(2).unwrap()));
    assert_eq!(
        resident.constitution().source_port(0),
        before.source_port(0),
        "the first deposit moves no upstream locus"
    );
    let (_, _, pullback, before) = window(&mut resident, 8);
    assert!(!zero(pullback.rings[0].source.as_ref().unwrap()));
    assert_ne!(
        resident.constitution().source_port(0),
        before.source_port(0),
        "the second deposit moves E"
    );
    assert_eq!(resident.constitution().commit(), 2);
    assert!(matches!(
        reference.read(&resident).unwrap().2.first(),
        Some((Handle::Moment(_), _))
    ));
}

/// A tree face of given dyadic probabilities at the grain.
fn tree_face(probabilities: &[Rat], grain: u64) -> crate::hnn::landmark::LandmarkFace {
    crate::hnn::landmark::LandmarkFace {
        grain,
        probabilities: probabilities.to_vec(),
        exponents: probabilities
            .iter()
            .map(|p| {
                grain_exponent(
                    &p.numer().to_biguint().unwrap(),
                    &p.denom().to_biguint().unwrap(),
                    grain,
                )
                .unwrap()
            })
            .collect(),
    }
}

/// **The mixture weighs the tree against the combined face, cell by cell** (ruling A; Lean
/// `HNN/LandmarkTree.{path_face_normalized, sequential_mixture, sequential_mixture_executed}`): it
/// opens at `β = 1`, `λ = 1/2`; phase `j` of a window reads the ratio after the earlier phases'
/// steps, so the window's product is `½ A + ½ B` (the tree's and the combined face's likelihoods),
/// within the steps' residuals, and a weight read before phase 0's step (`β = 1` at phase 1) is
/// excluded; each phase's code length encloses `−log₂(λ_j q_T + (1 − λ_j) q_C)` with `q_C` the
/// combined face's exact class mass, and the tree's own `−log₂ q_T` is returned beside it; the
/// steps multiply `β` by `q_T(x)/q̃_C(x)` in cell order, exactly while the odd parts fit `W`, and
/// past it the carried `β` is rebased with its drift reported; `log₂ β` is enclosed.
#[test]
fn the_mixture_weighs_the_tree_against_the_combined_face() {
    let grain = 16;
    let trees = [
        tree_face(&[rat(1, 2), rat(1, 4), rat(1, 8), rat(1, 8)], grain),
        tree_face(&[rat(1, 4), rat(1, 4), rat(1, 4), rat(1, 4)], grain),
    ];
    // Combined logits on the grain (no fibre), so q_C is exact in ℚ: (8, 2, 2, 4)/16 for the first
    // phase, (1, 1, 1, 2)/5 for the second.
    let logits = |exponents: [i64; 4]| -> Vec<Rat> {
        exponents
            .iter()
            .flat_map(|k| [Rat::from_integer(BigInt::from(*k)), Rat::zero()])
            .collect()
    };
    let reads = [
        ReceivingRead::of_logits(logits([3, 1, 1, 2]), grain),
        ReceivingRead::of_logits(logits([0, 0, 0, 1]), grain),
    ];
    let combined = crate::hnn::ratio::Faces::of_reads(&reads, grain).unwrap();
    let mut mixture = crate::hnn::receiving::Mixture::new(28);
    assert_eq!((mixture.beta(), mixture.weight()), (integer(1), rat(1, 2)));
    let targets = [1usize, 3];
    let scored = mixture.score(2, &combined, &trees, &targets).unwrap();
    let code = |p: Rat| crate::hnn::landmark::code_length(&p).unwrap();
    // Phase 0 at β = 1: q_T = 1/4, q_C = 1/8, q = 3/16.
    assert!(scored.model[0].lower <= code(rat(3, 16)).upper);
    assert!(code(rat(3, 16)).lower <= scored.model[0].upper);
    // The tree's own code lengths: two bits each.
    assert_eq!(scored.tree, vec![code(rat(1, 4)), code(rat(1, 4))]);
    // Phase 1 at β_1 = (1/4)/(1/8) = 2 (λ = 2/3): q_T = 1/4, q_C = 2/5, q = 3/10. The window's
    // product is (A + B)/2 = (1/16 + 1/20)/2 = 9/160; a weight left at β = 1 would read
    // 3/16 · 13/40 = 39/640.
    let drift: Rat = scored.steps.iter().map(|step| step.residual.clone()).sum();
    let window = crate::hnn::reference::window_code_length(&scored.model).unwrap();
    let (ideal, stale) = (code(rat(9, 160)), code(rat(39, 640)));
    assert!(window.lower <= &ideal.upper + &drift && ideal.lower <= &window.upper + &drift);
    assert!(
        &stale.upper + &drift < window.lower,
        "the stale weight (which codes this window shorter) is excluded"
    );
    assert_eq!(scored.steps.len(), 2);
    assert!(scored.steps.iter().all(|step| step.ring == 2));
    for step in &scored.steps {
        assert!(step.combined > Rat::zero() && step.residual >= Rat::zero());
    }
    let before = mixture.beta();
    for step in &scored.steps {
        mixture.step(step).unwrap();
    }
    let exact: Rat = scored
        .steps
        .iter()
        .fold(before, |beta, step| beta * &step.tree / &step.combined);
    // The charts' lower endpoints are rationals of many bits: β is rebased, within its drift.
    let drift = mixture.drift().clone();
    let log = mixture.log2_beta().unwrap();
    let exact_log = crate::hnn::landmark::code_length(&exact.recip()).unwrap();
    assert!(log.lower <= &exact_log.upper + &drift && exact_log.lower <= &log.upper + &drift);
    assert!(mixture.rebases() <= 2);
    // An exact step keeps β exact: q_T = 3/4 against q̃_C = 1/2 multiplies it by 3/2.
    let mut exact_mixture = crate::hnn::receiving::Mixture::new(28);
    exact_mixture
        .step(&crate::hnn::receiving::MixtureStep {
            ring: 2,
            tree: rat(3, 4),
            combined: rat(1, 2),
            residual: Rat::zero(),
        })
        .unwrap();
    assert_eq!(exact_mixture.beta(), rat(3, 2));
    assert_eq!(exact_mixture.weight(), rat(3, 5));
    assert_eq!(
        (exact_mixture.rebases(), exact_mixture.drift()),
        (0, &Rat::zero())
    );
    // Past the carrier width the ratio is rebased to its W-bit mantissa, with 3·2^(−W) of drift.
    let mut narrow = crate::hnn::receiving::Mixture::new(4);
    narrow
        .step(&crate::hnn::receiving::MixtureStep {
            ring: 2,
            tree: rat(17, 32),
            combined: rat(1, 2),
            residual: Rat::zero(),
        })
        .unwrap();
    assert_eq!(narrow.rebases(), 1);
    assert_eq!(narrow.drift(), &rat(3, 16));
    assert_eq!(narrow.beta(), integer(1));
    assert!(mixture.score(2, &combined, &trees[..1], &targets).is_err());
}

/// **The mixture codes within one bit of the better face, and the tree is read in cell order**
/// (Lean `HNN/LandmarkTree.{sequential_mixture_bounds, sequential_mixture_executed}`): on the
/// exposure's chain, over the whole cut, against the tree's executed face `L_T` (the face the
/// mixture weighs) and the combined face `L_C`, `min(L_T, L_C) − drift ≤ L_model ≤ min(L_T, L_C) +
/// 1 + drift`, each half read on the enclosure endpoints that can refute it (a half fails only when
/// the law is violated); `log₂ β` is `L_C − L_T` within the drift; and the tree's code length is
/// exactly the count-only prequential tree's over the same cut (`hnn::landmark::prequential`), so
/// every phase of every window read the tree after every earlier cell.
#[test]
fn the_mixture_codes_within_one_bit_of_the_better_face() {
    use super::learning::chain_of;
    use crate::hnn::reference::Cut;
    let n_star = chain_of(1 << 16).capacity().n_star() as usize;
    let length = n_star + n_star % 2;
    let field = chain_of(length as u64);
    let mut draw = Draw::new(97);
    let cut = Cut {
        cells: (0..length)
            .map(|k| {
                if draw.below(8) == 0 {
                    draw.below(4)
                } else {
                    [0, 1, 2, 1][k % 4]
                }
            })
            .collect(),
        held_out: std::iter::once(length - 4..length).collect(),
    };
    let exposure = Reference::new(64, Steps::campaign_one(), OPEN_BUDGET)
        .expose(&field, &cut)
        .unwrap();
    assert!(exposure.complete, "every window deposited");
    let total =
        |pick: fn(&crate::hnn::reference::Bits) -> &crate::ratio::algebraic::ExactInterval| {
            let (a, b) = (pick(&exposure.training), pick(&exposure.held_out));
            (&a.lower + &b.lower, &a.upper + &b.upper)
        };
    let model = total(|bits| &bits.model);
    let tree = total(|bits| &bits.tree);
    let combined = total(|bits| &bits.combined);
    let report = exposure.mixture.as_ref().unwrap();
    let drift = &report.drift;
    assert!(*drift >= Rat::zero());
    let lowest = |a: &Rat, b: &Rat| if a < b { a.clone() } else { b.clone() };
    // L_model ≤ min(L_T, L_C) + 1 + drift, refuted only if the lower endpoint passes the upper ones.
    assert!(model.0 <= lowest(&tree.1, &combined.1) + integer(1) + drift);
    // min(L_T, L_C) − drift ≤ L_model, refuted only if the upper endpoint falls below the lower ones.
    assert!(lowest(&tree.0, &combined.0) - drift <= model.1);
    // log₂ β = L_C − L_T within the drift (the mixture's evidence).
    let log = &report.log2_beta;
    assert!(log.lower <= &combined.1 - &tree.0 + drift);
    assert!(&combined.0 - &tree.1 - drift <= log.upper);
    // The tree read in cell order is the count-only prequential tree, exactly.
    let receiver = &field.receivers()[0];
    let declared = landmark_declaration(&field, receiver).unwrap();
    let alone = crate::hnn::landmark::prequential(&cut, &declared).unwrap();
    assert_eq!(exposure.training.tree, alone.development.tree);
    assert_eq!(exposure.held_out.tree, alone.held_out.tree);
    assert_eq!(
        (exposure.training.cells, exposure.held_out.cells),
        (alone.development.cells, alone.held_out.cells)
    );
}
