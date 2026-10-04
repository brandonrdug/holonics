//! The receiving phases: the grain derived from the receiver, the observability refusal (the exact
//! grain reading and its integer comparison are `receiver::face`'s, tested there); the receiving parametron's landmark tree declared from
//! the receiver and coded in the description; the active suffix address and each phase's causal
//! address; the combined read of the tree's face and the wave through `R P_R^(τ_R)`; the compare's
//! landmark steps and their deposit; and the maps' openings (the landmark tree: `R_0 = 0`, `E_0` the sign
//! generator times ½), with the deadlock they avoid. Campaign 2: the receiving letters read from the
//! clock before the cell they predict (through aeon boundaries and re-keying), restricted by whole
//! bundles, the sheet grain a scale square of the period grain, and the letters' partitions finite
//! with injective codes.

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::learning::{OPEN_BUDGET, chain, chain_declaration, moment, phases};
use super::support::{Draw, Medium, Parts, lift, small_field};
use crate::compression::landmark::context::{
    Landmarks, Letter, LetterFamily, Widths, address, letter_address,
};
use crate::hnn::HnnError;
use crate::hnn::constitution::{CAMPAIGN_ONE_BUDGET, Constitution, Locus};
use crate::hnn::field::{ConstitutionRead, Current, Field, FieldDeclaration, ReceiverDeclaration};
use crate::hnn::keys;
use crate::hnn::pending::PendingRatio;
use crate::hnn::port::{ExecutionPort, Handle, ReceiptDetail};
use crate::hnn::ratio::{HolonRatio, target_phases};
use crate::hnn::receiving::{
    ActiveAddress, Feature, FeatureFamily, LetterReader, ReceivingPhases, ReceivingRead,
    clock_letters, grain_logits, landmark_declaration, tree_code_length,
};
use crate::hnn::reference::{Reference, compose, one_hot};
use crate::ratio::algebraic::{ExactInterval, log2_enclosure};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer, rat};
use crate::receiver::face::{GrainCell, grain_exponent};

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
        prior: crate::compression::landmark::context::StopPrior::half(),
        mass: 1,
        base: crate::compression::landmark::context::BaseMeasure::Even,
        receiving_scale: 0,
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
        prior: crate::compression::landmark::context::StopPrior::half(),
        mass: 1,
        base: crate::compression::landmark::context::BaseMeasure::Even,
        receiving_scale: 0,
    };
    match ReceivingPhases::declare(&field, &medium, &current, &wide) {
        Err(HnnError::Observability { aperture, rank }) => {
            assert_eq!(aperture, 5);
            assert!(rank <= 4);
        }
        other => panic!("expected an observability refusal, found {other:?}"),
    }
}

/// **The active suffix address and each phase's causal address** (module header of
/// `hnn::receiving`): the register shifted at every cell holds the last `D` cells newest first,
/// `Boundary` before the first; at an epoch opening at `p` with its targets known, phase `j`'s
/// address is `compression::landmark::context::address(cells, p + j, D)` exactly, so no two phases of an epoch pool
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
                        register.phase(targets, j).unwrap(),
                        address(&cells, p + j, depth),
                        "depth {depth}, aperture {aperture}, cell {}",
                        p + j
                    );
                    assert_eq!(register.phase(&[], j).unwrap(), address(&cells, p, depth));
                }
                for &cell in targets {
                    register.receive(cell).unwrap();
                }
                p += aperture;
            }
            assert_eq!(register.letters(), address(&cells, p, depth).as_slice());
        }
    }
    let mut register = ActiveAddress::boundary(3);
    register.receive(7).unwrap();
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
/// no forced split; campaign 1 declares `D = 63`, the prior mass `2^(−3)` and the root's base, and at
/// `n* = 6,148 = 2²·29·53`, `L_R = 16`, `B = 8` the owner derives the path lattice `M_p = 50` (its
/// floor `1/(2(2³n* + 2))` at the root's base, the path depth 63) and the β carrier `W = 37`. A change of prior mass changes the field's code too. A change of depth changes the field's code; the initial
/// constitution carries a tree on the receiving ring only, empty, and its receiving map `R_0 = 0`
/// and source port `E_0` the declared sign sequence times ½ (entries `±½`).
#[test]
fn the_field_declares_the_tree_and_codes_it() {
    let deep = chain();
    let mut shallow = chain_declaration(1 << 20);
    shallow.receivers[0].depth = 1;
    let shallow = Field::declare(shallow).unwrap();
    assert_ne!(
        deep.describe(OPEN_BUDGET, 64),
        shallow.describe(OPEN_BUDGET, 64)
    );
    let campaign = Field::declare(FieldDeclaration::campaign_one(6_148)).unwrap();
    assert_eq!(campaign.receivers()[0].depth, 63);
    assert_eq!(campaign.capacity().n_star(), 6_148);
    let declared = landmark_declaration(&campaign, &campaign.receivers()[0]).unwrap();
    assert_eq!(
        (declared.alphabet, declared.depth, declared.forced),
        (256, 63, 0)
    );
    assert_eq!((declared.population, declared.grain, declared.mass), (6_148, 16, 3));
    let widths = Widths::derived(&declared);
    assert_eq!((widths.digits, widths.face, widths.carrier), (8, 50, 37));
    assert_eq!(
        declared.base,
        crate::compression::landmark::context::BaseMeasure::Root
    );
    let mut kt = FieldDeclaration::campaign_one(6_148);
    kt.receivers[0].mass = 1;
    assert_ne!(
        Field::declare(kt).unwrap().describe(OPEN_BUDGET, 64),
        campaign.describe(OPEN_BUDGET, 64)
    );
    let theta = Constitution::initial(&campaign, CAMPAIGN_ONE_BUDGET).unwrap();
    let tree = theta.landmarks(2).unwrap();
    assert_eq!(tree.declaration(), &declared);
    // The root base's doubled floor keeps the rule below half a grain at depth 63.
    assert!(tree.face_rule() < Rat::new(1.into(), 32.into()));
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
/// epoch's earlier targets (cell order); each class's
/// real logit read at the grain, its imaginary logit (the wave's alone) halved into turns. The
/// tree logits lie on the grain, so each cell is the wave's shifted by `k_c/L_R` exactly and keeps
/// the wave's fibre; the tree's face sums to one exactly and its grain logits alone code each class
/// within one grain of `−log₂ q(c)` (`grain_code_residual`).
#[test]
fn the_read_adds_the_trees_face_to_the_rotated_wave() {
    let field = &chain();
    let mut medium = Medium::encoding(field, 12);
    // A tree that received a short passage, so its face differs from address to address; the
    // epoch's two cells are not yet deposited.
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
        register.receive(cell).unwrap();
    }
    let targets = [passage[9], passage[10]];
    let faces = phases.tree_faces(&medium, &register, &targets).unwrap();
    assert_eq!(faces.len(), 2);
    // Phase j reads the tree after the epoch's earlier targets (cell order).
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

/// **The compare deposits its targets into the tree on their own addresses** (the landmark tree): the
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
        register.receive(cell).unwrap();
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
    let (_, deposit) = compose(
        &field,
        &theta,
        &pending,
        &crate::hnn::WordOpening::Rest,
        &back,
        &targets,
        &scored.steps,
    )
    .unwrap();
    assert_eq!(deposit.receiving(), &scored.steps[..]);
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
        "phase 1 reads its own lag-one cell, the epoch's first target"
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
    let mut received = theta.population(2).unwrap().clone();
    for step in &scored.steps {
        received.receive(&step.faces()).unwrap();
    }
    assert_eq!(
        next.population(2),
        Some(&received),
        "one step a phase, in cell order"
    );
    assert_eq!(received.cells(), 2);
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
    let initial = Constitution::initial(&field, OPEN_BUDGET).unwrap();
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

/// **`R` opens at zero and learns from the first deposit** (the landmark tree's declared openings): at
/// the declared initial constitution (`R_0 = 0`, `E_0` the sign sequence times ½) the first
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
fn tree_face(
    probabilities: &[Rat],
    grain: u64,
) -> crate::compression::landmark::context::LandmarkFace {
    crate::compression::landmark::context::LandmarkFace {
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

/// **The receiver's population weighs the tree against the combined face, cell by cell** (ruling
/// A, THE_REBUILD U1; Lean `Compression/Landmark/Context/{LocalWeighing.two_face_prior,
/// Tree.sequential_mixture}`): it opens at ½/½; phase `j` of an epoch reads the population after
/// the earlier phases' faces, so the epoch's product is `½ A + ½ B` (the tree's and the combined
/// face's likelihoods) exactly enclosed, with no chart, and a weight read before phase 0's step
/// (½/½ at phase 1) is excluded; each phase's code length encloses
/// `−log₂(w_T q_T + w_C q_C)` with `q_C` the combined face's exact class mass, and the tree's own
/// `−log₂ q_T` is returned beside it; the steps carry the families' faces of the targets in cell
/// order, and an epoch without one tree face a phase is refused.
#[test]
fn the_population_weighs_the_tree_against_the_combined_face() {
    use crate::hnn::receiving::{COMBINED, TREE, receiving_population, score};
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
    let population = receiving_population();
    assert_eq!(
        population.weight(TREE).unwrap(),
        ExactInterval::point(rat(1, 2))
    );
    let targets = [1usize, 3];
    let scored = score(&population, 2, &combined, &trees, &targets).unwrap();
    let code = |p: Rat| crate::compression::landmark::context::code_length(&p).unwrap();
    // Phase 0 at ½/½: q_T = 1/4, q_C = 1/8, q = 3/16.
    assert!(scored.model[0].lower <= code(rat(3, 16)).upper);
    assert!(code(rat(3, 16)).lower <= scored.model[0].upper);
    // The tree's own code lengths: two bits each.
    assert_eq!(scored.tree, vec![code(rat(1, 4)), code(rat(1, 4))]);
    // Phase 1 at w_T = (1/4)/(1/4 + 1/8) = 2/3: q_T = 1/4, q_C = 2/5, q = 3/10. The epoch's
    // product is (A + B)/2 = (1/16 + 1/20)/2 = 9/160; a weight left at ½/½ would read
    // 3/16 · 13/40 = 39/640.
    let window = crate::hnn::reference::window_code_length(&scored.model).unwrap();
    let (ideal, stale) = (code(rat(9, 160)), code(rat(39, 640)));
    assert!(window.lower <= ideal.upper && ideal.lower <= window.upper);
    assert!(
        stale.upper < window.lower,
        "the stale weight (which codes this epoch shorter) is excluded"
    );
    assert_eq!(scored.steps.len(), 2);
    assert!(scored.steps.iter().all(|step| step.ring == 2));
    assert_eq!(scored.steps[0].tree, rat(1, 4));
    for step in &scored.steps {
        assert!(step.combined.lower > Rat::zero() && step.combined.lower <= step.combined.upper);
    }
    // The staged steps received in cell order reach the population the epoch was scored through.
    let mut received = population.clone();
    for step in &scored.steps {
        received.receive(&step.faces()).unwrap();
    }
    let weight = received.weight(COMBINED).unwrap();
    // w_C after both phases: (1/8 · 2/5)/(1/4 · 1/4 + 1/8 · 2/5) = (1/20)/(1/16 + 1/20) = 4/9.
    assert!(weight.lower <= rat(4, 9) && rat(4, 9) <= weight.upper);
    assert!(score(&population, 2, &combined, &trees[..1], &targets).is_err());
}

/// **The receiver's population weighs by the families' likelihoods, cell by cell** (THE_REBUILD
/// U1; the fixture on which the retired carried ratio and the population agreed exactly, commit
/// `19f1eb61`): on dyadic faces the tree's weight is the exact posterior
/// `L_T/(L_T + L_C)` (`1/2, 3/4, 5/8, 7/16`), the face of the received class is exact
/// (`1/2, 3/8, 5/8`) and the passage's product is `15/128 = ½ L_T + ½ L_C`, each code enclosing its
/// exact code length. At an exactly zero combined face the combined family dies: its weight is
/// exactly zero, the tree's exactly one, and the face the tree's; no positive floor.
#[test]
fn the_receivers_population_weighs_by_likelihood_cell_by_cell() {
    use crate::compression::landmark::context::code_length;
    use crate::hnn::receiving::{COMBINED, ReceivingStep, TREE, receiving_population};
    let step = |tree: Rat, combined: Rat| ReceivingStep {
        ring: 2,
        tree,
        combined: ExactInterval::point(combined),
    };
    let steps = [
        step(rat(3, 4), rat(1, 4)),
        step(rat(5, 16), rat(9, 16)),
        step(rat(7, 16), rat(15, 16)),
    ];
    let weights = [rat(1, 2), rat(3, 4), rat(5, 8), rat(7, 16)];
    let faces = [rat(1, 2), rat(3, 8), rat(5, 8)];
    let mut population = receiving_population();
    let mut product = Rat::one();
    for (t, step) in steps.iter().enumerate() {
        let w = weights[t].clone();
        assert_eq!(
            population.weight(TREE).unwrap(),
            ExactInterval::point(w.clone())
        );
        assert_eq!(
            population.weight(COMBINED).unwrap(),
            ExactInterval::point(Rat::one() - &w)
        );
        let q = &w * &step.tree + (Rat::one() - &w) * &step.combined.lower;
        assert_eq!(q, faces[t]);
        assert_eq!(
            population.face_of(&step.faces()).unwrap(),
            ExactInterval::point(q.clone())
        );
        let exact = code_length(&q).unwrap();
        let weighed = population.code_of(&step.faces()).unwrap();
        assert!(weighed.lower <= exact.lower && exact.upper <= weighed.upper);
        product *= &q;
        population.receive(&step.faces()).unwrap();
    }
    assert_eq!(
        population.weight(TREE).unwrap(),
        ExactInterval::point(weights[3].clone())
    );
    assert_eq!(product, rat(15, 128));
    let exact = code_length(&product).unwrap();
    let code = population.code().unwrap();
    assert!(code.lower <= exact.lower && exact.upper <= code.upper);
    // Death: the combined face gives the received class exactly zero.
    let dying = step(rat(1, 2), Rat::zero());
    assert_eq!(
        population.face_of(&dying.faces()).unwrap(),
        ExactInterval::point(rat(7, 32))
    );
    assert_eq!(population.receive(&dying.faces()).unwrap(), vec![COMBINED]);
    assert_eq!(
        population.weight(COMBINED).unwrap(),
        ExactInterval::point(Rat::zero())
    );
    assert_eq!(
        population.weight(TREE).unwrap(),
        ExactInterval::point(Rat::one())
    );
    assert_eq!(
        population
            .face_of(&step(rat(3, 8), rat(1, 2)).faces())
            .unwrap(),
        ExactInterval::point(rat(3, 8))
    );
}

/// **The receiving face codes within one bit of the better face, and the tree is read in cell
/// order** (Lean `Compression/Landmark/Context/Tree.sequential_mixture_bounds`, the two-family
/// population at ½/½): on the exposure's chain, over the whole cut, against the tree's executed face
/// `L_T` (the face the population weighs) and the combined face `L_C`,
/// `min(L_T, L_C) ≤ L_model ≤ min(L_T, L_C) + 1`, each half read on the enclosure endpoints that can
/// refute it, with no chart drift; the population's own code (its telescope) meets the model's
/// summed code; each family's likelihood is its summed code (the population's tree code meets the
/// exposure's tree sum, its combined code the combined sum), so its log-odds is `L_C − L_T`; and the
/// tree's code length is the count-only prequential tree's over the same cut
/// (`hnn::reference::prequential`, which encloses the faces' product once, `PassageCode`, where the
/// exposure sums its epochs' enclosures): the two enclosures meet and each is narrower than
/// `2^(−60)` bits, far below the least move one cell's face read at a different standing would
/// make, so every phase of every epoch read the tree after every earlier cell.
#[test]
fn the_receiving_face_codes_within_one_bit_of_the_better_face() {
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
    let exposure = Reference::new(64, OPEN_BUDGET)
        .expose(&field, &cut)
        .unwrap();
    assert!(exposure.complete, "every epoch deposited");
    let total = |pick: fn(&crate::hnn::reference::Bits) -> &ExactInterval| {
        let (a, b) = (pick(&exposure.training), pick(&exposure.held_out));
        ExactInterval::new(&a.lower + &b.lower, &a.upper + &b.upper).unwrap()
    };
    let model = total(|bits| &bits.model);
    let tree = total(|bits| &bits.tree);
    let combined = total(|bits| &bits.combined);
    let lowest = |a: &Rat, b: &Rat| if a < b { a.clone() } else { b.clone() };
    // L_model ≤ min(L_T, L_C) + 1, refuted only if the lower endpoint passes the upper ones.
    assert!(model.lower <= lowest(&tree.upper, &combined.upper) + integer(1));
    // min(L_T, L_C) ≤ L_model, refuted only if the upper endpoint falls below the lower ones.
    assert!(lowest(&tree.lower, &combined.lower) <= model.upper);
    let meet = |a: &ExactInterval, b: &ExactInterval| a.lower <= b.upper && b.lower <= a.upper;
    let report = exposure.population.as_ref().unwrap();
    assert!(
        meet(&report.code, &model),
        "the telescope is the summed code"
    );
    assert!(meet(report.tree.as_ref().unwrap(), &tree));
    assert!(meet(report.combined.as_ref().unwrap(), &combined));
    let odds = report.odds.as_ref().unwrap();
    assert!(odds.lower <= &combined.upper - &tree.lower);
    assert!(&combined.lower - &tree.upper <= odds.upper);
    assert_eq!(
        report.cells,
        exposure.training.cells + exposure.held_out.cells
    );
    // The tree read in cell order is the count-only prequential tree, exactly.
    let receiver = &field.receivers()[0];
    let declared = landmark_declaration(&field, receiver).unwrap();
    let letters = crate::compression::landmark::context::cell_letters(&cut.cells);
    let alone = crate::hnn::reference::prequential(&cut, &letters, &declared).unwrap();
    let narrow = Rat::new(1.into(), num_bigint::BigInt::from(1u8) << 60usize);
    for (exposed, measured) in [
        (&exposure.training.tree, &alone.development.tree),
        (&exposure.held_out.tree, &alone.held_out.tree),
    ] {
        assert!(exposed.lower <= measured.upper && measured.lower <= exposed.upper);
        assert!(&exposed.upper - &exposed.lower < narrow);
        assert!(&measured.upper - &measured.lower < narrow);
    }
    assert_eq!(
        (exposure.training.cells, exposure.held_out.cells),
        (alone.development.cells, alone.held_out.cells)
    );
}

// -------------------------------------------------------------------------------------------
// campaign 2: the receiving letters

/// Campaign 1's field (four closing rings of periods 5, 7, 11, 13) over a declared population.
fn campaign_field() -> Field {
    Field::declare(FieldDeclaration::campaign_one(6_148)).unwrap()
}

/// Rings 0 and 1's phase classes at their declared periods.
fn clock_family() -> FeatureFamily {
    FeatureFamily::new(vec![
        Feature::Phase { ring: 0, grain: 5 },
        Feature::Phase { ring: 1, grain: 7 },
    ])
    .unwrap()
}

/// **The bundle letters are read from the clock before the cell they predict** (Lean
/// `Compression/Landmark/Context/Address.{bundle_causal, address_descends_retention}`): over a passage long enough
/// for the joint clock's carry-outs and their re-keyings, a register that receives each cell (its
/// clock stepping as the lift point does, synchronized after each re-keying) holds
/// `letter_address` of the replayed clock letters at every epoch, and each phase's address, read
/// by a copy of the register's clock over the epoch's earlier targets, is the letter address at
/// `p + j`. Changing every cell from `j` on changes no letter of the address at `j`: no bundle reads
/// the cell it predicts. The register's clock agrees with the lift point throughout.
#[test]
fn the_bundle_letters_are_read_from_the_clock_before_the_cell_they_predict() {
    let field = campaign_field();
    let family = clock_family();
    let mut draw = Draw::new(29);
    let cells: Vec<usize> = (0..3_000).map(|_| (draw.next() % 256) as usize).collect();
    let letters = clock_letters(&field, &family, &cells, &[]).unwrap();
    assert!(matches!(letters[0], Letter::Bundle(_)));
    let depth = 3;
    let aperture = 2;
    let mut current = Current::at_rest(&field);
    let mut register = ActiveAddress::of_reader(
        depth,
        LetterReader::of(&field, family.clone(), &current).unwrap(),
    );
    let (mut aeon_start, mut rekeyed) = (0usize, 0usize);
    let crib = field.crib();
    let mut p = 0;
    while p + aperture <= cells.len() {
        assert_eq!(
            register.letters(),
            letter_address(&letters, p, depth).as_slice()
        );
        let targets = &cells[p..p + aperture];
        for j in 0..aperture {
            assert_eq!(
                register.phase(targets, j).unwrap(),
                letter_address(&letters, p + j, depth),
                "cell {}",
                p + j
            );
        }
        for (offset, &cell) in targets.iter().enumerate() {
            let step = current.step(&field, cell).unwrap();
            register.receive(cell).unwrap();
            assert!(register.reader().agrees(&field, &current, current.lift()));
            if step.carry_out {
                let end = p + offset + 1;
                let from = end.saturating_sub(crib.window).max(aeon_start);
                let location =
                    keys::locate_closing(&field, &current, &cells[from..end], crib.offset).unwrap();
                location.rekey(&field, &mut current).unwrap();
                register.synchronize(&field, &current).unwrap();
                aeon_start = end;
                rekeyed += 1;
            }
        }
        p += aperture;
    }
    assert!(rekeyed >= 1, "the passage crossed an aeon boundary");
    for j in [1usize, 17, 400, 1_500, 2_999] {
        let mut changed = cells.clone();
        for cell in &mut changed[j..] {
            *cell = 255 - *cell;
        }
        let again = clock_letters(&field, &family, &changed, &[]).unwrap();
        assert_eq!(
            letter_address(&again, j, depth),
            letter_address(&letters, j, depth),
            "the address at {j} reads no cell from {j} on"
        );
    }
}

/// **The address restricts by whole bundles, and the sheet grain is a scale square** (Lean
/// `Compression/Landmark/Context/Address.{bundle_restrict, feature_scale_square}`): restricting the address at `D`
/// to `d` bundles is the address at `d`, and the bundle tree's letters of the restricted address
/// are the first `d(1 + r)` letters of the full one's; the half-turn sheet letters (grain 2) are the
/// coarsening `k ↦ ⌊2k/d_g⌋` of the period-grain letters, tick by tick, so coarsening commutes
/// with the restriction.
#[test]
fn the_address_restricts_by_whole_bundles_and_the_sheets_are_a_scale_square() {
    let field = campaign_field();
    let family = clock_family();
    let sheets = FeatureFamily::new(vec![
        Feature::Phase { ring: 0, grain: 2 },
        Feature::Phase { ring: 1, grain: 2 },
    ])
    .unwrap();
    let mut draw = Draw::new(41);
    let cells: Vec<usize> = (0..1_500).map(|_| (draw.next() % 256) as usize).collect();
    let letters = clock_letters(&field, &family, &cells, &[]).unwrap();
    let coarse = clock_letters(&field, &sheets, &cells, &[]).unwrap();
    let declared =
        |family: LetterFamily| crate::compression::landmark::context::LandmarkDeclaration {
            alphabet: 256,
            depth: 4,
            forced: 0,
            population: 6_148,
            grain: 16,
            family,
            prior: crate::compression::landmark::context::StopPrior::half(),
            capacity: crate::compression::landmark::context::Capacity::Unbounded,
            mass: 1,
            base: crate::compression::landmark::context::BaseMeasure::Even,
        };
    let tree = Landmarks::new(declared(family.letters().clone())).unwrap();
    let coarsen = |letter: Letter| match letter {
        Letter::Bundle(bundle) => {
            let values = family.letters().decode(bundle.features);
            Letter::Bundle(crate::compression::landmark::context::Bundle {
                cell: bundle.cell,
                features: sheets
                    .letters()
                    .encode(&[(2 * values[0]) / 5, (2 * values[1]) / 7])
                    .unwrap(),
            })
        }
        other => other,
    };
    for position in [0usize, 1, 5, 333, 1_499] {
        let full = letter_address(&letters, position, 4);
        for d in 0..=4 {
            assert_eq!(full[..d], letter_address(&letters, position, d)[..]);
            let restricted = [full[..d].to_vec(), vec![Letter::Boundary; 4 - d]].concat();
            let flat = tree.arena().letters(&full);
            let cut = tree.arena().letters(&restricted);
            assert_eq!(flat[0][..d], cut[0][..d]);
            assert_eq!(flat[1][..3 * d], cut[1][..3 * d]);
        }
        let coarse_address = letter_address(&coarse, position, 4);
        let mapped: Vec<Letter> = full.iter().map(|&letter| coarsen(letter)).collect();
        assert_eq!(mapped, coarse_address);
        for d in 0..=4 {
            let restricted: Vec<Letter> = full[..d].iter().map(|&l| coarsen(l)).collect();
            assert_eq!(restricted, letter_address(&coarse, position, d));
        }
    }
}

/// **The letters' partitions are finite and their codes injective** (Lean
/// `Compression/Landmark/Context/Address.{phase_partition_finite, lock_partition_finite, bundle_code_injective}`):
/// a ring's phases `k/d` read at grain `g ≤ d` fall in `[0, g)`, cover it, and each fibre is below
/// `1/g`; the lock letters at `(P, Q)` are `Unlocked` and the reduced `(p, q)`, `1 ≤ p ≤ P`,
/// `1 ≤ q ≤ Q` (the contact owner's family, `hnn::contact::ContactLock::code`), coded onto
/// `[0, 1 + #box)` one to one, an address outside the family refused; the contact slot's value
/// `lock · 5 + kind` is one to one onto its size; the features' mixed-radix code round-trips and is
/// one to one; and the bundle code `1 + x + |A| f` is one to one with the boundary at 0.
#[test]
fn the_letter_partitions_are_finite_and_their_codes_injective() {
    use crate::compression::landmark::context::Bundle;
    use crate::hnn::contact::{ContactLock, ContactReading, LockDeclaration};
    use crate::navigator::trace::SiteKind;
    use num_bigint::BigUint;
    use std::collections::BTreeSet;
    for period in [5u64, 7, 11, 13] {
        for grain in [2u64, period] {
            let classes: BTreeSet<u64> = (0..period)
                .map(|k| {
                    let cell = GrainCell::of(&rat(k as i64, period as i64), grain);
                    assert!(cell.fibre < rat(1, grain as i64));
                    assert_eq!(cell.carry, BigInt::zero());
                    cell.phase
                })
                .collect();
            assert_eq!(classes, (0..grain).collect::<BTreeSet<u64>>());
        }
    }
    let gcd = |mut a: u64, mut b: u64| {
        while b != 0 {
            (a, b) = (b, a % b);
        }
        a
    };
    let bound = |p: u64, q: u64| LockDeclaration {
        numerator: BigUint::from(p),
        denominator: BigUint::from(q),
    };
    let locked = |p: u64, q: u64| ContactLock::Locked {
        numerator: BigUint::from(p),
        denominator: BigUint::from(q),
    };
    for p_bound in [0u64, 1, 4, 9, 30] {
        for q_bound in [0u64, 1, 3, 9, 13] {
            let at = bound(p_bound, q_bound);
            let reduced = (1..=q_bound)
                .flat_map(|q| (1..=p_bound).map(move |p| (p, q)))
                .filter(|&(p, q)| gcd(p, q) == 1)
                .count() as u64;
            assert_eq!(at.letters().unwrap(), 1 + reduced);
            let mut codes = BTreeSet::from([ContactLock::Unlocked.code(&at).unwrap()]);
            for q in 0..=q_bound + 1 {
                for p in 0..=p_bound + 1 {
                    let inside = p >= 1 && q >= 1 && p <= p_bound && q <= q_bound;
                    match locked(p, q).code(&at) {
                        Ok(code) => {
                            assert!(inside && gcd(p, q) == 1, "({p}, {q})");
                            assert!(codes.insert(code));
                        }
                        Err(_) => assert!(!inside || gcd(p, q) != 1, "({p}, {q})"),
                    }
                }
            }
            assert_eq!(codes, (0..at.letters().unwrap()).collect());
        }
    }
    // Campaign 1's derived bounds, the horizon: contact 0 → 1 reads rates above one (P = 1001,
    // Q = 143).
    let field = campaign_field();
    let derived = LockDeclaration::derived(&field, 0);
    assert_eq!(derived.numerator, BigUint::from(7u32 * 11 * 13));
    assert_eq!(derived.denominator, BigUint::from(11u32 * 13));
    assert!(locked(8, 5).code(&derived).is_ok());
    let at = bound(3, 3);
    let slot = Feature::Contact {
        contact: 0,
        bound: at.clone(),
    };
    let kinds = [
        SiteKind::Rotation,
        SiteKind::Null,
        SiteKind::Boost,
        SiteKind::Reflection,
        SiteKind::Degenerate,
    ];
    let mut values = BTreeSet::new();
    let locks = (1..=3u64)
        .flat_map(|q| (1..=3u64).map(move |p| (p, q)))
        .filter(|&(p, q)| gcd(p, q) == 1)
        .map(|(p, q)| locked(p, q))
        .chain([ContactLock::Unlocked]);
    for lock in locks {
        for kind in kinds {
            let reading = ContactReading {
                contact: 0,
                lock: lock.clone(),
                kind,
            };
            assert!(values.insert(slot.contact_value(&reading).unwrap()));
        }
    }
    assert_eq!(values, (0..slot.size().unwrap()).collect());
    let declared = FeatureFamily::new(vec![
        Feature::Phase { ring: 0, grain: 3 },
        slot.clone(),
        Feature::Phase { ring: 1, grain: 2 },
    ])
    .unwrap();
    let family = declared.letters();
    assert_eq!(family.codes(), 3 * at.letters().unwrap() * 5 * 2);
    let mut codes = BTreeSet::new();
    let mut bundles = BTreeSet::from([family.bundle_code(Letter::Boundary, 4)]);
    for a in 0..3 {
        for b in 0..slot.size().unwrap() {
            for c in 0..2 {
                let code = family.encode(&[a, b, c]).unwrap();
                assert_eq!(family.decode(code), vec![a, b, c]);
                assert!(codes.insert(code));
                for cell in 0..4 {
                    let letter = Letter::Bundle(Bundle {
                        cell,
                        features: code,
                    });
                    assert!(bundles.insert(family.bundle_code(letter, 4)));
                }
            }
        }
    }
    assert_eq!(u64::from(*codes.iter().max().unwrap()) + 1, family.codes());
    assert_eq!(bundles.len() as u64, family.bundle_codes(4));
    assert!(family.encode(&[3, 0, 0]).is_err());
    assert!(
        FeatureFamily::new(vec![Feature::Phase {
            ring: 0,
            grain: 1 << 33
        }])
        .is_err()
    );
    // A slot of one letter carries nothing: no family declares one, and the constant-slot control
    // is its own constructor, never a declared family.
    assert!(FeatureFamily::new(vec![Feature::Phase { ring: 0, grain: 1 }]).is_err());
    let control = LetterFamily::constant_control(2);
    assert_eq!(control.sizes(), &[1, 1]);
    assert_eq!(control.codes(), 1);
}

/// **The contact letters are the contact owner's readings, read from the register's retained state
/// before the cell they predict** (campaign 2; Lean `Compression/Landmark/Context/Address.bundle_causal`,
/// `HNN/Contact.contact_lock_address`). Over a passage through carry-outs and re-keyings, with the
/// register refreshed from a constitution after each epoch's ingest (the site kinds changing where
/// a boost is declared on contact 0 for a stretch of epochs):
/// - each tick's contact letters are `hnn::contact::contact_readings` of the lift point after the
///   tick, from the aeon's opening, at the constitution of the last refresh (`ContactReading::letter`);
/// - each phase's address, read at the epoch's cut by a copy of the register (as a pending ratio
///   copies it), is the address the register's own letters give at `p + j`: the compare and the
///   ingest read the same letters, since no refresh falls inside an epoch;
/// - the register's clock agrees with the lift point, windings since the opening included;
/// - the replay `clock_letters` with the kinds held at each tick gives the register's letters, and
///   changing every cell from `j` on changes no letter of the address at `j`.
#[test]
fn the_contact_letters_are_read_from_the_register_before_the_cell_they_predict() {
    use crate::hnn::contact::{LockDeclaration, contact_readings, site_kinds};
    use crate::navigator::trace::SiteKind;
    let field = campaign_field();
    let theta = Constitution::initial(&field, OPEN_BUDGET).unwrap();
    let width = field.contact(0).width();
    let boosted = theta
        .clone()
        .with_contact_signature(&field, 0, (0..width).map(|j| j != 0).collect())
        .unwrap();
    assert_eq!(site_kinds(&field, &boosted).unwrap()[0], SiteKind::Boost);
    let family = FeatureFamily::new(vec![
        Feature::contact(&field, 1),
        Feature::contact(&field, 0),
    ])
    .unwrap();
    let bounds: Vec<(usize, LockDeclaration)> = family
        .features()
        .iter()
        .map(|feature| match feature {
            Feature::Contact { contact, bound } => (*contact, bound.clone()),
            Feature::Phase { .. } => unreachable!("a contact family"),
        })
        .collect();
    let mut draw = Draw::new(53);
    let cells: Vec<usize> = (0..3_000).map(|_| (draw.next() % 256) as usize).collect();
    let (depth, aperture) = (3, 2);
    let mut current = Current::at_rest(&field);
    let mut opening = current.clone();
    let mut reader = LetterReader::of(&field, family.clone(), &current).unwrap();
    assert!(
        reader.clone().tick(cells[0]).is_err(),
        "a contact letter reads the kinds of a refresh"
    );
    reader.refresh(&field, &theta).unwrap();
    let mut register = ActiveAddress::of_reader(depth, reader);
    let (mut received, mut held, mut predicted) = (Vec::new(), Vec::new(), Vec::new());
    let (mut aeon_start, mut rekeyed, mut locked) = (0usize, 0usize, 0usize);
    let crib = field.crib();
    let mut p = 0;
    while p + aperture <= cells.len() {
        let window = p / aperture;
        // Published after this epoch's ingest; the epoch's ticks hold the previous epoch's.
        let published = if (300..700).contains(&window) {
            &boosted
        } else {
            &theta
        };
        let holding = if (301..701).contains(&window) {
            &boosted
        } else {
            &theta
        };
        let targets = &cells[p..p + aperture];
        let cut = register.clone();
        for j in 0..aperture {
            predicted.push((p + j, cut.phase(targets, j).unwrap()));
        }
        for &cell in targets {
            let step = current.step(&field, cell).unwrap();
            register.receive(cell).unwrap();
            let letter = register.letters()[0];
            received.push(letter);
            held.push(site_kinds(&field, holding).unwrap());
            let readings = contact_readings(&field, holding, &current, Some(&opening)).unwrap();
            let Letter::Bundle(bundle) = letter else {
                panic!("a bundle letter")
            };
            let values = family.letters().decode(bundle.features);
            for ((contact, bound), value) in bounds.iter().zip(&values) {
                assert_eq!(*value, readings[*contact].letter(bound).unwrap());
                if readings[*contact].lock != crate::hnn::contact::ContactLock::Unlocked {
                    locked += 1;
                }
            }
            let carry = if step.carry_out {
                current.lift().to_vec()
            } else {
                opening.lift().to_vec()
            };
            assert!(register.reader().agrees(&field, &current, &carry));
            if step.carry_out {
                let end = received.len();
                let from = end.saturating_sub(crib.window).max(aeon_start);
                let location =
                    keys::locate_closing(&field, &current, &cells[from..end], crib.offset).unwrap();
                location.rekey(&field, &mut current).unwrap();
                register.synchronize(&field, &current).unwrap();
                opening = current.clone();
                aeon_start = end;
                rekeyed += 1;
            }
        }
        // The resident refreshes after the epoch's ingest, from the constitution then published.
        register.refresh(&field, published).unwrap();
        p += aperture;
    }
    assert!(rekeyed >= 1, "the passage crossed an aeon boundary");
    assert!(locked > 0, "some contact locked within an aeon");
    for (position, address) in &predicted {
        assert_eq!(
            address,
            &letter_address(&received, *position, depth),
            "cell {position}"
        );
    }
    let replayed = clock_letters(&field, &family, &cells[..received.len()], &held).unwrap();
    assert_eq!(replayed, received);
    for j in [1usize, 17, 400, 1_500, 2_999] {
        let mut changed = cells[..received.len()].to_vec();
        for cell in &mut changed[j..] {
            *cell = 255 - *cell;
        }
        let again = clock_letters(&field, &family, &changed, &held).unwrap();
        assert_eq!(
            letter_address(&again, j, depth),
            letter_address(&received, j, depth),
            "the address at {j} reads no cell from {j} on"
        );
    }
}

/// The receiver's spans of cells are the epochs of the cell clock at the receiver's section (U5;
/// Lean `Aeon/Clock/Epoch.{forward_epoch_is_window, mem_epoch_digitTicks, odometer_tower}`): for
/// every aperture `A` and passage of `n` cells, the epochs tile the passage as
/// `[kA, min((k + 1)A, n))`, cell `c` is read in its epoch `⌊c/A⌋`, the epochs that close number
/// the section's flux `⌊n/A⌋`, and the cell clock's own grain coarsens to the receiver's by the
/// carry `winding A`. The declared receiver reads its epochs through the same law, and `A = 0` is
/// no section.
#[test]
fn the_receiving_windows_are_the_epochs_of_the_cell_clock() {
    use crate::aeon::{ClockLift, EpochTower, epochs};
    use crate::geometry::winding::winding;
    use crate::hnn::receiving::receiving_windows;
    use num_bigint::BigUint;
    for aperture in 1usize..=4 {
        for n in 0usize..=13 {
            let windows = receiving_windows(n, aperture).unwrap();
            let expected: Vec<_> = (0..n.div_ceil(aperture))
                .map(|k| k * aperture..((k + 1) * aperture).min(n))
                .collect();
            assert_eq!(windows, expected, "A = {aperture}, n = {n}");
            for (k, window) in windows.iter().enumerate() {
                assert!(window.clone().all(|cell| cell / aperture == k));
            }
            let closed = windows.iter().filter(|w| w.len() == aperture).count();
            assert_eq!(closed, n / aperture);
            // The tower: the cell clock's own grain one, then the receiver's grain A.
            let lift = ClockLift::new(vec![BigUint::one()]).unwrap();
            let aeon = lift
                .forward(vec![BigInt::zero()], &[BigInt::from(n)])
                .unwrap();
            let at =
                |grain: usize| epochs(&aeon, lift.ring_section(0, BigUint::from(grain)).unwrap());
            let receiver = at(aperture);
            assert_eq!(receiver.flux(), BigInt::from(n / aperture));
            let tower = EpochTower::new(vec![at(1), receiver]).unwrap();
            for (fine, coarse) in tower.coarsen(0, 1).unwrap() {
                assert_eq!(
                    BigUint::from(coarse),
                    winding(&BigUint::from(aperture), &BigUint::from(fine)).unwrap()
                );
            }
        }
    }
    assert!(receiving_windows(5, 0).is_err());
    let field = &chain();
    let medium = Medium::initial(field, 4);
    let current = Current::at_rest(field);
    let phases = ReceivingPhases::declare(field, &medium, &current, &field.receivers()[0]).unwrap();
    assert_eq!(
        phases.windows(7).unwrap(),
        receiving_windows(7, phases.aperture()).unwrap()
    );
}
