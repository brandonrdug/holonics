//! The population's laws checked exactly on small fixtures: the telescope of the replicator's
//! faces to the families' likelihoods (against a mixture stepped in ℚ), survivor filtering as
//! uniform Bayes against brute force, the sheet tuple's factorization, death at zero likelihood,
//! the refusals naming the Bombe, a rotor crib's drawn key in its located fibre, the tree family
//! scored as the prequential harness scores the tree, and selection of the family that made the
//! terrain.

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use super::families::{GratingSheet, MOIRE_BOMBE, ROTOR_BOMBE};
use super::*;
use crate::compression::landmark::context::{
    Capacity, LandmarkDeclaration, LetterFamily, StopPrior, cell_letters, code_length,
};
use crate::hnn::Cut;
use crate::hnn::field::{Field, FieldDeclaration};
use crate::hnn::reference::tree_prequential;
use crate::holarchy::terrain::{
    Draw, Grating, Moire, MoireClass, MoireFamily, RotorCrib, TreeSource, TreeSourceFamily,
    rotor_crib,
};
use crate::holon::contact::menu::PortPermutation;
use crate::ratio::{Rat, rat};

/// A family with one fixed exact face, the same at every cell.
struct Fixed {
    face: Vec<Rat>,
    likelihood: Rat,
    description: u64,
}

impl Fixed {
    fn new(face: Vec<Rat>, description: u64) -> Self {
        Self {
            face,
            likelihood: Rat::one(),
            description,
        }
    }
}

impl Family for Fixed {
    fn label(&self) -> String {
        "fixed".to_string()
    }
    fn alphabet(&self) -> usize {
        self.face.len()
    }
    fn description(&self) -> u64 {
        self.description
    }
    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        Ok(self.face.clone())
    }
    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        let face = self.face[cell].clone();
        self.likelihood *= &face;
        Ok(face)
    }
    fn likelihood(&self) -> Likelihood {
        Likelihood::Exact(self.likelihood.clone())
    }
    fn readout(&self) -> Readout<'_> {
        Readout::Keys(KeyReadout {
            spaces: vec![1],
            survivors: vec![vec![Vec::new()]],
        })
    }
}

/// The terrain's hand moiré: `1/4 @ 0` and `1/3 @ 1/3`, joint period 12.
fn hand_moire(class: MoireClass) -> Moire {
    Moire::new(
        vec![
            Grating::new(1, 4, 0).unwrap(),
            Grating::new(1, 3, 1).unwrap(),
        ],
        class,
    )
    .unwrap()
}

fn small_family() -> MoireFamily {
    MoireFamily {
        rings: 2,
        denominator: 4,
    }
}

fn tree(alphabet: usize, depth: usize, population: usize) -> LandmarkDeclaration {
    LandmarkDeclaration {
        alphabet,
        depth,
        forced: 0,
        population: population as u64,
        grain: 16,
        family: LetterFamily::cells(),
        prior: StopPrior::half(),
        capacity: Capacity::Unbounded,
    }
}

fn contains(interval: &ExactInterval, value: &ExactInterval) -> bool {
    interval.lower <= value.upper && value.lower <= interval.upper
}

fn families(parity: bool) -> Vec<Box<dyn Family>> {
    let class = if parity {
        MoireClass::Parity
    } else {
        MoireClass::Sheets
    };
    vec![
        Box::new(Fixed::new(vec![rat(1, 3), rat(2, 3)], 1)),
        Box::new(KeyFamily::gratings(&small_family(), class, 1 << 16, 2).unwrap()),
        Box::new(Fixed::new(vec![rat(1, 2), rat(1, 2)], 2)),
    ]
}

/// Lean `Population.population_mixture` and `HolonicAdjointNormalization.bayes_eq_discrete_
/// replicator`: the replicator stepped in ℚ (each weight times its face of the cell over the
/// mixture's face) has faces whose product is `Σ_f π_f L_f`, exactly; the population, carrying no
/// weights, encloses that product's code, each posterior and each face. The prior is `2^(−ℓ)/M` with
/// `M = 1/2 + 1/4 + 1/4 = 1`.
#[test]
fn the_replicators_faces_telescope_to_the_families_likelihoods() {
    let cells = hand_moire(MoireClass::Parity).emit(40);
    let mut population = Population::new(families(true)).unwrap();
    let mut reference = families(true);
    assert_eq!(population.mass(), &Rat::one());
    let mut weights: Vec<Rat> = (0..3)
        .map(|f| population.prior(f).unwrap().clone())
        .collect();
    assert_eq!(weights, vec![rat(1, 2), rat(1, 4), rat(1, 4)]);
    let mut product = Rat::one();
    for (t, &cell) in cells.iter().enumerate() {
        let faces: Vec<Vec<Rat>> = reference.iter().map(|f| f.face().unwrap()).collect();
        let face_of = |c: usize| -> Rat {
            weights
                .iter()
                .zip(&faces)
                .map(|(w, face)| w * &face[c])
                .sum()
        };
        let enclosed = population.face().unwrap();
        for (c, interval) in enclosed.iter().enumerate() {
            let exact = face_of(c);
            assert!(
                interval.lower <= exact && exact <= interval.upper,
                "cell {t}"
            );
        }
        let q = face_of(cell);
        product *= &q;
        weights = weights
            .iter()
            .zip(&faces)
            .map(|(w, face)| w * &face[cell] / &q)
            .collect();
        for family in &mut reference {
            family.receive(cell).unwrap();
        }
        population.receive(cell).unwrap();
    }
    let likelihoods: Vec<Rat> = reference
        .iter()
        .map(|f| match f.likelihood() {
            Likelihood::Exact(value) => value,
            Likelihood::Enclosed(_) => unreachable!(),
        })
        .collect();
    let telescoped: Rat = (0..3)
        .map(|f| population.prior(f).unwrap() * &likelihoods[f])
        .sum();
    assert_eq!(product, telescoped);
    let code = population.code().unwrap();
    assert!(contains(&code, &code_length(&product).unwrap()));
    assert!(&code.upper - &code.lower < Rat::new(BigInt::one(), BigInt::one() << 90usize));
    for (f, weight) in weights.iter().enumerate() {
        match population.posterior_of(&[f]).unwrap() {
            Posterior::Bits(bits) => assert!(contains(&bits, &code_length(weight).unwrap())),
            Posterior::Dead => assert!(weight.is_zero()),
        }
    }
    // The gratings made the passage: their posterior is decided above one half.
    assert_eq!(population.receipt().unwrap().selected, Some(1));
}

/// Lean `Population.survivor_code`: survivor filtering is uniform Bayes over the key space. The
/// survivors after 24 cells are exactly the keys whose parity color reproduces them (brute force
/// over all `N_4² = 16² = 256` keys through the terrain's own emission), the truth among them; each
/// step's face is the fraction of survivors emitting each class, and the likelihood is
/// `#S/256`, so the code is `log₂ 256 − log₂ #S`.
#[test]
fn survivor_filtering_is_uniform_bayes_over_the_key_space() {
    let family = small_family();
    let cells = hand_moire(MoireClass::Parity).emit(24);
    let mut keys = KeyFamily::gratings(&family, MoireClass::Parity, 1 << 16, 0).unwrap();
    let mut likelihood = Rat::one();
    for &cell in &cells {
        likelihood *= keys.receive(cell).unwrap();
    }
    let brute: Vec<Vec<u64>> = (0..16u64)
        .flat_map(|a| (0..16u64).map(move |b| (a, b)))
        .filter_map(|(a, b)| {
            let (first, second) = (family.grating(a).unwrap(), family.grating(b).unwrap());
            let moire =
                Moire::new(vec![first.clone(), second.clone()], MoireClass::Parity).unwrap();
            (moire.emit(24) == cells).then(|| {
                vec![
                    first.numerator(),
                    first.denominator(),
                    first.phase(),
                    second.numerator(),
                    second.denominator(),
                    second.phase(),
                ]
            })
        })
        .collect();
    let Readout::Keys(readout) = keys.readout() else {
        unreachable!()
    };
    let mut survivors = readout.survivors[0].clone();
    let mut brute_sorted = brute.clone();
    survivors.sort();
    brute_sorted.sort();
    assert_eq!(survivors, brute_sorted);
    assert!(survivors.contains(&vec![1, 4, 0, 1, 3, 1]));
    assert!(
        survivors.contains(&vec![1, 3, 1, 1, 4, 0]),
        "the rings' swap is a gauge"
    );
    assert_eq!(readout.space(), BigUint::from(256u32));
    let count = survivors.len() as i64;
    assert_eq!(likelihood, rat(count, 256));
    assert_eq!(keys.likelihood(), Likelihood::Exact(rat(count, 256)));
}

/// Lean `Population.survivors_product`: the sheet tuple's key space factorizes per ring, so its
/// face at every cell is the joint key space's survivor fraction (brute force over the 256 joint
/// keys, each emitting `s_0 + 2 s_1`), and its likelihood `#S_0 #S_1/256` is the joint one.
#[test]
fn the_sheet_tuple_factorizes_per_ring() {
    let family = small_family();
    let cells = hand_moire(MoireClass::Sheets).emit(30);
    let mut keys = KeyFamily::gratings(&family, MoireClass::Sheets, 1 << 16, 0).unwrap();
    assert_eq!(keys.alphabet(), 4);
    let joint: Vec<Vec<usize>> = (0..16u64)
        .flat_map(|a| (0..16u64).map(move |b| (a, b)))
        .map(|(a, b)| {
            Moire::new(
                vec![family.grating(a).unwrap(), family.grating(b).unwrap()],
                MoireClass::Sheets,
            )
            .unwrap()
            .emit(30)
        })
        .collect();
    let mut alive: Vec<usize> = (0..joint.len()).collect();
    for (t, &cell) in cells.iter().enumerate() {
        let face = keys.face().unwrap();
        for (class, value) in face.iter().enumerate() {
            let emitting = alive.iter().filter(|&&k| joint[k][t] == class).count();
            assert_eq!(value, &rat(emitting as i64, alive.len() as i64));
        }
        keys.receive(cell).unwrap();
        alive.retain(|&k| joint[k][t] == cell);
    }
    assert_eq!(
        keys.likelihood(),
        Likelihood::Exact(rat(alive.len() as i64, 256))
    );
    let Readout::Keys(readout) = keys.readout() else {
        unreachable!()
    };
    assert_eq!(readout.count(), BigUint::from(alive.len()));
}

/// Lean `HolonicAdjointNormalization.replicator_eq_zero_iff`: the gratings die exactly at the first
/// cell no surviving key emits (a cell flipped in the moiré's passage), their posterior is exactly
/// zero thereafter and they are never read again; the population's code is then the tree's charged
/// code, and when only the gratings are declared the population is extinct.
#[test]
fn a_family_dies_exactly_at_zero_likelihood() {
    let mut cells = hand_moire(MoireClass::Parity).emit(60);
    cells[36] = 1 - cells[36];
    let mut population = Population::new(vec![
        Box::new(TreeFamily::new(tree(2, 3, 60), 1).unwrap()),
        Box::new(KeyFamily::gratings(&small_family(), MoireClass::Parity, 1 << 16, 1).unwrap()),
    ])
    .unwrap();
    let mut alone = KeyFamily::gratings(&small_family(), MoireClass::Parity, 1 << 16, 1).unwrap();
    let first_zero = cells
        .iter()
        .position(|&cell| alone.receive(cell).unwrap().is_zero())
        .expect("the flipped cell kills every key");
    assert_eq!(
        first_zero, 36,
        "36 cells pin every surviving key's emission (Fine–Wilf)"
    );
    population.receive_passage(&cells).unwrap();
    assert_eq!(population.died(1), Some(first_zero));
    assert_eq!(population.died(0), None);
    let receipt = population.receipt().unwrap();
    assert_eq!(receipt.families[1].posterior, Posterior::Dead);
    assert_eq!(receipt.families[1].code, None);
    assert_eq!(receipt.selected, Some(0));
    assert_eq!(Some(&receipt.code), receipt.families[0].charged.as_ref());

    let mut gratings_only = Population::new(vec![Box::new(
        KeyFamily::gratings(&small_family(), MoireClass::Parity, 1 << 16, 0).unwrap(),
    )])
    .unwrap();
    assert_eq!(
        gratings_only.receive_passage(&cells),
        Err(PopulationError::Extinct { cell: first_zero })
    );
}

/// The declared enumeration refuses what survivor filtering cannot hold and names the Bombe that
/// owns it: the parity color of three gratings at denominators up to `2^4` (`862³` keys) and campaign
/// 1's period-11 ring (`11 · 11 · 11!` keys). The descriptions must be a prefix code's lengths and
/// the families must share one alphabet.
#[test]
fn the_declarations_refuse_and_name_the_bombe() {
    let wide = MoireFamily {
        rings: 3,
        denominator: 16,
    };
    match KeyFamily::gratings(&wide, MoireClass::Parity, 1 << 24, 0) {
        Err(PopulationError::Bombe {
            key_space, bombe, ..
        }) => {
            assert_eq!(key_space, BigUint::from(862u32).pow(3));
            assert_eq!(bombe, MOIRE_BOMBE);
        }
        _ => panic!("the parity class past the enumeration is the Bombe's"),
    }
    assert!(KeyFamily::gratings(&wide, MoireClass::Sheets, 1 << 24, 0).is_ok());
    let field = Field::declare(FieldDeclaration::campaign_one(1 << 16)).unwrap();
    match KeyFamily::rotor(&field, 2, &[0, 0, 0, 0], 1 << 24, 0) {
        Err(PopulationError::Bombe {
            key_space, bombe, ..
        }) => {
            assert_eq!(key_space, RotorKeys::key_space(11));
            assert_eq!(bombe, ROTOR_BOMBE);
        }
        _ => panic!("a period-11 ring's crib is the built Bombe's"),
    }
    assert!(matches!(
        Population::new(vec![
            Box::new(Fixed::new(vec![rat(1, 2), rat(1, 2)], 0)),
            Box::new(Fixed::new(vec![rat(1, 2), rat(1, 2)], 0)),
        ]),
        Err(PopulationError::Declaration { .. })
    ));
    assert!(matches!(
        Population::new(vec![
            Box::new(Fixed::new(vec![rat(1, 2), rat(1, 2)], 1)),
            Box::new(Fixed::new(vec![rat(1, 3), rat(1, 3), rat(1, 3)], 1)),
        ]),
        Err(PopulationError::Declaration { .. })
    ));
    let population = Population::new(vec![
        Box::new(Fixed::new(vec![rat(1, 2), rat(1, 2)], 2)),
        Box::new(Fixed::new(vec![rat(1, 2), rat(1, 2)], 3)),
    ])
    .unwrap();
    assert_eq!(population.mass(), &rat(3, 8));
    assert_eq!(population.prior(0), Some(&rat(2, 3)));
}

/// Campaign 1's field with its period-7 ring locked at every port, so the ring steps every tick (as
/// the keys tests' crib ring does): a ring whose stage stays fixed returns a two-cycle crib that
/// names no plugboard.
fn crib_field() -> Field {
    let mut declared = FieldDeclaration::campaign_one(1 << 16);
    declared.rings[1].lock = (0..7).collect();
    Field::declare(declared).unwrap()
}

/// A drawn rotor crib on that period-7 ring (`holarchy::terrain::RotorCrib::draw`): the
/// truth's start, key and plugboard survive, every survivor reproduces the crib by the terrain's own
/// law (`rotor_crib`), and the survivors are the ring's rotor-gauge orbit of 7, so the family's
/// likelihood is `7/(7 · 7 · 7!) = 1/35280`: its code is the start's `log₂ 7` and the key
/// description `log₂(7 · 7!)` less the gauge's `log₂ 7`.
#[test]
fn the_rotor_family_keeps_the_drawn_key_in_its_gauge_orbit() {
    let field = crib_field();
    let configurations = [0u64, 0, 0, 0];
    let crib = RotorCrib::draw(&field, 1, &configurations, 64, &mut Draw::new(41)).unwrap();
    let mut keys = KeyFamily::rotor(&field, 1, &configurations, 1 << 24, 0).unwrap();
    for &cell in &crib.cells {
        assert!(!keys.receive(cell).unwrap().is_zero());
    }
    let Readout::Keys(readout) = keys.readout() else {
        unreachable!()
    };
    assert_eq!(readout.space(), BigUint::from(7u32 * 7 * 5040));
    let truth: Vec<u64> = [crib.truth.start as u64, crib.truth.key]
        .into_iter()
        .chain(crib.truth.board.images().iter().map(|&i| i as u64))
        .collect();
    assert!(readout.survivors[0].contains(&truth));
    for survivor in &readout.survivors[0] {
        let board =
            PortPermutation::new(survivor[2..].iter().map(|&i| i as usize).collect()).unwrap();
        let reproduced = rotor_crib(
            &field,
            1,
            survivor[1],
            &board,
            &configurations,
            crib.cells.len(),
            survivor[0] as usize,
        )
        .unwrap();
        assert_eq!(reproduced, crib.cells);
    }
    assert_eq!(readout.survivors[0].len(), 7);
    assert_eq!(keys.likelihood(), Likelihood::Exact(rat(1, 35280)));
}

/// The tree family scores each cell by the tree's executed face at the current standing, then
/// deposits it: its likelihood's code is `hnn::reference::tree_prequential`'s on the same cells.
#[test]
fn the_tree_family_scores_as_the_prequential_harness() {
    let cells = hand_moire(MoireClass::Sheets).emit(200);
    let declaration = tree(4, 3, 200);
    let mut family = TreeFamily::new(declaration.clone(), 0).unwrap();
    for &cell in &cells {
        family.receive(cell).unwrap();
    }
    let cut = Cut {
        cells: cells.clone(),
        held_out: Vec::new(),
    };
    let ([development, _], _) =
        tree_prequential(&cut, &cell_letters(&cells), &declaration).unwrap();
    assert_eq!(family.likelihood().code().unwrap(), Some(development));
}

/// The population selects the family that made the terrain: on a drawn tree source the gratings die
/// and a tree family's posterior is decided above one half; on the hand moiré the gratings' is.
#[test]
fn the_population_selects_the_family_that_made_the_terrain() {
    let n = 1 << 10;
    let population_of = || {
        Population::new(vec![
            Box::new(TreeFamily::new(tree(2, 2, n), 2).unwrap()) as Box<dyn Family>,
            Box::new(TreeFamily::new(tree(2, 6, n), 2).unwrap()),
            Box::new(KeyFamily::gratings(&small_family(), MoireClass::Parity, 1 << 16, 2).unwrap()),
        ])
        .unwrap()
    };
    let mut draw = Draw::new(7);
    let source = TreeSource::draw(
        &TreeSourceFamily {
            alphabet: 2,
            depth: 2,
            grid: 16,
        },
        &mut draw,
    )
    .unwrap();
    let cells = source.emit(n, &mut draw);
    let mut population = population_of();
    population.receive_passage(&cells).unwrap();
    let receipt = population.receipt().unwrap();
    assert!(receipt.families[2].died.is_some());
    assert_ne!(receipt.selected, Some(2));
    assert_eq!(
        population.posterior_of(&[0, 1]).unwrap(),
        Posterior::Bits(ExactInterval::point(Rat::zero()))
    );
    assert_eq!(receipt.mass, rat(3, 4));

    let cells = hand_moire(MoireClass::Parity).emit(n);
    let mut population = population_of();
    population.receive_passage(&cells).unwrap();
    assert_eq!(population.receipt().unwrap().selected, Some(2));
}

/// A ring's sheet cannot tell it from its mirror, the Swing about the centre of its upper sheet arc
/// (`GratingSheet::mirror`), and from nothing else: over the `N_16 = 862` gratings of the family,
/// the gratings emitting a grating's sheet word are exactly it and its mirror (32 ticks decide it:
/// two words of periods at most 16 agreeing on 32 consecutive ticks are one word, by Fine and Wilf).
/// So a ring's survivors on a moiré are two, one when `q = 2` (its own mirror).
#[test]
fn a_rings_sheet_cannot_tell_it_from_its_mirror() {
    let family = MoireFamily {
        rings: 1,
        denominator: 16,
    };
    let gratings: Vec<Grating> = (0..family.gratings())
        .map(|i| family.grating(i).unwrap())
        .collect();
    let words: Vec<Vec<bool>> = gratings
        .iter()
        .map(|g| (0..32).map(|t| g.sheet(t)).collect())
        .collect();
    for (grating, word) in gratings.iter().zip(&words) {
        let mirror = GratingSheet::mirror(grating).unwrap();
        let mut fibre: Vec<&Grating> = gratings
            .iter()
            .zip(&words)
            .filter(|(_, other)| *other == word)
            .map(|(g, _)| g)
            .collect();
        fibre.dedup();
        let expected = if grating.denominator() == 2 { 1 } else { 2 };
        assert_eq!(fibre.len(), expected, "{grating:?}");
        assert!(fibre.contains(&&mirror) && fibre.contains(&grating));
    }
}
