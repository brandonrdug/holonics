//! The population's laws checked exactly on small fixtures: the telescope of the replicator's
//! faces to the families' likelihoods (against a mixture stepped in ℚ), survivor filtering as
//! uniform Bayes against brute force, the sheet tuple's factorization, death at zero likelihood,
//! the refusals naming the Bombe, a rotor crib's drawn key in its located fibre, the tree family
//! scored as the prequential harness scores the tree, and selection of the family that made the
//! terrain.

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use super::families::{GratingParity, GratingSheet, MOIRE_BOMBE, ROTOR_BOMBE};
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
use crate::ratio::algebraic::interval_difference;
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
            masses: Vec::new(),
            dormant: Vec::new(),
        })
    }
    /// The fixed face's numerators and denominators.
    fn declaration(&self) -> Declaration {
        Declaration::new(
            "fixed face",
            self.face
                .iter()
                .flat_map(|class| {
                    [
                        class.numer().try_into().unwrap_or(u64::MAX),
                        class.denom().try_into().unwrap_or(u64::MAX),
                    ]
                })
                .collect(),
        )
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

// -------------------------------------------------------------------------------------------
// campaign 3 at the population: dormancy, death as an exchange, birth from reserved mass

/// The exact forward mixture over (key, activity) in ℚ (Lean `Dormancy.dormant_survivor_code`'s
/// mixture): the uniform key prior, the opening a step from every layer active, the fixed share at
/// `α = 2^(−j)` per layer, a state's face `[class(sounding, a) = x]`; its face of each cell.
fn exact_dormant_faces(mut emitters: Box<dyn Layered>, rung: u32, cells: &[usize]) -> Vec<Rat> {
    let (keys, layers) = (emitters.keys() as usize, emitters.layers());
    let masks = 1usize << layers;
    let alpha = Rat::new(BigInt::one(), BigInt::one() << rung as usize);
    let stay = Rat::one() - &alpha;
    let opening: Vec<Rat> = (0..masks)
        .map(|mask| {
            (0..layers)
                .map(|layer| {
                    if mask & (1 << layer) != 0 {
                        stay.clone()
                    } else {
                        alpha.clone()
                    }
                })
                .product::<Rat>()
                / Rat::from_integer(BigInt::from(keys))
        })
        .collect();
    let mut weights: Vec<Rat> = (0..keys).flat_map(|_| opening.clone()).collect();
    let mut faces = Vec::new();
    for &cell in cells {
        let total: Rat = weights.iter().sum();
        let mut emitted = Rat::zero();
        for key in 0..keys {
            let sounding = emitters.sounding(key as u64);
            for mask in 0..masks {
                let w = &mut weights[key * masks + mask];
                if emitters.class(sounding, mask) == cell {
                    emitted += &*w;
                } else {
                    *w = Rat::zero();
                }
            }
        }
        faces.push(if total.is_zero() {
            Rat::zero()
        } else {
            emitted / total
        });
        for key in 0..keys {
            for layer in 0..layers {
                let bit = 1 << layer;
                for mask in 0..masks {
                    if mask & bit == 0 {
                        let (dormant, active) = (
                            weights[key * masks + mask].clone(),
                            weights[key * masks + (mask | bit)].clone(),
                        );
                        weights[key * masks + mask] = &stay * &dormant + &alpha * &active;
                        weights[key * masks + (mask | bit)] = &alpha * &dormant + &stay * &active;
                    }
                }
            }
        }
        emitters.advance(cell).unwrap();
    }
    faces
}

/// The hand moiré's cells with grating `silent` dormant over `[from, to)`: a dormant ring's layer
/// reads `0` while its clock keeps turning (the terrain's `Moire::emit_active`).
fn dormant_passage(
    class: MoireClass,
    silent: usize,
    from: usize,
    to: usize,
    n: usize,
) -> Vec<usize> {
    let moire = hand_moire(class);
    let every = moire.emit(n);
    let mut active = vec![true; 2];
    active[silent] = false;
    let quiet = moire.emit_active(n, &active);
    (0..n)
        .map(|t| {
            if (from..to).contains(&t) {
                quiet[t]
            } else {
                every[t]
            }
        })
        .collect()
}

/// Lean `Dormancy.dormant_survivor_code`'s mixture, executed: on a ring silent for 40 of 120 cells
/// (the sheet tuple, one factor a ring) and on the parity of two rings over `q ≤ 3`, every executed
/// face is the exact forward mixture's (stepped in ℚ over key and activity) within a relative
/// `2^(−40)`, and zero exactly where it is zero: the chart never kills or revives a state.
#[test]
fn the_dormant_filter_executes_the_exact_forward_mixture() {
    let rung = 3;
    let sheets = dormant_passage(MoireClass::Sheets, 0, 40, 80, 120);
    let ring = MoireFamily {
        rings: 1,
        denominator: 4,
    };
    for factor in 0..2 {
        let digits: Vec<usize> = sheets.iter().map(|&cell| (cell >> factor) & 1).collect();
        let exact = exact_dormant_faces(Box::new(GratingSheet::new(&ring).unwrap()), rung, &digits);
        let mut family = DormantFamily::new(
            "one ring".to_string(),
            0,
            vec![
                Dormancy::new(
                    Box::new(GratingSheet::new(&ring).unwrap()),
                    rung,
                    1 << 16,
                    "",
                )
                .unwrap(),
            ],
        )
        .unwrap();
        for (t, (&digit, ideal)) in digits.iter().zip(&exact).enumerate() {
            let face = family.receive(digit).unwrap();
            assert_eq!(face.is_zero(), ideal.is_zero(), "ring {factor}, cell {t}");
            if !ideal.is_zero() {
                let gap = (&face - ideal).abs() / ideal;
                assert!(
                    gap < Rat::new(BigInt::one(), BigInt::one() << 40usize),
                    "cell {t}"
                );
            }
        }
        assert!(family.drift() < Rat::new(BigInt::one(), BigInt::one() << 40usize));
    }
    let pair = MoireFamily {
        rings: 2,
        denominator: 3,
    };
    let moire = Moire::new(
        vec![
            Grating::new(1, 3, 1).unwrap(),
            Grating::new(1, 2, 0).unwrap(),
        ],
        MoireClass::Parity,
    )
    .unwrap();
    let every = moire.emit(60);
    let quiet = moire.emit_active(60, &[false, true]);
    let cells: Vec<usize> = (0..60)
        .map(|t| {
            if (20..40).contains(&t) {
                quiet[t]
            } else {
                every[t]
            }
        })
        .collect();
    let exact = exact_dormant_faces(Box::new(GratingParity::new(&pair).unwrap()), rung, &cells);
    let mut family = DormantFamily::gratings(&pair, MoireClass::Parity, 1 << 16, rung, 0).unwrap();
    for (t, (&cell, ideal)) in cells.iter().zip(&exact).enumerate() {
        let face = family.receive(cell).unwrap();
        assert_eq!(face.is_zero(), ideal.is_zero(), "parity, cell {t}");
        let gap = (&face - ideal).abs() / ideal;
        assert!(
            gap < Rat::new(BigInt::one(), BigInt::one() << 40usize),
            "cell {t}"
        );
    }
}

/// **A dormant ring keeps its key** (Lean `Dormancy.dormant_survivor_code`, `share_path_code`): on
/// the hand moiré's sheet tuple with ring 0 silent over cells `[40, 80)`, the static family dies at
/// the first silent cell that changes, with ring 0's factor exhausted; the dormant family keeps ring
/// 0's grating and its mirror through the silent aeon, believes the layer dormant at its end, locates
/// the ring again after its return, and codes within `log₂ |K| − log₂ #S_σ` plus the truth path's
/// switching code (two switches of ring 0, none of ring 1) and the certified drift.
#[test]
fn a_dormant_ring_keeps_its_key_through_its_silent_aeon() {
    let rung = 7;
    let n = 120;
    let cells = dormant_passage(MoireClass::Sheets, 0, 40, 80, n);
    let family = small_family();
    let mut fixed = KeyFamily::gratings(&family, MoireClass::Sheets, 1 << 16, 0).unwrap();
    let first_zero = cells
        .iter()
        .position(|&cell| fixed.receive(cell).unwrap().is_zero())
        .expect("the static family dies in the silent aeon");
    assert!((40..80).contains(&first_zero));
    assert_eq!(fixed.exhausted(), Some(0));

    let mut dormant =
        DormantFamily::gratings(&family, MoireClass::Sheets, 1 << 16, rung, 0).unwrap();
    let truth = [vec![1u64, 4, 0], vec![1, 3, 1]];
    let ring = |family: &DormantFamily| -> (Vec<Vec<u64>>, Vec<Rat>, Rat) {
        let Readout::Keys(readout) = family.readout() else {
            unreachable!()
        };
        (
            readout.survivors[0].clone(),
            readout.masses[0].clone(),
            readout.dormant[0][0].clone(),
        )
    };
    for (t, &cell) in cells.iter().enumerate() {
        if t == 80 {
            // The end of the silent aeon: ring 0's key is retained, its layer believed dormant.
            let (survivors, _, dormant_mass) = ring(&dormant);
            assert!(survivors.contains(&truth[0]));
            assert!(dormant_mass > rat(1, 2));
        }
        assert!(!dormant.receive(cell).unwrap().is_zero(), "cell {t}");
    }
    // Located again at the return: the ring is active and its fibre (the grating and its mirror)
    // holds its posterior.
    let (survivors, masses, dormant_mass) = ring(&dormant);
    assert!(dormant_mass < rat(1, 2));
    let mirror = GratingSheet::mirror(&Grating::new(1, 4, 0).unwrap()).unwrap();
    let mirror = vec![mirror.numerator(), mirror.denominator(), mirror.phase()];
    let fibre: Rat = survivors
        .iter()
        .zip(&masses)
        .filter(|(key, _)| **key == truth[0] || **key == mirror)
        .map(|(_, mass)| mass.clone())
        .sum();
    assert!(fibre > rat(1, 2));

    // The bound: each ring keeps its grating and mirror on its active cells (#S_σ = 2 · 2 of
    // 16 · 16); ring 0 opens active, switches twice and stays 117 times; ring 1 stays 119 times.
    let alpha = Rat::new(BigInt::one(), BigInt::one() << rung as usize);
    let stay = Rat::one() - &alpha;
    let power = |base: &Rat, exponent: usize| (0..exponent).map(|_| base.clone()).product::<Rat>();
    let path = &stay * power(&alpha, 2) * power(&stay, n - 1 - 2) * &stay * power(&stay, n - 1);
    let bound = code_length(&(rat(4, 256) * path)).unwrap();
    let code = dormant.likelihood().code().unwrap().unwrap();
    assert!(code.lower <= &bound.upper + dormant.drift());
}

/// Lean `Population.death_is_an_exchange`: the gratings die at the flipped cell and their mass
/// passes to the survivors in proportion to their posteriors, which sum to it exactly; the receipt
/// names the killing cell, what arrived, the dead family's last face (it predicted the other class
/// with certainty) and the exhausted factor; the dying mass and shares enclose the exact ones. A cell
/// every living family gives zero is refused and moves nothing.
#[test]
fn death_is_an_exchange() {
    let mut cells = hand_moire(MoireClass::Parity).emit(60);
    cells[36] = 1 - cells[36];
    let mut population = Population::new(families(true)).unwrap();
    let reception = population.receive_passage(&cells).unwrap();
    assert_eq!(reception.deaths.len(), 1);
    let death = &reception.deaths[0];
    assert_eq!(
        (death.family, death.cell, death.arrived),
        (1, 36, cells[36])
    );
    assert_eq!(death.factor, Some(0));
    let mut predicted = vec![Rat::zero(); 2];
    predicted[1 - cells[36]] = Rat::one();
    assert_eq!(death.face, predicted);
    let exchange = death.exact.as_ref().expect("every likelihood is exact");
    let received: Rat = exchange.shares.iter().map(|(_, share)| share.clone()).sum();
    assert_eq!(received, exchange.mass);
    assert_eq!(
        exchange.shares.iter().map(|(g, _)| *g).collect::<Vec<_>>(),
        vec![0, 2]
    );
    assert!(contains(&death.mass, &code_length(&exchange.mass).unwrap()));
    for ((g, bits), (h, share)) in death.shares.iter().zip(&exchange.shares) {
        assert_eq!(g, h);
        assert!(contains(bits, &code_length(share).unwrap()));
    }
    // The survivors' posteriors after the cell are the exchange's shares over the dying mass.
    let before = Population::new(families(true)).unwrap();
    let mut before = before;
    before.receive_passage(&cells[..36]).unwrap();
    let weights: Vec<Rat> = (0..3)
        .map(|f| match before.posterior_of(&[f]).unwrap() {
            Posterior::Bits(bits) => bits.lower,
            Posterior::Dead => unreachable!(),
        })
        .collect();
    assert!(
        weights[1] < Rat::one(),
        "the gratings held most of the mass"
    );

    let mut gratings_only = Population::new(vec![Box::new(
        KeyFamily::gratings(&small_family(), MoireClass::Parity, 1 << 16, 0).unwrap(),
    )])
    .unwrap();
    gratings_only.receive_passage(&cells[..36]).unwrap();
    let code = gratings_only.code().unwrap();
    assert_eq!(
        gratings_only.receive(cells[36]),
        Err(PopulationError::Extinct { cell: 36 })
    );
    assert_eq!(gratings_only.cells(), 36);
    assert_eq!(gratings_only.code().unwrap(), code);
    assert_eq!(gratings_only.died(0), None);
}

/// A family that refuses one class (its declared admission).
struct Refusing {
    inner: Fixed,
    refused: usize,
}

impl Family for Refusing {
    fn label(&self) -> String {
        "refusing".to_string()
    }
    fn alphabet(&self) -> usize {
        self.inner.alphabet()
    }
    fn description(&self) -> u64 {
        self.inner.description()
    }
    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        self.inner.face()
    }
    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        self.inner.receive(cell)
    }
    fn likelihood(&self) -> Likelihood {
        self.inner.likelihood()
    }
    fn readout(&self) -> Readout<'_> {
        self.inner.readout()
    }
    fn declaration(&self) -> Declaration {
        Declaration::new("refusing", vec![self.refused as u64]).with(vec![self.inner.declaration()])
    }
    fn admits(&self, cells: &[usize]) -> Result<(), PopulationError> {
        if cells.contains(&self.refused) {
            return Err(refuse("a refusing family", "it refuses its declared class"));
        }
        Ok(())
    }
}

/// **A refusal moves nothing**: every living family's admission is read before any family
/// receives, so a cell one family refuses, a passage past a tree's declared population and a cell
/// outside the alphabet leave every family, the cells received and the code as they were.
#[test]
fn a_refusal_moves_nothing() {
    let mut population = Population::new(vec![
        Box::new(Fixed::new(vec![rat(1, 3), rat(2, 3)], 1)) as Box<dyn Family>,
        Box::new(TreeFamily::new(tree(2, 2, 8), 2).unwrap()),
        Box::new(Refusing {
            inner: Fixed::new(vec![rat(1, 2), rat(1, 2)], 2),
            refused: 1,
        }),
    ])
    .unwrap();
    population.receive_passage(&[0, 0, 0]).unwrap();
    let code = population.code().unwrap();
    assert!(population.receive(1).is_err());
    assert!(population.receive_passage(&[0, 1]).is_err());
    assert!(population.receive_passage(&[0; 6]).is_err());
    assert!(matches!(
        population.receive(2),
        Err(PopulationError::CellOutside { .. })
    ));
    assert_eq!(population.cells(), 3);
    assert_eq!(population.code().unwrap(), code);
    population.receive_passage(&[0; 5]).unwrap();
    assert_eq!(population.cells(), 8);
}

/// **Birth from reserved mass** (module header): with the declared `M = 1/2` a newborn of 2 bits
/// takes `1/4` of the reserved `1/2`. The population's code does not move at the birth; after it the
/// population's product of faces is `[Σ_f 2^(−ℓ_f) L_f + 2^(−ℓ_g) W_(t_g) L_g]/M_n` exactly (the
/// newborn abstained before its birth). The trigger founds it at the first section after the opening
/// one whose residual passes its description; a candidate past the reserved mass is refused at the
/// declaration.
#[test]
fn a_newborn_draws_from_the_reserved_mass() {
    let cells = vec![1usize; 40];
    let (bad, good) = (vec![rat(2, 3), rat(1, 3)], vec![rat(1, 64), rat(63, 64)]);
    let epoch = 8;
    let good_face = good.clone();
    let mut population = Population::new(vec![Box::new(Fixed::new(bad.clone(), 1))])
        .unwrap()
        .with_founding(Founding {
            epoch,
            candidates: vec![Candidate {
                description: 2,
                found: Box::new(move |_| Ok(Box::new(Fixed::new(good_face.clone(), 2)))),
            }],
            reseed: false,
        })
        .unwrap();
    assert_eq!(population.reserved(), rat(1, 2));
    let mut births = Vec::new();
    for &cell in &cells {
        let reception = population.receive(cell).unwrap();
        if !reception.births.is_empty() {
            // The population's code does not move at a birth: it encloses the unborn population's.
            let mut unborn = Population::new(vec![Box::new(Fixed::new(bad.clone(), 1))]).unwrap();
            unborn
                .receive_passage(&cells[..population.cells()])
                .unwrap();
            assert!(contains(
                &population.code().unwrap(),
                &unborn.code().unwrap()
            ));
        }
        births.extend(reception.births);
    }
    assert_eq!(births.len(), 1);
    let birth = &births[0];
    assert_eq!(
        (birth.cell, birth.mass.clone(), birth.reserved.clone()),
        (16, rat(1, 4), rat(1, 4))
    );
    assert_eq!(population.born(1), Some(16));
    assert_eq!(population.founded(), &rat(3, 4));
    // The opening section only opens the reading; the next one's residual `8 log₂ 3` passes the
    // 2 bits: W_(t_g) = (1/3)^16, then W_n = [½ (1/3)^40 + ¼ (1/3)^16 (63/64)^24] / ¾.
    let w_birth = power(&rat(1, 3), 16);
    assert!(contains(&birth.inherited, &code_length(&w_birth).unwrap()));
    let exact = (rat(1, 2) * power(&rat(1, 3), 40)
        + rat(1, 4) * &w_birth * power(&rat(63, 64), 24))
        / rat(3, 4);
    assert!(contains(
        &population.code().unwrap(),
        &code_length(&exact).unwrap()
    ));
    assert_eq!(population.receipt().unwrap().selected, Some(1));

    assert!(
        Population::new(vec![Box::new(Fixed::new(bad, 1))])
            .unwrap()
            .with_founding(Founding {
                epoch,
                candidates: vec![Candidate {
                    description: 0,
                    found: Box::new(|_| unreachable!()),
                }],
                reseed: false,
            })
            .is_err()
    );
}

fn power(base: &Rat, exponent: usize) -> Rat {
    (0..exponent).map(|_| base.clone()).product()
}

/// **The parity class locates one word, not one rate** (the families' module header): on the
/// notebook's drawn moiré (`k = 3`, `q ≤ 2^3`, its seed), the survivors after 840 ticks are exactly
/// the keys whose parity word matches (a brute force over the `122³` keys by each grating's word
/// as bits), `720 = 2⁴·3²·5` of them, split by denominators as `(7, 8, 8)` 384, `(3, 6, 7)` 144,
/// `(2, 7, 7)` 96 and `(4, 4, 7)` 96: 336 hold no period-8 pair and 384 no `5/7` ring.
#[test]
fn the_parity_fibre_is_one_word_not_one_rate() {
    let family = MoireFamily {
        rings: 3,
        denominator: 8,
    };
    let moire = Moire::draw(&family, MoireClass::Parity, &mut Draw::new(20_260_927)).unwrap();
    let ticks = 840;
    let cells = moire.emit(ticks);
    let mut keys = KeyFamily::gratings(&family, MoireClass::Parity, 1 << 24, 0).unwrap();
    for &cell in &cells {
        keys.receive(cell).unwrap();
    }
    let gratings: Vec<Grating> = (0..family.gratings())
        .map(|i| family.grating(i).unwrap())
        .collect();
    let words = |bits: &dyn Fn(u64) -> bool| -> Vec<u64> {
        let mut word = vec![0u64; ticks.div_ceil(64)];
        for t in 0..ticks as u64 {
            if bits(t) {
                word[(t / 64) as usize] |= 1 << (t % 64);
            }
        }
        word
    };
    let sheets: Vec<Vec<u64>> = gratings.iter().map(|g| words(&|t| g.sheet(t))).collect();
    let target = words(&|t| cells[t as usize] == 1);
    let mut brute: Vec<Vec<u64>> = Vec::new();
    for (a, first) in sheets.iter().enumerate() {
        for (b, second) in sheets.iter().enumerate() {
            let pair: Vec<u64> = first.iter().zip(second).map(|(x, y)| x ^ y).collect();
            for (c, third) in sheets.iter().enumerate() {
                if pair
                    .iter()
                    .zip(third)
                    .zip(&target)
                    .all(|((x, y), z)| x ^ y == *z)
                {
                    brute.push(
                        [a, b, c]
                            .iter()
                            .flat_map(|&i| {
                                let g = &gratings[i];
                                [g.numerator(), g.denominator(), g.phase()]
                            })
                            .collect(),
                    );
                }
            }
        }
    }
    let Readout::Keys(readout) = keys.readout() else {
        unreachable!()
    };
    let mut survivors = readout.survivors[0].clone();
    survivors.sort();
    brute.sort();
    assert_eq!(survivors, brute);
    assert_eq!(survivors.len(), 720);
    let mut by_denominators = std::collections::BTreeMap::new();
    for key in &survivors {
        let mut qs = vec![key[1], key[4], key[7]];
        qs.sort();
        *by_denominators.entry(qs).or_insert(0usize) += 1;
    }
    let expected: std::collections::BTreeMap<Vec<u64>, usize> = [
        (vec![7, 8, 8], 384),
        (vec![3, 6, 7], 144),
        (vec![2, 7, 7], 96),
        (vec![4, 4, 7], 96),
    ]
    .into_iter()
    .collect();
    assert_eq!(by_denominators, expected);
    let without_five_sevenths = survivors
        .iter()
        .filter(|key| !key.chunks(3).any(|g| g[0] == 5 && g[1] == 7))
        .count();
    assert_eq!(without_five_sevenths, 384);
    assert!(survivors.contains(&vec![1, 2, 1, 1, 7, 3, 1, 7, 5]));
}

/// **A death keeps the seed** (module header): a parity moiré of two rings (`3/7 @ 2/7`,
/// `5/8 @ 1/8`, joint period `56`) for 168 cells, then another (`1/5 @ 0`, `2/3 @ 1/3`) for 168,
/// then the first again at its continued phase. The static gratings locate the first, die when the
/// second contradicts every key they hold (the receipt names their seed), and the population
/// re-founds the seed from its reserved mass at a section whose residual passes the charge. Each
/// seed that dies in the second aeon returns to the dead family; the one re-founded as the third
/// aeon opens codes it near its unswitched code (the seed's surviving fibre) plus its birth
/// charge, not the tree's.
#[test]
fn a_death_keeps_the_seed_and_the_seed_is_refounded() {
    let family = MoireFamily {
        rings: 2,
        denominator: 8,
    };
    let first = Moire::new(
        vec![
            Grating::new(3, 7, 2).unwrap(),
            Grating::new(5, 8, 1).unwrap(),
        ],
        MoireClass::Parity,
    )
    .unwrap();
    let second = Moire::new(
        vec![
            Grating::new(1, 5, 0).unwrap(),
            Grating::new(2, 3, 1).unwrap(),
        ],
        MoireClass::Parity,
    )
    .unwrap();
    let (aeon, n) = (168usize, 504usize);
    let (a, b) = (first.emit(n), second.emit(n));
    let cells: Vec<usize> = (0..n)
        .map(|t| {
            if (aeon..2 * aeon).contains(&t) {
                b[t]
            } else {
                a[t]
            }
        })
        .collect();
    let mut population = Population::new(vec![
        Box::new(TreeFamily::new(tree(2, 4, n), 2).unwrap()) as Box<dyn Family>,
        Box::new(KeyFamily::gratings(&family, MoireClass::Parity, 1 << 24, 2).unwrap()),
    ])
    .unwrap()
    .with_founding(Founding {
        epoch: 24,
        candidates: Vec::new(),
        reseed: true,
    })
    .unwrap();
    let opening = population.receive_passage(&cells[..2 * aeon]).unwrap();
    let death = opening
        .deaths
        .iter()
        .find(|death| death.family == 1)
        .expect("the gratings die in the second aeon");
    assert!((aeon..2 * aeon).contains(&death.cell));
    let seed = death.seed.as_ref().expect("a key family's seed");
    assert!(seed.survivors[0].contains(&vec![3, 7, 2, 5, 8, 1]));
    let at_opening = population.code().unwrap();
    let tree_at_opening = population.receipt().unwrap().families[0]
        .code
        .clone()
        .unwrap();
    let birth = opening
        .births
        .iter()
        .find(|birth| birth.cell == 2 * aeon)
        .expect("the seed re-founded as the third aeon opens");
    // Every earlier seed died in the second aeon, and returned to the dead family.
    assert!(
        opening
            .births
            .iter()
            .filter(|b| b.cell < 2 * aeon)
            .all(|b| population.died(b.family).is_some() && b.seed == Some(1))
    );
    population.receive_passage(&cells[2 * aeon..]).unwrap();
    assert_eq!(birth.seed, Some(1));
    let newborn = birth.family;
    assert_eq!(
        population.died(newborn),
        None,
        "the seed codes the third aeon"
    );
    let receipt = population.receipt().unwrap();
    let paid = interval_difference(&receipt.code, &at_opening).unwrap();
    let tree_paid =
        interval_difference(receipt.families[0].code.as_ref().unwrap(), &tree_at_opening).unwrap();
    // Near the unswitched code plus the birth charge: its posterior at its birth is its mass over
    // the founded mass, and the seed's survivors keep one word.
    let founded_at_birth = population.founded().clone();
    let charge = code_length(&(&birth.mass / founded_at_birth * rat(1, 2))).unwrap();
    assert!(
        paid.upper < &charge.upper + Rat::one(),
        "paid {paid:?}, charge {charge:?}"
    );
    assert!(paid.upper < tree_paid.lower, "the tree pays more");
}
