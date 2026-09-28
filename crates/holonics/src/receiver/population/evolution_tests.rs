//! The population's remaining terms checked exactly on small fixtures: a family's identity across
//! re-founding and a new aeon, the evolved prior as the Dirichlet face of the retained counts (KT with
//! no deaths) with its normalization and code bound, founding at a declared mass, species collapse
//! (no code moves over the admitted future, a collapsed family refuses past it, and a species splits
//! when the future grows), species within a composed egg, the composed egg re-founded from its
//! seed, and the work each family reports.

use std::sync::Arc;

use num_bigint::BigUint;
use num_traits::{One, Zero};

use super::composition::{Conditioned, Keystone, Port, PortPath, PortReader, PortedEmitters};
use super::tests::Fixed;
use super::*;
use crate::compression::landmark::context::{
    Capacity, LandmarkDeclaration, LetterFamily, StopPrior, ratio_code_length,
};
use crate::hnn::field::{Field, FieldDeclaration};
use crate::holarchy::terrain::arithmetic::{
    DigitOrder, PrimeEmission, PrimeWindow, ProductCell, ProductFamily, Products,
};
use crate::holarchy::terrain::{
    Draw, Grating, Moire, MoireClass, MoireFamily, RotorCrib, TreeSource, TreeSourceFamily,
};
use crate::ratio::rat;

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

fn gratings(class: MoireClass, description: u64) -> KeyFamily {
    KeyFamily::gratings(&small_family(), class, 1 << 16, description).unwrap()
}

/// `−log₂ x`, enclosed.
fn bits(x: &Rat) -> ExactInterval {
    ratio_code_length(x.numer().magnitude(), x.denom().magnitude()).unwrap()
}

/// A family's identity is its declaration and description: the same declaration built again, in a
/// new aeon or re-founded from its seed, carries it; a tree's is independent of the aeon's
/// alphabet and passage; another description or class is another identity.
#[test]
fn a_familys_identity_is_its_declaration_across_aeons_and_refounding() {
    let parity = gratings(MoireClass::Parity, 3);
    assert_eq!(
        parity.identity(),
        gratings(MoireClass::Parity, 3).identity()
    );
    assert_ne!(
        parity.identity(),
        gratings(MoireClass::Parity, 4).identity()
    );
    assert_ne!(
        parity.identity(),
        gratings(MoireClass::Sheets, 3).identity()
    );
    let reseeded = parity
        .reseed(5)
        .expect("a moiré's rings wind without the cells");
    assert_ne!(reseeded.label(), parity.label());
    assert_eq!(reseeded.identity(), parity.identity());
    let short = TreeFamily::new(tree(2, 4, 64), 3).unwrap();
    let wide = TreeFamily::new(tree(13, 4, 1 << 20), 3).unwrap();
    assert_eq!(short.identity(), wide.identity());
    assert_ne!(
        short.identity(),
        TreeFamily::new(tree(2, 8, 64), 3).unwrap().identity()
    );
    let family = ProductFamily {
        base: 10,
        digits: 2,
        face: 1,
        order: DigitOrder::LeastFirst,
    };
    let composed = Composed::products(&family, 1).unwrap();
    assert_eq!(
        composed.identity(),
        Composed::products(&family, 1).unwrap().identity()
    );
    assert_eq!(composed.reseed(19).unwrap().identity(), composed.identity());
    assert_ne!(
        composed.identity(),
        Composed::products(
            &ProductFamily {
                base: 16,
                ..family.clone()
            },
            1
        )
        .unwrap()
        .identity()
    );
}

/// Every key family's identity is its declaration, unmoved by a passage: the moiré's gratings (both
/// classes, static and dormant), the rotor crib's keys (its declared configurations, never the
/// field's lift the cells step) and the composed arithmetic eggs carry after reading their terrain
/// the identity they carried before it.
#[test]
fn a_key_familys_identity_is_unmoved_by_a_passage() {
    let parity = hand_moire(MoireClass::Parity).emit(24);
    let sheets = hand_moire(MoireClass::Sheets).emit(24);
    let mut declared = FieldDeclaration::campaign_one(1 << 16);
    declared.rings[1].lock = (0..7).collect();
    let field = Field::declare(declared).unwrap();
    let configurations = [0u64, 0, 0, 0];
    let crib = RotorCrib::draw(&field, 1, &configurations, 64, &mut Draw::new(41)).unwrap();
    let products = ProductFamily {
        base: 10,
        digits: 2,
        face: 1,
        order: DigitOrder::LeastFirst,
    };
    let product_cells = Products::draw(&products, 4, &mut Draw::new(7))
        .unwrap()
        .emit();
    let window = PrimeWindow {
        base: 10,
        start: 137,
        end: 400,
        digits: 3,
        trailing: 1,
        order: DigitOrder::MostFirst,
        emission: PrimeEmission::Digits,
    };
    let prime_cells = window.emit().unwrap();
    let dormant = |class| DormantFamily::gratings(&small_family(), class, 1 << 16, 4, 3).unwrap();
    let passages: Vec<(Box<dyn Family>, &[usize])> = vec![
        (Box::new(gratings(MoireClass::Parity, 3)), &parity),
        (Box::new(gratings(MoireClass::Sheets, 3)), &sheets),
        (Box::new(dormant(MoireClass::Parity)), &parity),
        (Box::new(dormant(MoireClass::Sheets)), &sheets),
        (
            Box::new(KeyFamily::rotor(&field, 1, &configurations, 1 << 24, 3).unwrap()),
            &crib.cells,
        ),
        (
            Box::new(Composed::products(&products, 3).unwrap()),
            &product_cells,
        ),
        (
            Box::new(Composed::primes(&window, 1 << 20, 3).unwrap()),
            &prime_cells[..40],
        ),
    ];
    for (mut family, cells) in passages {
        let before = family.identity();
        for &cell in cells {
            family.receive(cell).unwrap();
        }
        assert_eq!(family.identity(), before, "{}", family.label());
    }
}

/// The survival pseudo-count: `½` without a death (the KT count), `(2(a − d) + 1)/(2(2a + 1))`.
#[test]
fn the_survival_pseudo_count_is_kts_half_until_a_death() {
    let tally = |declared, died| Tally {
        declared,
        selected: 0,
        died,
    };
    assert_eq!(tally(0, 0).pseudo(), rat(1, 2));
    assert_eq!(tally(5, 0).pseudo(), rat(1, 2));
    assert_eq!(tally(1, 1).pseudo(), rat(1, 6));
    assert_eq!(tally(2, 1).pseudo(), rat(3, 10));
    assert!(tally(4, 2).pseudo() < tally(4, 1).pseudo());
}

/// Two aeons read into the retention (a moiré, where the gratings are selected; a tree source,
/// where they die and the tree is selected), then the evolved prior of the third: its Dirichlet
/// face is exact, KT after the first aeon, normalized, mixed at `λ = ½` with the description
/// prior; the evolved population keeps the static total mass; and the third aeon's code is at most
/// the selected family's code plus `−log₂` of its evolved prior.
#[test]
fn the_evolved_prior_is_the_dirichlet_face_of_the_retained_counts() {
    let aeon = |cells: &[usize], selections: Option<&Selections>| {
        let families: Vec<Box<dyn Family>> = vec![
            Box::new(TreeFamily::new(tree(2, 2, 1 << 10), 2).unwrap()),
            Box::new(gratings(MoireClass::Parity, 2)),
        ];
        let mut population = match selections {
            Some(selections) => Population::evolved(families, selections, &rat(1, 2)).unwrap(),
            None => Population::new(families).unwrap(),
        };
        population.receive_passage(cells).unwrap();
        population
    };
    let moire = hand_moire(MoireClass::Parity).emit(48);
    let source = TreeSource::draw(
        &TreeSourceFamily {
            alphabet: 2,
            depth: 2,
            grid: 16,
        },
        &mut Draw::new(11),
    )
    .unwrap()
    .emit(96, &mut Draw::new(12));
    let mut selections = Selections::new();
    let first = aeon(&moire, None).receipt().unwrap();
    assert_eq!(first.selected, Some(1), "the gratings made the moiré");
    selections.record(&first);
    let declared: Vec<Identity> = first.families.iter().map(|f| f.identity.clone()).collect();
    assert_eq!(
        selections.face(&declared).unwrap(),
        vec![rat(1, 4), rat(3, 4)]
    );

    let second = aeon(&source, None).receipt().unwrap();
    assert!(
        second.families[1].died.is_some(),
        "the gratings die on the tree source"
    );
    assert_eq!(second.selected, Some(0));
    selections.record(&second);
    assert_eq!(selections.aeons(), 2);
    assert_eq!(
        selections.tally(&declared[1]),
        Tally {
            declared: 2,
            selected: 1,
            died: 1
        }
    );
    // D: tree (1 + ½), gratings (1 + 3/10), over 28/10.
    assert_eq!(
        selections.face(&declared).unwrap(),
        vec![rat(15, 28), rat(13, 28)]
    );
    let prior = selections.prior(&declared, &rat(1, 2)).unwrap();
    assert_eq!(prior, vec![rat(29, 56), rat(27, 56)]);
    assert_eq!(prior.iter().sum::<Rat>(), Rat::one());
    assert!(
        selections
            .face(&[declared[0].clone(), declared[0].clone()])
            .is_err()
    );

    let third = aeon(&moire, Some(&selections));
    assert_eq!(
        third.mass(),
        &rat(1, 2),
        "the static total: the reserve is unchanged"
    );
    assert_eq!(third.prior(1), Some(&rat(27, 56)));
    let receipt = third.receipt().unwrap();
    assert_eq!(receipt.selected, Some(1));
    let bound = interval_sum(
        receipt.families[1].code.as_ref().unwrap(),
        &bits(&rat(27, 56)),
    )
    .unwrap();
    // Decided below, not merely unrefuted: the enclosed slack `bound − code` is positive.
    assert!(receipt.code.upper < bound.lower);
    // Against the static prior's ½ the gratings' death costs this aeon: it codes more.
    let stat = aeon(&moire, None).receipt().unwrap();
    assert!(receipt.code.lower > stat.code.upper);
}

/// **The evolved aeon bound with a birth** (module header of `evolution`): one evolved family at
/// `M = ½, π = 1` and a newborn of mass `¼` that dies at the next cell. The no-birth form
/// `−log₂ π(f) − log₂ L_f` is exceeded, decided, by `log₂(3/2)`; the bound over the founded mass,
/// `−log₂(m_f/M_n) − log₂ L_f` at `m_f/M_n = (½)/(¾) = 2/3`, is not refuted (it is the code itself
/// here: every newborn died).
#[test]
fn the_evolved_aeon_bound_with_a_birth_is_over_the_founded_mass() {
    let fair = Box::new(Fixed::new(vec![rat(1, 2), rat(1, 2)], 1)) as Box<dyn Family>;
    let mut population = Population::evolved(vec![fair], &Selections::new(), &rat(1, 2)).unwrap();
    assert_eq!(population.mass(), &rat(1, 2));
    let opening = population.prior(0).unwrap().clone();
    assert_eq!(opening, Rat::one());
    population.receive_passage(&[0, 1, 0]).unwrap();
    let newborn = Fixed::new(vec![Rat::one(), Rat::zero()], 2);
    population
        .found_with(Box::new(newborn), rat(1, 4), None)
        .unwrap();
    population.receive(1).unwrap();
    assert!(
        population.died(1).is_some(),
        "the newborn dies at the next cell"
    );
    assert_eq!(population.prior(0), Some(&rat(2, 3)), "m_f/M_n");
    let code = population.code().unwrap();
    let own = bits(&rat(1, 16));
    let unrestricted = interval_sum(&bits(&opening), &own).unwrap();
    let corrected = interval_sum(&bits(&rat(2, 3)), &own).unwrap();
    assert!(
        code.lower > unrestricted.upper,
        "the no-birth form is exceeded"
    );
    let excess = ExactInterval {
        lower: &code.lower - &unrestricted.upper,
        upper: &code.upper - &unrestricted.lower,
    };
    let three_halves = bits(&rat(2, 3));
    assert!(excess.lower <= three_halves.upper && three_halves.lower <= excess.upper);
    assert!(
        code.lower <= corrected.upper && corrected.lower <= code.upper,
        "the bound over the founded mass is not refuted"
    );
}

/// Founding at a declared rational mass: the newborn draws it from the reserve and the population's
/// code does not move.
#[test]
fn a_family_is_founded_at_a_declared_mass() {
    let cells = hand_moire(MoireClass::Parity).emit(12);
    let mut population =
        Population::new(vec![Box::new(TreeFamily::new(tree(2, 2, 64), 1).unwrap())]).unwrap();
    population.receive_passage(&cells).unwrap();
    let before = population.code().unwrap();
    let birth = population
        .found_with(Box::new(gratings(MoireClass::Parity, 3)), rat(3, 16), None)
        .unwrap();
    assert_eq!((birth.mass, birth.reserved), (rat(3, 16), rat(5, 16)));
    assert_eq!(population.code().unwrap(), before);
    assert!(
        population
            .found_with(Box::new(gratings(MoireClass::Parity, 3)), rat(1, 2), None)
            .is_err()
    );
}

/// Every surviving parity key emits one word forever, so over the whole future the survivors are
/// one species: the collapse keeps one member at their summed posterior, the population's code,
/// face and posteriors do not move, and the collapsed population codes every later cell as its
/// uncollapsed twin does.
#[test]
fn a_collapse_over_the_whole_future_changes_no_code() {
    let cells = hand_moire(MoireClass::Parity).emit(64);
    let declare = || {
        Population::new(vec![
            Box::new(TreeFamily::new(tree(2, 2, 64), 1).unwrap()) as Box<dyn Family>,
            Box::new(gratings(MoireClass::Parity, 1)),
        ])
        .unwrap()
    };
    let (mut population, mut twin) = (declare(), declare());
    population.receive_passage(&cells[..24]).unwrap();
    twin.receive_passage(&cells[..24]).unwrap();
    let (code, face) = (population.code().unwrap(), population.face().unwrap());
    let collapse = population.collapse(1, AdmittedFuture::Whole).unwrap();
    let survivors = twin
        .families()
        .nth(1)
        .map(|family| match family.readout() {
            Readout::Keys(keys) => keys.count(),
            _ => unreachable!(),
        })
        .unwrap();
    assert_eq!(BigUint::from(collapse.before()), survivors);
    assert_eq!(collapse.after(), 1, "one word, one species");
    let Collapse::Keys { factors, .. } = &collapse else {
        unreachable!()
    };
    assert_eq!(factors[0].species[0].posterior, Rat::one());
    assert_eq!(population.code().unwrap(), code);
    assert_eq!(population.face().unwrap(), face);
    assert_eq!(
        population.posterior_of(&[1]).unwrap(),
        twin.posterior_of(&[1]).unwrap()
    );
    for &cell in &cells[24..] {
        population.receive(cell).unwrap();
        twin.receive(cell).unwrap();
        assert_eq!(population.code().unwrap(), twin.code().unwrap());
    }
}

/// The sheet tuple's rings each keep their grating and its mirror, one species a ring.
#[test]
fn a_rings_grating_and_its_mirror_are_one_species() {
    let cells = hand_moire(MoireClass::Sheets).emit(24);
    let mut family = gratings(MoireClass::Sheets, 0);
    for &cell in &cells {
        assert!(!family.receive(cell).unwrap().is_zero());
    }
    let likelihood = family.likelihood();
    let Some(Collapse::Keys { factors, .. }) = family.collapse(AdmittedFuture::Whole).unwrap()
    else {
        unreachable!()
    };
    for factor in &factors {
        assert_eq!(factor.before, 2);
        assert_eq!(factor.species.len(), 1);
        let species = &factor.species[0];
        let mirror = GratingSheet::mirror(
            &Grating::new(
                species.coordinates[0][0],
                species.coordinates[0][1],
                species.coordinates[0][2],
            )
            .unwrap(),
        )
        .unwrap();
        assert_eq!(
            species.coordinates[1],
            vec![mirror.numerator(), mirror.denominator(), mirror.phase()]
        );
    }
    assert_eq!(family.likelihood(), likelihood);
}

/// A species relative to a short admitted future is wider than the whole future's: at the same
/// cell the whole future splits what one tick merges (60 survivors: 2 species over the next tick,
/// 7 over every tick). Collapsed over one tick, the family refuses a second cell and codes the one
/// as its uncollapsed twin does; split from its receipt it holds its twin's survivors again, each one
/// member, and it codes every later cell as its twin.
#[test]
fn a_species_splits_when_the_admitted_future_grows() {
    let cells = hand_moire(MoireClass::Parity).emit(40);
    let (mut family, mut twin, mut wide) = (
        gratings(MoireClass::Parity, 0),
        gratings(MoireClass::Parity, 0),
        gratings(MoireClass::Parity, 0),
    );
    for &cell in &cells[..2] {
        family.receive(cell).unwrap();
        twin.receive(cell).unwrap();
        wide.receive(cell).unwrap();
    }
    let short = family.collapse(AdmittedFuture::Ticks(1)).unwrap().unwrap();
    let whole = wide.collapse(AdmittedFuture::Whole).unwrap().unwrap();
    assert_eq!(short.before(), whole.before());
    assert_eq!(
        (short.before(), short.after(), whole.after()),
        (60, 2, 7),
        "the whole future splits what one tick merges"
    );
    assert_eq!(family.face().unwrap(), twin.face().unwrap());
    assert!(family.admits(&cells[2..4]).is_err());
    assert!(family.admits(&cells[2..3]).is_ok());
    for &cell in &cells[2..3] {
        let face = twin.receive(cell).unwrap();
        assert_eq!(family.receive(cell).unwrap(), face);
        assert_eq!(wide.receive(cell).unwrap(), face);
    }
    assert_eq!(family.likelihood(), twin.likelihood());
    family.split(&short).unwrap();
    assert_eq!(
        family.factors()[0].survivors(),
        twin.factors()[0].survivors()
    );
    assert!(
        family.factors()[0]
            .members()
            .iter()
            .all(|&members| members == 1)
    );
    assert!(family.admits(&cells[3..]).is_ok());
    for &cell in &cells[3..] {
        assert_eq!(family.face().unwrap(), twin.face().unwrap());
        let face = twin.receive(cell).unwrap();
        assert_eq!(family.receive(cell).unwrap(), face);
        assert_eq!(wide.receive(cell).unwrap(), face);
    }
    assert_eq!(family.likelihood(), twin.likelihood());
    assert_eq!(wide.likelihood(), twin.likelihood());
}

/// A rotor crib's survivors are the ring's rotor-gauge orbit: their transition tables agree over
/// every stage, so they are one species of 7.
#[test]
fn a_rotor_gauge_orbit_is_one_species() {
    let mut declared = FieldDeclaration::campaign_one(1 << 16);
    declared.rings[1].lock = (0..7).collect();
    let field = Field::declare(declared).unwrap();
    let configurations = [0u64, 0, 0, 0];
    let crib = RotorCrib::draw(&field, 1, &configurations, 64, &mut Draw::new(41)).unwrap();
    let mut keys = KeyFamily::rotor(&field, 1, &configurations, 1 << 24, 0).unwrap();
    for &cell in &crib.cells {
        keys.receive(cell).unwrap();
    }
    let collapse = keys.collapse(AdmittedFuture::Whole).unwrap().unwrap();
    assert_eq!((collapse.before(), collapse.after()), (7, 1));
}

/// A keystone of four phases keyed by its offset, reading the passage's clock.
struct Clock;

impl Keystone for Clock {
    fn label(&self) -> String {
        "clock of 4".to_string()
    }
    fn keys(&self) -> u64 {
        4
    }
    fn port(&self, key: u64, upstream: Port) -> Port {
        Port {
            phase: (key + upstream.winding) % 4,
            winding: (key + upstream.winding) / 4,
        }
    }
    fn coordinates(&self, key: u64) -> Vec<u64> {
        vec![key]
    }
    fn declaration(&self) -> Declaration {
        Declaration::new("clock", vec![4])
    }
}

/// A keystone of one key passing its port through.
struct Pass;

impl Keystone for Pass {
    fn label(&self) -> String {
        "pass".to_string()
    }
    fn keys(&self) -> u64 {
        1
    }
    fn port(&self, _key: u64, upstream: Port) -> Port {
        upstream
    }
    fn coordinates(&self, key: u64) -> Vec<u64> {
        vec![key]
    }
    fn declaration(&self) -> Declaration {
        Declaration::new("pass", Vec::new())
    }
}

/// A reader of the phase's half-turn sheet: the phase mod 2.
struct Half;

impl PortReader for Half {
    fn label(&self) -> String {
        "half".to_string()
    }
    fn alphabet(&self) -> usize {
        2
    }
    fn emit(&self, port: Port) -> usize {
        (port.phase % 2) as usize
    }
    fn declaration(&self) -> Declaration {
        Declaration::new("half", Vec::new())
    }
}

fn clock_half() -> Composed {
    let conditioned: Conditioned = Arc::new(|path| {
        let emitters = PortedEmitters::new(Arc::new(Pass), Arc::new(Half), path)?;
        let factor = Survivors::new(Box::new(emitters), 1, "none")?;
        Ok(
            Box::new(KeyFamily::new("pass ⊳ half".to_string(), 0, vec![factor])?)
                as Box<dyn Family>,
        )
    });
    Composed::new(
        "clock ⊳ (pass ⊳ half)".to_string(),
        0,
        Arc::new(Clock),
        &PortPath::tick(),
        &conditioned,
        4,
    )
    .unwrap()
}

/// Within a composed egg: the clock's offsets 1 and 3 read one half-turn word, so over the admitted
/// future they are one species at the summed posterior; the composed face does not move; past the
/// future the egg refuses; split from its receipt, key 3 returns from its seed at its share and the
/// egg codes every later cell as its uncollapsed twin.
#[test]
fn keystone_keys_reading_one_word_are_one_species_and_split_from_their_seed() {
    let cells: Vec<usize> = (0..24).map(|t| (1 + t) % 2).collect();
    let (mut composed, mut twin) = (clock_half(), clock_half());
    for &cell in &cells[..3] {
        composed.receive(cell).unwrap();
        twin.receive(cell).unwrap();
    }
    assert_eq!(composed.posterior(), vec![(1, rat(1, 2)), (3, rat(1, 2))]);
    let collapse = composed
        .collapse(AdmittedFuture::Ticks(6))
        .unwrap()
        .unwrap();
    assert_eq!((collapse.before(), collapse.after()), (2, 1));
    assert_eq!(composed.posterior(), vec![(1, Rat::one())]);
    assert_eq!(composed.members(), vec![(1, 2)]);
    assert_eq!(composed.face().unwrap(), twin.face().unwrap());
    assert!(composed.admits(&cells[3..10]).is_err());
    for &cell in &cells[3..9] {
        assert_eq!(composed.receive(cell).unwrap(), twin.receive(cell).unwrap());
    }
    composed.split(&collapse).unwrap();
    assert_eq!(composed.posterior(), twin.posterior());
    for &cell in &cells[9..] {
        assert_eq!(composed.face().unwrap(), twin.face().unwrap());
        assert_eq!(composed.receive(cell).unwrap(), twin.receive(cell).unwrap());
    }
    assert_eq!(composed.posterior(), twin.posterior());
}

/// The composed egg re-founded from its seed at a record's boundary: the located clock key and,
/// on a prime stream, the counter's located start carry over, the ports wound to the cell; the
/// newborn reads every determined cell with face one once it has read a record whole.
#[test]
fn a_composed_egg_is_refounded_from_its_seed() {
    let family = ProductFamily {
        base: 10,
        digits: 2,
        face: 1,
        order: DigitOrder::LeastFirst,
    };
    let length = family.record_length();
    let products = Products::draw(&family, 6, &mut Draw::new(7)).unwrap();
    let (cells, classes) = (products.emit(), products.classes());
    let mut composed = Composed::products(&family, 1).unwrap();
    for &cell in &cells[..2 * length] {
        composed.receive(cell).unwrap();
    }
    let mut newborn = composed
        .reseed(2 * length)
        .expect("the clock winds without the cells");
    assert_eq!(newborn.identity(), composed.identity());
    for (t, (&cell, class)) in cells.iter().zip(&classes).enumerate().skip(2 * length) {
        let face = newborn.receive(cell).unwrap();
        let expected = match class {
            ProductCell::Operand => rat(1, 10),
            _ => Rat::one(),
        };
        assert_eq!(face, expected, "cell {t}");
    }

    let window = PrimeWindow {
        base: 10,
        start: 137,
        end: 400,
        digits: 3,
        trailing: 1,
        order: DigitOrder::MostFirst,
        emission: PrimeEmission::Digits,
    };
    let cells = window.emit().unwrap();
    let mut primes = Composed::primes(&window, 1 << 20, 1).unwrap();
    for &cell in &cells[..40] {
        primes.receive(cell).unwrap();
    }
    let mut newborn = primes
        .reseed(40)
        .expect("the clock and counter wind without the cells");
    let Readout::Keys(keys) = newborn.readout() else {
        unreachable!()
    };
    assert_eq!(keys.survivors, vec![vec![vec![0]], vec![vec![137]]]);
    for &cell in &cells[40..] {
        assert_eq!(newborn.receive(cell).unwrap(), Rat::one());
    }
}

/// `pass ⊳ (clock ⊳ half)`: a keystone of one key, and the clock's offsets as the conditioned key
/// family reading the half-turn sheet, named by `description` bits.
fn pass_clock_half(description: u64) -> Composed {
    let conditioned: Conditioned = Arc::new(|path| {
        let emitters = PortedEmitters::new(Arc::new(Clock), Arc::new(Half), path)?;
        let factor = Survivors::new(Box::new(emitters), 4, "none")?;
        Ok(
            Box::new(KeyFamily::new("clock ⊳ half".to_string(), 0, vec![factor])?)
                as Box<dyn Family>,
        )
    });
    Composed::new(
        "pass ⊳ (clock ⊳ half)".to_string(),
        description,
        Arc::new(Pass),
        &PortPath::tick(),
        &conditioned,
        1,
    )
    .unwrap()
}

/// **A composed egg refuses re-founding past a conditioned collapse**, as a key family does: the
/// conditioned family's offsets 1 and 3 are one species over six ticks (the keystone's one key
/// merges nothing), so within that future the egg is re-founded holding the species, and once the
/// future has ended it is refused (split first), never re-founded by declaring the conditioned
/// family anew over its whole key space. In a population the refusal names the split it is owed.
#[test]
fn a_composed_egg_refuses_refounding_past_a_conditioned_collapse() {
    let cells: Vec<usize> = (0..16).map(|t| (1 + t) % 2).collect();
    let mut composed = pass_clock_half(0);
    for &cell in &cells[..3] {
        composed.receive(cell).unwrap();
    }
    composed.collapse(AdmittedFuture::Ticks(6)).unwrap();
    assert_eq!(
        composed.members(),
        vec![(0, 1)],
        "the keystone merges nothing"
    );
    let Readout::Keys(keys) = composed.readout() else {
        unreachable!()
    };
    assert_eq!(
        keys.survivors[1],
        vec![vec![1]],
        "offsets 1 and 3 are one species"
    );
    let within = composed.reseed(5).expect("within the admitted future");
    let Readout::Keys(keys) = within.readout() else {
        unreachable!()
    };
    assert_eq!(
        keys.survivors[1],
        vec![vec![1]],
        "re-founded holding the species"
    );
    assert!(
        composed.reseed(9).is_none(),
        "the future has ended: split first"
    );

    let mut population = Population::new(vec![
        Box::new(TreeFamily::new(tree(2, 2, 64), 1).unwrap()) as Box<dyn Family>,
        Box::new(pass_clock_half(1)),
    ])
    .unwrap();
    population.receive_passage(&cells[..3]).unwrap();
    population.collapse(1, AdmittedFuture::Ticks(6)).unwrap();
    population.receive(1 - cells[3]).unwrap();
    assert_eq!(population.died(1), Some(3));
    population.receive_passage(&cells[4..12]).unwrap();
    assert_eq!(
        population.refound(1, None).unwrap_err(),
        refuse(
            "a re-founding",
            "the dead family's clocks wind without the cells, and its species are split first (a composed egg's keystone species, and any species whose admitted future has ended)",
        )
    );
}

/// The work each family reports: a key family's reads are its survivors before each cell, a tree's
/// deposits are its cells, a composed prime egg's maintenance is its sieve's window decided once.
#[test]
fn the_cost_receipt_reports_each_familys_work() {
    let cells = hand_moire(MoireClass::Parity).emit(20);
    let mut family = gratings(MoireClass::Parity, 0);
    let mut reads = 0u64;
    for &cell in &cells {
        reads += family.factors()[0].survivors().len() as u64;
        family.receive(cell).unwrap();
    }
    assert_eq!(family.work().of(Act::Read), reads);
    let mut population = Population::new(vec![
        Box::new(TreeFamily::new(tree(2, 3, 64), 1).unwrap()) as Box<dyn Family>,
        Box::new(gratings(MoireClass::Parity, 1)),
    ])
    .unwrap();
    population.receive_passage(&cells).unwrap();
    let receipt = population.receipt().unwrap();
    assert_eq!(receipt.families[0].work.of(Act::Deposit), 20);
    assert!(receipt.families[0].work.of(Act::Node) > 0);
    assert_eq!(receipt.families[1].work.of(Act::Read), reads);

    let window = PrimeWindow {
        base: 10,
        start: 0,
        end: 1000,
        digits: 3,
        trailing: 1,
        order: DigitOrder::MostFirst,
        emission: PrimeEmission::Digits,
    };
    let primes = Composed::primes(&window, 1 << 20, 1).unwrap();
    let decided: u64 = primes
        .work()
        .acts
        .iter()
        .filter(|(act, _)| matches!(act, Act::Decide(_)))
        .map(|(_, &count)| count)
        .sum();
    assert_eq!(decided, 1000);
    // The 168 primes below 1000 less the 11 up to 31, which their own faces decide.
    assert_eq!(primes.work().of(Act::Decide(SieveFace::Gap)), 157);
    assert_eq!(primes.work().of(Act::Decide(SieveFace::Unit)), 2);
}
