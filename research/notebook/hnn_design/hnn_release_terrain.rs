//! **Population release checks on known-truth terrain** (#73, #148). A moiré's candidate one-hot
//! face is checked across a full joint period before it can count as a future-equivalent key. An
//! arithmetic product composition is checked through its record stop. The stochastic receiver's
//! learned tree face is compared with the identified source face; mismatches are exact separators.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_release_terrain
//! ```

use holonics::compression::landmark::context::{
    Capacity, LandmarkDeclaration, LetterFamily, StopPrior,
};
use holonics::holarchy::terrain::arithmetic::{DigitOrder, ProductCell, ProductFamily, Products};
use holonics::holarchy::terrain::{
    Draw, Moire, MoireClass, MoireFamily, MoireTruth, TreeSource, TreeSourceFamily,
};
use holonics::ratio::Rat;
use holonics::receiver::population::{Composed, Family, KeyFamily, Population, TreeFamily};
use num_traits::{One, Zero};

const SEED: u64 = 20_260_927;
const OBSERVED_TICKS: usize = 1 << 12;
const STOCHASTIC_TICKS: usize = 1 << 10;
const ADMITTED_KEYS: u64 = 1 << 20;

/// The one-member mixture's exact conditional face, checked against its public enclosure.
fn exact_population_face(population: &Population) -> Vec<Rat> {
    let exact = population
        .families()
        .next()
        .expect("the declared one-family population")
        .face()
        .expect("the member's exact conditional face");
    let enclosure = population.face().expect("population conditional enclosure");
    assert_eq!(exact.len(), enclosure.len());
    assert!(exact.iter().zip(&enclosure).all(|(probability, bounds)| {
        bounds.lower <= *probability && *probability <= bounds.upper
    }));
    exact
}

fn truth_cell(truth: &MoireTruth, tick: u64, class: MoireClass) -> usize {
    let sheets: Vec<bool> = truth
        .gratings
        .iter()
        .map(|grating| {
            let port = (grating.phase() + (tick * grating.numerator()) % grating.denominator())
                % grating.denominator();
            2 * port >= grating.denominator()
        })
        .collect();
    match class {
        MoireClass::Parity => sheets.iter().filter(|sheet| **sheet).count() % 2,
        MoireClass::Sheets => sheets
            .iter()
            .enumerate()
            .map(|(ring, sheet)| usize::from(*sheet) << ring)
            .sum(),
    }
}

fn deterministic_moire() {
    // Small declared key space permits exact survivor filtering. The truth is independently read
    // from the terrain's returned rate/phase keys, while the receiver advances through cells.
    let family = MoireFamily {
        rings: 2,
        denominator: 5,
    };
    let class = MoireClass::Sheets;
    let moire = Moire::draw(&family, class, &mut Draw::new(SEED)).expect("declared moiré family");
    let truth = moire.truth(&family).expect("exact moiré truth");
    let description = u64::from(family.gratings()).ilog2() as u64 * family.rings as u64 + 1;
    let keys = KeyFamily::gratings(&family, class, ADMITTED_KEYS, description)
        .expect("admitted exact grating-key family");
    let mut population =
        Population::new(vec![Box::new(keys) as Box<dyn Family>]).expect("one-family population");

    let cells = moire.emit(OBSERVED_TICKS + 1);
    assert!(
        cells
            .iter()
            .enumerate()
            .all(|(tick, cell)| *cell == truth_cell(&truth, tick as u64, class))
    );
    let mut candidate_at = None;
    let mut last_face = Vec::new();
    let mut last_truth = 0usize;
    for (tick, &cell) in cells[..OBSERVED_TICKS].iter().enumerate() {
        population
            .receive(cell)
            .expect("receive known terrain cell");
        let next_truth = truth_cell(&truth, tick as u64 + 1, class);
        let face = exact_population_face(&population);
        last_face = face.clone();
        last_truth = next_truth;
        let is_exact_continuation = face.len() == moire.alphabet()
            && face.iter().enumerate().all(|(class, probability)| {
                if class == next_truth {
                    probability.is_one()
                } else {
                    probability.is_zero()
                }
            });
        if is_exact_continuation {
            assert_eq!(cells[tick + 1], next_truth);
            candidate_at = Some(tick + 1);
            break;
        }
    }
    if candidate_at.is_none() {
        println!(
            "deterministic moire: typed refusal — no exact one-hot next-cell face located within {OBSERVED_TICKS} received cells; at the horizon, truth class {last_truth} and receiver face {last_face:?}"
        );
        return;
    }
    let start = candidate_at.expect("checked above");
    let period = usize::try_from(truth.joint_period.clone())
        .expect("the declared joint period fits this terrain passage");
    let mut separator = None;
    for offset in 0..period {
        let tick = start + offset;
        let expected = truth_cell(&truth, tick as u64, class);
        let face = exact_population_face(&population);
        let exact = face.len() == moire.alphabet()
            && face.iter().enumerate().all(|(class, probability)| {
                if class == expected {
                    probability.is_one()
                } else {
                    probability.is_zero()
                }
            });
        if !exact && separator.is_none() {
            separator = Some((tick, expected, face));
        }
        population
            .receive(expected)
            .expect("receive the truth continuation cell");
    }
    match separator {
        Some((tick, expected, face)) => println!(
            "deterministic moire: typed refusal — candidate at tick {start} failed within the checked joint period {period}; first separating tick {tick}, truth class {expected}, exact population face {face:?}"
        ),
        None => println!(
            "deterministic moire: future-equivalent grating keys verified across joint period {period}, beginning at tick {start}; every exact conditional population face matched terrain truth"
        ),
    }
}

fn deterministic_arithmetic() {
    let family = ProductFamily {
        base: 2,
        digits: 1,
        face: 1,
        order: DigitOrder::LeastFirst,
    };
    let products = Products::new(family.clone(), vec![(1, 1)]).expect("known product terrain");
    let stream = products.emit();
    let truth = products.truth().expect("exact product truth");
    assert_eq!(truth[0].value, 1);
    assert_eq!(stream.len(), family.record_length());
    let composed = Composed::products(&family, 1).expect("record clock joined to carry egg");
    let mut population = Population::new(vec![Box::new(composed) as Box<dyn Family>])
        .expect("one-family arithmetic population");

    let mut located_at = None;
    for (position, &cell) in stream.iter().enumerate() {
        let class = family.class(position);
        if class != ProductCell::Operand {
            let face = exact_population_face(&population);
            let exact = face.len() == family.alphabet()
                && face.iter().enumerate().all(|(candidate, probability)| {
                    if candidate == cell {
                        probability.is_one()
                    } else {
                        probability.is_zero()
                    }
                });
            if located_at.is_none() && exact {
                located_at = Some(position);
            } else if let Some(start) = located_at
                && !exact
            {
                println!(
                    "deterministic arithmetic products: typed refusal — composed key failed at cell {position} after first exact face at {start}; known class {cell}, receiver face {face:?}"
                );
                return;
            }
        }
        population
            .receive(cell)
            .expect("receive product terrain cell");
    }
    match located_at {
        Some(start) => println!(
            "deterministic arithmetic products: composed record-clock/carry key first predicts a determined face at cell {start}; all later determined faces through the record stop match exact product truth"
        ),
        None => println!(
            "deterministic arithmetic products: typed refusal — no exact composed key face located through the record stop"
        ),
    }
}

fn stochastic_population_face() {
    let family = TreeSourceFamily {
        alphabet: 2,
        depth: 3,
        grid: 16,
    };
    let source = TreeSource::draw(&family, &mut Draw::new(SEED)).expect("tree source");
    let truth = source.truth().expect("exact tree-source truth");
    let cells = source.emit(STOCHASTIC_TICKS, &mut Draw::new(SEED ^ 0xF4));
    let declaration = LandmarkDeclaration {
        alphabet: 2,
        depth: family.depth,
        forced: 0,
        population: (STOCHASTIC_TICKS + family.depth) as u64,
        grain: 16,
        family: LetterFamily::cells(),
        prior: StopPrior::half(),
        capacity: Capacity::Unbounded,
    };
    let tree = TreeFamily::new(declaration, 1).expect("declared receiving tree");
    let mut population = Population::new(vec![Box::new(tree) as Box<dyn Family>])
        .expect("one-tree receiving population");
    // Put the receiving navigator at the known initial source boundary before comparing faces.
    population
        .receive_passage(source.initial())
        .expect("receive initial source address");

    let mut history: Vec<usize> = source.initial().iter().rev().copied().collect();
    let mut equal_faces = 0usize;
    let mut first_separator = None;
    for (tick, cell) in cells.into_iter().enumerate() {
        let leaf = source
            .tree()
            .leaf(history.iter().rev().copied())
            .expect("known source address reaches a leaf");
        let source_face = &truth.faces[leaf];
        let receiver_face = exact_population_face(&population);
        if receiver_face.len() == source_face.len()
            && receiver_face
                .iter()
                .zip(source_face)
                .all(|(got, expected)| got == expected)
        {
            equal_faces += 1;
        } else if first_separator.is_none() {
            let differences = receiver_face
                .iter()
                .zip(source_face)
                .map(|(got, expected)| got - expected)
                .collect::<Vec<_>>();
            first_separator = Some((tick, differences));
        }
        population
            .receive(cell)
            .expect("receive stochastic source cell");
        history.push(cell);
    }
    match first_separator {
        Some((tick, difference)) => println!(
            "stochastic source: {equal_faces}/{STOCHASTIC_TICKS} receiving faces equal the identified conditional truth face; first separator at tick {tick}: {difference:?}"
        ),
        None => println!(
            "stochastic source: all {STOCHASTIC_TICKS} receiving faces equal the identified conditional truth face"
        ),
    }
}

fn main() {
    deterministic_moire();
    deterministic_arithmetic();
    stochastic_population_face();
}
