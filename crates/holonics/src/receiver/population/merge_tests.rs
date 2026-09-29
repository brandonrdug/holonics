//! Tests of the merge law, its price and description, and the hazard's learned partition (`merge`'s
//! module header).

use num_bigint::BigInt;
use num_traits::One;

use super::*;
use crate::compression::landmark::context::{
    Capacity, LandmarkDeclaration, PassageCode, SectionSlots, Sections, StopPrior, code_length,
    sections::Section,
};
use crate::receiver::population::boundary::{BoundaryEgg, Hazard, byte_index};
use crate::receiver::population::{Family, TreeFamily};

/// The exact KT mass of a count table over `classes` classes.
fn kt(counts: &[u64], classes: u64) -> Rat {
    let mut mass = Rat::one();
    let mut seen = 0u64;
    for &count in counts {
        for j in 0..count {
            mass *= Rat::new(BigInt::from(2 * j + 1), BigInt::from(2 * seen + classes));
            seen += 1;
        }
    }
    mass
}

/// The exact restaurant mass at `α = ½` of blocks of the given sizes.
fn restaurant(sizes: &[usize]) -> Rat {
    let items: usize = sizes.iter().sum();
    let mut mass = Rat::one();
    for &size in sizes {
        mass *= Rat::new(BigInt::from(factorial(size - 1)), BigInt::from(2));
    }
    for j in 0..items as u64 {
        mass /= Rat::new(BigInt::from(2 * j + 1), BigInt::from(2));
    }
    mass
}

fn contains(interval: &ExactInterval, value: &ExactInterval) -> bool {
    interval.lower <= value.upper && value.lower <= interval.upper
}

fn item(group: usize, lanes: &[[u64; 2]]) -> Item {
    Item {
        group,
        counts: lanes.iter().map(|lane| lane.to_vec()).collect(),
    }
}

#[test]
fn the_kt_mass_is_the_exchangeable_product_of_its_faces() {
    let mut tables = KtTables::new(2).expect("tables");
    for counts in [[0u64, 0], [3, 1], [1, 4], [7, 0]] {
        let (numerator, denominator) = tables.mass(&counts);
        let exact = code_length(&kt(&counts, 2)).expect("bits");
        let bounded = negated(&log_ratio(numerator, denominator).expect("bits"));
        assert!(contains(&exact, &bounded), "{counts:?}");
    }
    // Any order of the same arrivals has the same product: the counts are the whole likelihood.
    let order = [true, false, false, true, false];
    let (mut ones, mut zeros, mut product) = (0u64, 0u64, Rat::one());
    for letter in order {
        let (count, total) = if letter { (ones, ones + zeros) } else { (zeros, ones + zeros) };
        product *= Rat::new(BigInt::from(2 * count + 1), BigInt::from(2 * total + 2));
        if letter {
            ones += 1;
        } else {
            zeros += 1;
        }
    }
    assert_eq!(product, kt(&[3, 2], 2));
}

#[test]
fn the_restaurant_ratio_is_the_masses_ratio_and_never_below_two() {
    for (a, b, rest) in [(1usize, 1usize, vec![]), (3, 2, vec![1, 4]), (5, 1, vec![2])] {
        let mut before = vec![a, b];
        before.extend(&rest);
        let mut after = vec![a + b];
        after.extend(&rest);
        let ratio = restaurant(&after) / restaurant(&before);
        assert_eq!(
            ratio,
            Rat::from_integer(BigInt::from(restaurant_ratio(a, b))),
            "Lean restaurant_merge_ratio"
        );
        assert!(ratio >= Rat::from_integer(BigInt::from(2)));
    }
    // The seatings are a face at every step (restaurant_step_sum).
    let sizes = [3u64, 1, 2];
    let n: u64 = sizes.iter().sum();
    let total: Rat = sizes
        .iter()
        .map(|&m| Rat::new(BigInt::from(2 * m), BigInt::from(2 * n + 1)))
        .sum::<Rat>()
        + Rat::new(BigInt::from(1), BigInt::from(2 * n + 1));
    assert_eq!(total, Rat::one());
}

#[test]
fn the_price_is_the_code_length_pair_decided_exactly() {
    // Two cells of one rate: pooling costs little, and the description pays more than it.
    let mut blocks = Blocks::new(
        2,
        2,
        vec![
            item(0, &[[20, 2], [0, 0]]),
            item(0, &[[19, 2], [0, 0]]),
            item(0, &[[1, 30], [2, 3]]),
        ],
    )
    .expect("blocks");
    for (a, b) in [(0, 1), (0, 2), (1, 2)] {
        let price = blocks.price(a, b).expect("a price");
        let (x, y) = (blocks.counts(a).to_vec(), blocks.counts(b).to_vec());
        let mut ratio = Rat::from_integer(BigInt::from(price.description.clone()));
        for lane in 0..2 {
            let pooled: Vec<u64> = x[lane].iter().zip(&y[lane]).map(|(p, q)| p + q).collect();
            ratio *= kt(&pooled, 2) / (kt(&x[lane], 2) * kt(&y[lane], 2));
        }
        // merge_cost_mass_iff: accepted exactly when P·W < P′·W′, `R·E > 1`.
        assert_eq!(price.accepted, Some(ratio > Rat::one()), "{a}, {b}");
        let exact = negated(&code_length(&ratio).expect("bits"));
        assert!(contains(&exact, &price.gain));
    }
    assert_eq!(blocks.price(0, 1).expect("a price").accepted, Some(true));
    assert_eq!(blocks.price(0, 2).expect("a price").accepted, Some(false));
    assert!(blocks.price(0, 0).is_err(), "a block merges with another");
}

#[test]
fn a_merge_keeps_every_seed_and_splits_back_exactly() {
    let items = vec![
        item(0, &[[20, 2]]),
        item(0, &[[19, 2]]),
        item(1, &[[4, 0]]),
    ];
    let mut blocks = Blocks::new(2, 1, items.clone()).expect("blocks");
    let before = blocks.likelihood_bits().expect("bits");
    assert!(blocks.price(0, 2).is_err(), "merges stay within one group");
    let price = blocks.merge(0, 1).expect("a price");
    assert_eq!(price.accepted, Some(true));
    assert_eq!(blocks.blocks(), vec![vec![0, 1], vec![2]]);
    assert_eq!(blocks.counts(0), &[vec![39, 4]]);
    assert_eq!(blocks.split(0), vec![0, 1]);
    assert_eq!(blocks.blocks(), vec![vec![0], vec![1], vec![2]]);
    assert_eq!(blocks.counts(1), items[1].counts.as_slice());
    assert_eq!(blocks.likelihood_bits().expect("bits"), before);
}

#[test]
fn learning_merges_what_reads_alike_and_keeps_apart_what_differs() {
    // Three values that almost never precede a letter, two that often do, one lane each channel.
    let items = vec![
        item(0, &[[400, 1], [300, 0]]),
        item(0, &[[380, 0], [310, 1]]),
        item(0, &[[390, 1], [290, 1]]),
        item(0, &[[10, 30], [5, 20]]),
        item(0, &[[12, 28], [6, 19]]),
        item(0, &[[50, 50], [0, 0]]),
    ];
    let mut blocks = Blocks::new(2, 2, items).expect("blocks");
    let receipt = blocks.learn().expect("a receipt");
    assert_eq!(receipt.before, 6);
    let learned = blocks.blocks();
    assert!(learned.contains(&vec![0, 1, 2]), "{learned:?}");
    assert!(learned.contains(&vec![3, 4]), "{learned:?}");
    assert_eq!(receipt.after, learned.len());
    assert_eq!(receipt.undecided, 0);
    // Every accepted merge lowered the complete code, so the whole passage did.
    let before = add(&receipt.likelihood[0], &receipt.description[0]).expect("bits");
    let after = add(&receipt.likelihood[1], &receipt.description[1]).expect("bits");
    assert!(after.upper < before.lower);
    assert!(
        receipt
            .accepted
            .iter()
            .all(|(_, _, gain)| gain.lower > Rat::zero())
    );
}

#[test]
fn a_release_groups_the_cells_whose_faces_agree_and_moves_nothing() {
    // (0, 0) and (1, 1) read ½; (1, 0) reads ¾ for the byte; (3, 1) and (1, 0) do not agree.
    let blocks = Blocks::new(
        2,
        1,
        vec![
            item(0, &[[0, 0]]),
            item(0, &[[1, 0]]),
            item(0, &[[1, 1]]),
            item(0, &[[3, 1]]),
        ],
    )
    .expect("blocks");
    assert_eq!(blocks.species(), vec![vec![0, 2], vec![1], vec![3]]);
    assert_eq!(blocks.blocks().len(), 4);
}

fn chart() -> SectionChart {
    SectionChart::curated()
}

const POPULATION: u64 = 1 << 12;

fn typed_tree(depth: usize) -> TreeFamily {
    let sections = Sections::new(chart(), SectionSlots::Channel).expect("the channel slot");
    TreeFamily::sectioned(
        LandmarkDeclaration {
            alphabet: chart().alphabet(),
            depth,
            forced: 0,
            population: POPULATION,
            grain: 16,
            family: sections.family().clone(),
            prior: StopPrior::half(),
            capacity: Capacity::Unbounded,
        },
        1,
        sections,
    )
    .expect("a typed tree")
}

fn letter_declaration(depth: usize) -> LandmarkDeclaration {
    LandmarkDeclaration {
        alphabet: chart().letters(),
        depth,
        forced: 0,
        population: POPULATION,
        grain: 16,
        family: BoundaryEgg::letter_family(POPULATION).expect("the letter family"),
        prior: StopPrior::half(),
        capacity: Capacity::Unbounded,
    }
}

fn letter(kind: usize, channel: usize) -> usize {
    chart()
        .letter(Section { kind, channel })
        .expect("a section")
}

/// A passage whose agent parts often end after a closing quote and whose human parts end on a
/// letter's byte: the declared classes put both in `Other`.
fn quoted() -> Vec<usize> {
    let mut cells = Vec::new();
    for turn in 0..40 {
        cells.push(letter(2, 1));
        cells.extend(b"It said \"yes\" and then \"no\"".iter().map(|&b| usize::from(b)));
        if turn % 3 == 0 {
            cells.extend(b". Done.".iter().map(|&b| usize::from(b)));
        }
        cells.push(letter(2, 0));
        cells.extend(b"ok thanks".iter().map(|&b| usize::from(b)));
    }
    cells
}

#[test]
fn the_hazards_code_on_a_partition_is_its_cells_kt_code() {
    let cells = quoted();
    let (partition, receipt) = learn_hazard_partition(chart(), &cells).expect("a partition");
    for (candidate, code) in [
        (HazardPartition::declared(), &receipt.declared_code),
        (partition.clone(), &receipt.learned_code),
    ] {
        let mut clock = PartClock::new(chart());
        let mut hazard = Hazard::with_partition(candidate);
        let mut passage = PassageCode::new();
        for &cell in &cells {
            let port = clock.port();
            let letter = chart().section(cell).is_some();
            if port.section.is_some() {
                passage
                    .face(&hazard.face(&port)[usize::from(letter)])
                    .expect("a positive face");
            }
            hazard.deposit(&port, letter);
            clock.advance(cell);
        }
        let read = passage.bits().expect("bits");
        assert!(contains(code, &read), "the passage's code is the counts' KT code");
    }
}

#[test]
fn the_learned_partition_separates_a_closing_quote_and_splits_back_to_the_declared() {
    let cells = quoted();
    let (partition, receipt) = learn_hazard_partition(chart(), &cells).expect("a partition");
    assert!(receipt.classes_adopted, "{receipt:?}");
    let quote = partition.classes()[byte_index(Some(b'"'))];
    let other = partition.classes()[byte_index(Some(b'x'))];
    assert_ne!(quote, other, "the quote is a class of its own");
    assert!(receipt.values_met < BYTE_VALUES);
    assert!(receipt.classes.after < receipt.classes.before);
    let complete = add(&receipt.learned_code, &receipt.description).expect("bits");
    assert!(complete.upper < receipt.declared_code.lower);
    // The seeds are kept: the learned hazard reads back through the declared partition exactly.
    let mut learned = Hazard::with_partition(partition);
    let mut declared = Hazard::new();
    let mut clock = PartClock::new(chart());
    for &cell in &cells {
        let port = clock.port();
        let letter = chart().section(cell).is_some();
        learned.deposit(&port, letter);
        declared.deposit(&port, letter);
        clock.advance(cell);
    }
    assert_eq!(learned.cells(), receipt.learned_cells);
    learned.repartition(HazardPartition::declared());
    assert_eq!(learned.counts(), declared.counts());
}

#[test]
fn a_comparison_hazard_reads_the_same_cells_and_enters_no_face() {
    let cells = quoted();
    let (partition, _) = learn_hazard_partition(chart(), &cells).expect("a partition");
    let egg = |hazard: HazardPartition| {
        BoundaryEgg::new(
            "boundary egg".to_string(),
            1,
            typed_tree(3),
            chart(),
            letter_declaration(2),
        )
        .expect("an egg")
        .with_hazard(hazard)
        .expect("a hazard")
    };
    let mut learned = egg(partition.clone())
        .compared_with("declared".to_string(), HazardPartition::declared())
        .expect("a comparison");
    let mut declared = egg(HazardPartition::declared());
    for &cell in &cells {
        learned.receive(cell).expect("a cell");
        declared.receive(cell).expect("a cell");
    }
    let (with, without) = (learned.stages(), declared.stages());
    let comparison = &with.comparisons[0];
    assert_eq!(comparison.bytes, without.hazard_bytes);
    assert_eq!(comparison.closes, without.hazard_closes);
    assert_eq!(comparison.cells, without.hazard_cells);
    assert_eq!(with.within_bytes, without.within_bytes, "the conditioned faces are unchanged");
    assert_eq!(with.letters, without.letters);
    assert!(
        learned
            .compared_with("late".to_string(), HazardPartition::declared())
            .is_err(),
        "a comparison is declared before any cell"
    );
}
