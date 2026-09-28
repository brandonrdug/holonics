//! Tests of the part clock, the hazard law and the boundary egg (`boundary`'s module header).

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::*;
use crate::compression::landmark::context::{
    Capacity, SectionSlots, Sections, StopPrior, sections::Section,
};
use crate::receiver::population::Population;

const POPULATION: u64 = 1 << 10;
const GRAIN: u64 = 16;

fn chart() -> SectionChart {
    SectionChart::curated()
}

fn letter(kind: usize, channel: usize) -> usize {
    chart()
        .letter(Section { kind, channel })
        .expect("a section")
}

/// A short curated passage: an opening human part, an agent turn of two sentences, a further agent
/// part, and a human turn closing on a line.
fn passage() -> Vec<usize> {
    let mut cells = vec![letter(0, 0)];
    cells.extend(b"Hi. Can you read it?".iter().map(|&b| usize::from(b)));
    cells.push(letter(2, 1));
    cells.extend(b"Yes. I read it.".iter().map(|&b| usize::from(b)));
    cells.push(letter(3, 1));
    cells.extend(b"Done.".iter().map(|&b| usize::from(b)));
    cells.push(letter(2, 0));
    cells.extend(b"Thanks.\n".iter().map(|&b| usize::from(b)));
    cells.push(letter(2, 1));
    cells.extend(b"Ok.".iter().map(|&b| usize::from(b)));
    cells
}

fn typed_tree(depth: usize) -> TreeFamily {
    let sections = Sections::new(chart(), SectionSlots::Channel).expect("the channel slot");
    TreeFamily::sectioned(
        LandmarkDeclaration {
            alphabet: chart().alphabet(),
            depth,
            forced: 0,
            population: POPULATION,
            grain: GRAIN,
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
        grain: GRAIN,
        family: BoundaryEgg::letter_family(POPULATION).expect("the letter family"),
        prior: StopPrior::half(),
        capacity: Capacity::Unbounded,
    }
}

fn egg() -> BoundaryEgg {
    BoundaryEgg::new(
        "boundary egg".to_string(),
        1,
        typed_tree(3),
        chart(),
        letter_declaration(2),
    )
    .expect("a boundary egg")
}

#[test]
fn the_section_chart_reads_a_letter_once_and_carries_its_channel() {
    let chart = chart();
    assert_eq!(chart.alphabet(), 268);
    assert_eq!(chart.section(255), None);
    assert_eq!(
        chart.section(256 + 3 * 2 + 1),
        Some(Section {
            kind: 2,
            channel: 1
        })
    );
    assert_eq!(chart.section(268), None);
    let mut sections = Sections::new(chart, SectionSlots::Channel).expect("the channel slot");
    // A byte before any section is refused, and nothing moves.
    assert!(sections.read(usize::from(b'a')).is_err());
    assert_eq!(sections.open(), None);
    let family = sections.family().clone();
    let opened = sections.read(letter(2, 1)).expect("a letter");
    assert_eq!(
        opened,
        Letter::Bundle(Bundle {
            cell: letter(2, 1),
            features: family.encode(&[1]).expect("a channel")
        })
    );
    let byte = sections
        .read(usize::from(b'a'))
        .expect("a byte of the agent's part");
    assert_eq!(
        byte,
        Letter::Bundle(Bundle {
            cell: usize::from(b'a'),
            features: family.encode(&[1]).expect("a channel")
        })
    );
    // A letter carries its own channel, not the part it closes.
    let human = sections.read(letter(3, 0)).expect("a letter");
    assert_eq!(
        human,
        Letter::Bundle(Bundle {
            cell: letter(3, 0),
            features: family.encode(&[0]).expect("a channel")
        })
    );
    assert!(sections.read(268).is_err());
}

#[test]
fn a_typed_tree_refuses_a_foreign_family_and_a_passage_opening_on_a_byte() {
    let sections = Sections::new(chart(), SectionSlots::ChannelKind).expect("two slots");
    let mismatched = TreeFamily::sectioned(
        LandmarkDeclaration {
            alphabet: chart().alphabet(),
            depth: 2,
            forced: 0,
            population: POPULATION,
            grain: GRAIN,
            family: LetterFamily::new(vec![3]).expect("one slot"),
            prior: StopPrior::half(),
            capacity: Capacity::Unbounded,
        },
        1,
        sections,
    );
    assert!(mismatched.is_err());
    let tree = typed_tree(2);
    assert!(tree.admits(&[usize::from(b'a')]).is_err());
    assert!(tree.admits(&passage()).is_ok());
}

#[test]
fn the_part_clock_winds_by_bytes_and_carries_at_a_sentence_close() {
    let mut clock = PartClock::new(chart());
    assert_eq!(clock.port().section, None);
    clock.advance(letter(2, 1));
    for &byte in b"Yes. I read it." {
        clock.advance(usize::from(byte));
    }
    let port = clock.port();
    assert_eq!(
        port.section,
        Some(Section {
            kind: 2,
            channel: 1
        })
    );
    assert_eq!(
        (port.phase, port.carry, port.last),
        (15, 2, LastByte::SentenceClose)
    );
    assert_eq!(
        HazardCell::of(port.section.expect("open"), &port),
        HazardCell::Sentence {
            channel: 1,
            kind: 2,
            phase: 4,
            carry: 2
        }
    );
    clock.advance(letter(3, 1));
    assert_eq!((clock.port().phase, clock.port().last), (0, LastByte::None));
    assert_eq!(
        [0, 1, 2, 3, 4, 7, 8].map(dyadic_class),
        [0, 1, 2, 2, 3, 3, 4]
    );
}

#[test]
fn the_hazard_is_a_kt_face_per_partition_cell_and_the_pin_before_any_section() {
    let mut hazard = Hazard::new();
    let pinned = PartClock::new(chart()).port();
    assert_eq!(hazard.face(&pinned), [Rat::zero(), Rat::one()]);
    let mut clock = PartClock::new(chart());
    clock.advance(letter(0, 0));
    clock.advance(usize::from(b'.'));
    let port = clock.port();
    let half = Rat::new(BigInt::from(1), BigInt::from(2));
    assert_eq!(hazard.face(&port), [half.clone(), half]);
    hazard.deposit(&port, true);
    hazard.deposit(&port, false);
    hazard.deposit(&port, true);
    // (2·2 + 1)/(2·3 + 2) = 5/8 for the letter, 3/8 for the byte.
    assert_eq!(
        hazard.face(&port),
        [
            Rat::new(BigInt::from(3), BigInt::from(8)),
            Rat::new(BigInt::from(5), BigInt::from(8))
        ]
    );
    hazard.deposit(&pinned, true);
    assert_eq!(hazard.cells(), 1);
}

#[test]
fn the_staged_face_is_a_face_and_its_product_is_the_hazards_times_the_conditioned() {
    let mut egg = egg();
    let (mut product, mut staged) = (Rat::one(), Rat::one());
    for &cell in &passage() {
        let face = egg.face().expect("a face");
        assert_eq!(face.len(), 268);
        assert!(face.iter().all(|class| *class >= Rat::zero()));
        assert_eq!(face.iter().sum::<Rat>(), Rat::one(), "a face at every cell");
        let port = egg.clock.port();
        let letter = egg.chart.section(cell).is_some();
        let stage = egg.hazard.face(&port)[usize::from(letter)].clone();
        let received = egg.receive(cell).expect("a cell of the chart");
        assert_eq!(
            received, face[cell],
            "the received face is the face read before it"
        );
        assert!(received > Rat::zero());
        product *= &received;
        staged *= &stage;
        // q = h(σ(x)) r(x): the conditioned face is the received face over the hazard's.
        assert_eq!(&received / &stage * &stage, received);
    }
    // The staged chain rule: the product of the received faces is the hazard's product times the
    // conditioned faces' product (the receipts' stages multiply to the egg's likelihood).
    let stages = egg.stages();
    let mut hazard = PassageCode::new();
    let mut conditioned = PassageCode::new();
    for channel in 0..chart().channels() {
        hazard.join(&stages.hazard_bytes[channel]);
        hazard.join(&stages.hazard_closes[channel]);
        conditioned.join(&stages.within_bytes[channel]);
    }
    conditioned.join(&stages.letters);
    let mut joined = hazard;
    joined.join(&conditioned);
    let Likelihood::Enclosed(likelihood) = egg.likelihood() else {
        panic!("an enclosed likelihood")
    };
    let (whole, parts) = (
        likelihood.bits().expect("bits"),
        joined.bits().expect("bits"),
    );
    assert!(whole.lower <= parts.upper && parts.lower <= whole.upper);
    // The hazard's receipts are exactly its faces' product.
    let exact = crate::compression::landmark::context::code_length(&staged).expect("bits");
    let read = hazard.bits().expect("bits");
    assert!(exact.lower <= read.upper && read.lower <= exact.upper);
    let exact = crate::compression::landmark::context::code_length(&product).expect("bits");
    assert!(exact.lower <= whole.upper && whole.lower <= exact.upper);
    assert_eq!(
        stages.closes,
        vec![2, 2, 0],
        "each close on the channel of the part it closes"
    );
    assert_eq!(
        stages.bytes.iter().sum::<u64>() as usize + 5,
        passage().len(),
        "every byte on its channel beside the five letters"
    );
}

#[test]
fn the_unheld_port_is_the_byte_tree_alone() {
    let mut egg = egg();
    let mut alone = typed_tree(3);
    for &cell in &passage() {
        egg.receive(cell).expect("a cell");
        alone.receive(cell).expect("a cell");
    }
    let stages = egg.stages();
    let mut unheld = PassageCode::new();
    for channel in 0..chart().channels() {
        unheld.join(&stages.root_bytes[channel]);
        unheld.join(&stages.root_closes[channel]);
        unheld.join(&stages.within_bytes[channel]);
    }
    unheld.join(&stages.tree_letters);
    let (Likelihood::Enclosed(inside), Likelihood::Enclosed(outside)) =
        (egg.byte_tree().likelihood(), alone.likelihood())
    else {
        panic!("enclosed likelihoods")
    };
    assert_eq!(
        inside.bits(),
        outside.bits(),
        "the egg's byte tree is the tree alone"
    );
    let (whole, parts) = (outside.bits().expect("bits"), unheld.bits().expect("bits"));
    assert!(whole.lower <= parts.upper && parts.lower <= whole.upper);
}

#[test]
fn the_egg_refuses_a_chart_whose_bytes_do_not_fill_the_lower_half() {
    let small = SectionChart::new(6, 2, 2).expect("a chart of ten cells");
    let sections = Sections::new(small, SectionSlots::Channel).expect("the channel slot");
    let tree = TreeFamily::sectioned(
        LandmarkDeclaration {
            alphabet: small.alphabet(),
            depth: 2,
            forced: 0,
            population: POPULATION,
            grain: GRAIN,
            family: sections.family().clone(),
            prior: StopPrior::half(),
            capacity: Capacity::Unbounded,
        },
        1,
        sections,
    )
    .expect("a typed tree");
    let letters = LandmarkDeclaration {
        alphabet: small.letters(),
        ..letter_declaration(2)
    };
    assert!(BoundaryEgg::new("refused".to_string(), 1, tree, small, letters).is_err());
}

#[test]
fn a_population_selects_the_boundary_egg_over_its_tree_alone_on_sectioned_prose() {
    // The same passage repeated: the part clock learns where each part ends.
    let cells: Vec<usize> = (0..6).flat_map(|_| passage()).collect();
    let mut population = Population::new(vec![
        Box::new(typed_tree(3)) as Box<dyn Family>,
        Box::new(egg()),
    ])
    .expect("a population");
    population.receive_passage(&cells).expect("the passage");
    let receipt = population.receipt().expect("a receipt");
    assert!(receipt.families.iter().all(|family| family.died.is_none()));
    let Some(Readout::Boundary(stages)) = population.readout(1) else {
        panic!("the boundary egg's readout")
    };
    assert_eq!(stages.closes.iter().sum::<u64>(), 29);
    let (tree, egg) = (
        receipt.families[0].code.clone().expect("a code"),
        receipt.families[1].code.clone().expect("a code"),
    );
    assert!(
        egg.upper < tree.lower,
        "the part clock pays on sectioned prose"
    );
}
