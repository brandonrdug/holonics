//! Tests of the admitted receivers (`admitted`'s module header): the located continuation, the copy
//! stage's face and chain rule, the unheld port, the receipt that never enters the face, the
//! incidence's code and the spans' release.

use num_bigint::BigInt;
use num_traits::One;

use super::*;
use crate::compression::landmark::context::{
    Capacity, LandmarkDeclaration, SectionSlots, Sections, StopPrior, sections::Section,
};
use crate::ratio::algebraic::ExactInterval;
use crate::receiver::population::TreeFamily;
use crate::receiver::population::{Population, PopulationRelease};

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

fn inner() -> BoundaryEgg {
    let sections = Sections::new(chart(), SectionSlots::Channel).expect("the channel slot");
    let bytes = TreeFamily::sectioned(
        LandmarkDeclaration {
            alphabet: chart().alphabet(),
            depth: 3,
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
    BoundaryEgg::new(
        "boundary egg".to_string(),
        1,
        bytes,
        chart(),
        LandmarkDeclaration {
            alphabet: chart().letters(),
            depth: 2,
            forced: 0,
            population: POPULATION,
            grain: GRAIN,
            family: BoundaryEgg::letter_family(POPULATION).expect("the letter family"),
            prior: StopPrior::half(),
            capacity: Capacity::Unbounded,
        },
    )
    .expect("a boundary egg")
}

/// A request, two parts of its response (each quoting it), and a later human part quoting the
/// response: the cells and the four parts' letter ticks.
fn passage() -> (Vec<usize>, [u64; 4]) {
    let mut cells = Vec::new();
    let mut ticks = [0u64; 4];
    let parts: [(usize, usize, &[u8]); 4] = [
        (0, HUMAN, b"Please read the file alpha.txt now."),
        (
            2,
            AGENT,
            b"I read the file alpha.txt now, it holds two lines.",
        ),
        (3, AGENT, b"The file alpha.txt holds two lines."),
        (2, HUMAN, b"Good, alpha.txt holds two lines."),
    ];
    for (at, (kind, channel, text)) in parts.iter().enumerate() {
        ticks[at] = cells.len() as u64;
        cells.push(letter(*kind, *channel));
        cells.extend(text.iter().map(|&b| usize::from(b)));
    }
    (cells, ticks)
}

fn relations(ticks: [u64; 4]) -> Vec<Relation> {
    vec![
        Relation {
            letter: ticks[1],
            kind: RelationKind::Request,
            target: ticks[0],
        },
        Relation {
            letter: ticks[2],
            kind: RelationKind::Request,
            target: ticks[0],
        },
        Relation {
            letter: ticks[3],
            kind: RelationKind::LaterHuman,
            target: ticks[1],
        },
    ]
}

fn law() -> CopyLaw {
    CopyLaw::new(2, 3, 2).expect("a copy law")
}

fn egg(relations: Vec<Relation>) -> AdmittedEgg {
    AdmittedEgg::new(
        "admitted receivers".to_string(),
        1,
        inner(),
        chart(),
        relations,
        law(),
    )
    .expect("the admitted receivers")
    .with_receipt(RelationKind::LaterHuman, law())
}

fn readout(egg: &AdmittedEgg) -> AdmittedReadout {
    let Readout::Admitted(readout) = egg.readout() else {
        panic!("the admitted receivers' readout")
    };
    *readout
}

fn contains(enclosure: &ExactInterval, bits: i64) -> bool {
    let point = Rat::from_integer(BigInt::from(bits));
    enclosure.lower <= point && point <= enclosure.upper
}

#[test]
fn a_span_is_located_by_its_longest_suffix_and_kept_while_it_continues() {
    let span: Vec<usize> = b"abcab_abx".iter().map(|&b| usize::from(b)).collect();
    let mut reading = SpanReading::new();
    assert_eq!(reading.located(&span), None);
    // `a` recurs at 0, 3 and 6: the latest with a cell after it is 6, followed by `b`.
    reading.read(&span, usize::from(b'a'));
    assert_eq!(
        reading.located(&span),
        Some(Located {
            length: 1,
            next: usize::from(b'b')
        })
    );
    // `ab` continues at 6..8, followed by `x`.
    reading.read(&span, usize::from(b'b'));
    assert_eq!(
        reading.located(&span),
        Some(Located {
            length: 2,
            next: usize::from(b'x')
        })
    );
    // A break: `abc` is located anew at 0..3 (the only `abc`), followed by `a`.
    reading.read(&span, usize::from(b'c'));
    assert_eq!(
        reading.located(&span),
        Some(Located {
            length: 3,
            next: usize::from(b'a')
        })
    );
    // No cell of `z` recurs: nothing located.
    reading.read(&span, usize::from(b'z'));
    assert_eq!(reading.located(&span), None);
    assert_eq!(reading.cells(), 4);
}

#[test]
fn the_odds_class_is_exact() {
    let q = |n: i64, d: i64| Rat::new(BigInt::from(n), BigInt::from(d));
    assert_eq!(odds_class(&q(1, 2)), 0);
    assert_eq!(odds_class(&q(2, 3)), 1);
    assert_eq!(odds_class(&q(1, 3)), -1);
    assert_eq!(odds_class(&q(3, 4)), 1);
    assert_eq!(odds_class(&q(4, 5)), 2);
    assert_eq!(odds_class(&q(1, 5)), -2);
    assert_eq!(odds_class(&q(1, 6)), -3);
    assert_eq!(odds_class(&q(1023, 1024)), 9);
    let law = CopyLaw::new(4, 2, 1).expect("a law");
    assert_eq!(law.cell(3, &q(1, 2)), None);
    assert_eq!(
        law.cell(4, &q(1023, 1024)),
        Some(CopyCell { length: 0, odds: 0 })
    );
    assert_eq!(
        law.cell(64, &q(1, 6)),
        Some(CopyCell {
            length: 1,
            odds: -1
        })
    );
    assert!(CopyLaw::new(0, 1, 0).is_err());
    assert!(CopyLaw::new(1, 0, 0).is_err());
}

#[test]
fn the_boundary_eggs_one_class_face_is_its_face_entry() {
    let (cells, _) = passage();
    let mut egg = inner();
    for &cell in &cells {
        let face = egg.face().expect("a face");
        for class in (0..chart().alphabet()).step_by(7).chain([cell]) {
            assert_eq!(egg.probability(class).expect("a class"), face[class]);
        }
        egg.receive(cell).expect("a cell");
    }
}

#[test]
fn the_admitted_egg_is_a_face_and_its_code_is_the_chain_rule() {
    let (cells, ticks) = passage();
    let mut egg = egg(relations(ticks));
    egg.admits(&cells).expect("the passage");
    let mut product = Rat::one();
    for &cell in &cells {
        let face = egg.face().expect("a face");
        assert_eq!(face.iter().sum::<Rat>(), Rat::one(), "a face");
        let received = egg.receive(cell).expect("a cell");
        assert_eq!(
            received, face[cell],
            "the received face is the face's entry"
        );
        product *= received;
    }
    let Likelihood::Enclosed(code) = egg.likelihood() else {
        panic!("an enclosed likelihood")
    };
    let bits = code.bits().expect("an enclosure");
    let mut exact = PassageCode::new();
    exact.face(&product).expect("a positive product");
    let exact = exact.bits().expect("an enclosure");
    assert!(exact.lower <= bits.upper && bits.lower <= exact.upper);
    let readout = readout(&egg);
    let request = &readout.stages[0];
    assert_eq!(request.kind, RelationKind::Request);
    assert!(
        request.ticks[0] > 0 && request.copies > 0,
        "the response quotes its request"
    );
    // The chain rule: the staged code is the stage's code plus the conditioned code.
    let staged = {
        let mut all = request.staged[0];
        all.join(&request.staged[1]);
        all.bits().expect("an enclosure")
    };
    let mut parts = request.stage;
    parts.join(&request.conditioned);
    let parts = parts.bits().expect("an enclosure");
    assert!(staged.lower <= parts.upper && parts.lower <= staged.upper);
}

#[test]
fn unheld_the_admitted_egg_is_its_inner_egg() {
    let (cells, _) = passage();
    let mut admitted = egg(Vec::new());
    let mut alone = inner();
    for &cell in &cells {
        assert_eq!(
            admitted.face().expect("a face"),
            alone.face().expect("a face")
        );
        assert_eq!(
            admitted.receive(cell).expect("a cell"),
            alone.receive(cell).expect("a cell")
        );
    }
    let readout = readout(&admitted);
    assert!(readout.stages.iter().all(|stage| stage.ticks == [0, 0]));
    assert_eq!(readout.inner, *alone.stages());
}

#[test]
fn a_later_human_return_is_a_receipt_and_never_enters_the_face() {
    let (cells, ticks) = passage();
    let later: Vec<Relation> = relations(ticks)
        .into_iter()
        .filter(|relation| relation.kind == RelationKind::LaterHuman)
        .collect();
    let mut admitted = egg(later);
    let mut alone = inner();
    for &cell in &cells {
        assert_eq!(
            admitted.receive(cell).expect("a cell"),
            alone.receive(cell).expect("a cell"),
            "the family's face is the inner egg's"
        );
    }
    let readout = readout(&admitted);
    let receipt = &readout.stages[1];
    assert_eq!(receipt.kind, RelationKind::LaterHuman);
    assert!(
        receipt.ticks[0] > 0 && receipt.copies > 0,
        "the return quotes the response"
    );
    assert_eq!(readout.stages[0].ticks, [0, 0]);
}

#[test]
fn the_incidence_is_coded_where_it_arrives() {
    let (cells, ticks) = passage();
    let mut egg = egg(relations(ticks));
    for &cell in &cells {
        egg.receive(cell).expect("a cell");
    }
    let readout = readout(&egg);
    // The request's pointer at the two agent letters (a turn and a part): each held at the KT face
    // `½` of its context; the first's rank `0` of the only human part forced, the second the same
    // target as the first (`½`): `3` bits.
    let request = &readout.pointers[RelationKind::Request.index()];
    assert_eq!((request.parts, request.held), (2, 2));
    assert!(contains(&request.code.bits().expect("an enclosure"), 3));
    // The later human's pointer: none at the opening human letter (`½`), then held (`½`) at rank 1
    // of two agent parts, its class `1` above the forced level (`½`), one offset: `3` bits.
    let later = &readout.pointers[RelationKind::LaterHuman.index()];
    assert_eq!((later.parts, later.held), (2, 1));
    assert!(contains(&later.code.bits().expect("an enclosure"), 3));
}

#[test]
fn a_span_is_held_while_a_relation_reaches_it() {
    let (cells, ticks) = passage();
    let mut egg = egg(relations(ticks));
    // Through the second agent part: the request's span and the first response's are held.
    for &cell in &cells[..ticks[3] as usize] {
        egg.receive(cell).expect("a cell");
    }
    let before = readout(&egg);
    assert_eq!(before.retained, 2);
    // The later human part opens: the request's last reader closed, so only the response is held.
    egg.receive(cells[ticks[3] as usize]).expect("a letter");
    let after = readout(&egg);
    assert_eq!(after.retained, 1);
    assert!(after.widest_cells > after.retained_cells);
}

#[test]
fn the_incidence_is_refused_out_of_order_or_off_its_ports() {
    let (cells, ticks) = passage();
    let build = |relations| {
        AdmittedEgg::new(
            "admitted receivers".to_string(),
            1,
            inner(),
            chart(),
            relations,
            law(),
        )
    };
    let mut reversed = relations(ticks);
    reversed.reverse();
    assert!(build(reversed).is_err());
    assert!(
        build(vec![Relation {
            letter: ticks[1],
            kind: RelationKind::Request,
            target: ticks[1],
        }])
        .is_err()
    );
    // A request read on a human part, and a target that is a byte: refused before anything moves.
    for relation in [
        Relation {
            letter: ticks[3],
            kind: RelationKind::Request,
            target: ticks[0],
        },
        Relation {
            letter: ticks[1],
            kind: RelationKind::Request,
            target: ticks[0] + 1,
        },
    ] {
        let egg = build(vec![relation]).expect("in order");
        assert!(egg.admits(&cells).is_err());
        assert!(egg.likelihood() == Likelihood::Enclosed(PassageCode::new()));
    }
}

#[test]
fn a_planned_request_conditions_the_response_face_before_the_request_span_is_read() {
    let (cells, ticks) = passage();
    let make = || {
        AdmittedEgg::new(
            "planned admitted receivers".to_string(),
            1,
            inner(),
            chart(),
            Vec::new(),
            law(),
        )
        .expect("an admitted egg")
    };
    let relation = Relation {
        letter: ticks[1],
        kind: RelationKind::Request,
        target: ticks[0],
    };
    let mut conditioned = Population::new(vec![Box::new(make())]).expect("population");
    conditioned
        .plan_relation(relation)
        .expect("plan before the request arrives");
    let mut unconditioned = Population::new(vec![Box::new(make())]).expect("population");

    // Read the request and its bytes, then the response's opening section. Its following byte is
    // now scored against the retained request span only in the planned receiver.
    // Read through the first response while its request span is retained; its locator can then
    // condition the next scored cell.
    for &cell in &cells[..ticks[2] as usize] {
        conditioned.receive(cell).expect("conditioned reception");
        unconditioned
            .receive(cell)
            .expect("unconditioned reception");
    }
    let scored = conditioned.face().expect("conditioned score");
    let bare = unconditioned.face().expect("unconditioned score");
    assert_ne!(
        scored, bare,
        "the request relation changes the response face"
    );

    let released = PopulationRelease::from_scored_face(&conditioned, chart().alphabet() - 1)
        .expect("release the current scored face");
    assert_eq!(released.face(), scored.as_slice());
    assert_eq!(released.stopping_class(), chart().alphabet() - 1);
}

#[test]
fn planning_refuses_passed_targets_and_duplicate_reading_parts() {
    let (cells, ticks) = passage();
    let make = || {
        AdmittedEgg::new(
            "planned admitted receivers".to_string(),
            1,
            inner(),
            chart(),
            Vec::new(),
            law(),
        )
        .expect("an admitted egg")
    };
    let relation = Relation {
        letter: ticks[1],
        kind: RelationKind::Request,
        target: ticks[0],
    };
    let mut population = Population::new(vec![Box::new(make())]).expect("population");
    population
        .plan_relation(relation)
        .expect("the request target is still ahead");
    assert!(
        population.plan_relation(relation).is_err(),
        "one relation per part"
    );

    let mut late = Population::new(vec![Box::new(make())]).expect("population");
    late.receive(cells[0]).expect("receive the target section");
    assert!(
        late.plan_relation(relation).is_err(),
        "the target has passed"
    );
}
