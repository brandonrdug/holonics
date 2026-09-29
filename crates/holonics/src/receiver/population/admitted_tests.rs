//! Tests of the admitted receivers (`admitted`'s module header): the located continuation, the copy
//! stage's face and chain rule, the unheld port, the receipt that never enters the face, the
//! incidence's code, retention by the present law, the aeon, and the invariance of the request's
//! time under any withheld continuation.

use num_bigint::BigInt;
use num_traits::One;

use super::*;
use crate::compression::landmark::context::{
    Capacity, LandmarkDeclaration, SectionSlots, Sections, StopPrior, sections::Section,
};
use crate::ratio::algebraic::ExactInterval;
use crate::receiver::population::TreeFamily;
use crate::receiver::population::{Population, PopulationRelease, ResponseLaw};

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
fn a_run_is_held_until_its_aeon_turns_to_its_port_again() {
    let (cells, ticks) = passage();
    let mut egg = egg(relations(ticks));
    // Through the second agent part: the request's run (one human part) and the response's run
    // (two agent parts) are held.
    for &cell in &cells[..ticks[3] as usize] {
        egg.receive(cell).expect("a cell");
    }
    let before = readout(&egg);
    assert_eq!(before.retained, 3);
    let request = (ticks[1] - ticks[0] - 1) as usize;
    // The later human part opens a new human run: the request's is released, the response's
    // stays for the return that reads it, and the return's own part joins the human port.
    egg.receive(cells[ticks[3] as usize]).expect("a letter");
    let after = readout(&egg);
    assert_eq!(after.retained, 3);
    assert_eq!(after.retained_cells, before.retained_cells - request);
    assert!(after.widest_cells > after.retained_cells);
    assert_eq!(after.released, vec![0, 0], "every relation was held");
}

#[test]
fn a_relation_to_a_released_run_is_unheld_and_counted() {
    let (mut cells, ticks) = passage();
    // A further agent part after the human return, declared to read the first request: the
    // conversation turned to the human port since, so retention released that run.
    let late = cells.len() as u64;
    cells.push(letter(2, AGENT));
    cells.extend(b"alpha.txt holds".iter().map(|&b| usize::from(b)));
    let mut declared = relations(ticks);
    declared.push(Relation {
        letter: late,
        kind: RelationKind::Request,
        target: ticks[0],
    });
    let mut admitted = egg(declared);
    let mut unheld = egg(relations(ticks));
    admitted
        .admits(&cells)
        .expect("an earlier target retention released is admitted");
    for &cell in &cells {
        assert_eq!(
            admitted.face().expect("a face"),
            unheld.face().expect("a face")
        );
        admitted.receive(cell).expect("a cell");
        unheld.receive(cell).expect("a cell");
    }
    assert_eq!(readout(&admitted).released, vec![1, 0]);
    let pointer = &readout(&admitted).pointers[RelationKind::Request.index()];
    assert_eq!((pointer.parts, pointer.held), (3, 2));
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
    assert_eq!(released.selected_class(), chart().alphabet() - 1);
}

#[test]
fn request_face_provenance_tracks_the_open_relation_and_survives_branching() {
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
        .expect("plan before the target arrives");

    // Receive the request section and its bytes, then open the response section.
    for &cell in &cells[..ticks[1] as usize + 1] {
        population.receive(cell).expect("receive request");
    }
    let Readout::Admitted(opening) = population.readout(0).expect("family readout") else {
        panic!("admitted readout")
    };
    let opening = opening.request_provenance.as_ref().expect("held request");
    assert_eq!(opening.response_letter_tick, ticks[1]);
    assert_eq!(opening.request_target_tick, ticks[0]);
    assert_eq!(
        opening.target_span_cells,
        (ticks[1] - ticks[0] - 1) as usize
    );
    assert_eq!(opening.located_length, None);
    assert_eq!(opening.next_byte, None);
    assert_eq!(opening.copy_law, law());
    assert_eq!(opening.copy_cell, None);

    // The response's `read ` matches a suffix of the request with a following target byte.
    let read_space = b"I read ";
    for &byte in &read_space[1..] {
        population
            .receive(usize::from(byte))
            .expect("receive response byte");
    }
    let Readout::Admitted(matched) = population.readout(0).expect("family readout") else {
        panic!("admitted readout")
    };
    let matched = matched.request_provenance.as_ref().expect("held request");
    assert_eq!(matched.response_letter_tick, ticks[1]);
    assert_eq!(matched.request_target_tick, ticks[0]);
    assert!(matched.located_length.is_some());
    assert_eq!(matched.next_byte, Some(usize::from(b't')));
    assert!(matched.copy_cell.is_some());

    let branch = population.branch_future().expect("branch future");
    assert_eq!(branch.readout(0), population.readout(0));
}

#[test]
fn request_face_provenance_is_absent_without_a_held_request_relation() {
    let (cells, ticks) = passage();
    let make = || {
        AdmittedEgg::new(
            "unheld admitted receivers".to_string(),
            1,
            inner(),
            chart(),
            Vec::new(),
            law(),
        )
        .expect("an admitted egg")
    };
    let mut population = Population::new(vec![Box::new(make())]).expect("population");
    for &cell in &cells[..ticks[1] as usize + 1] {
        population.receive(cell).expect("receive unheld request");
    }
    let Readout::Admitted(readout) = population.readout(0).expect("family readout") else {
        panic!("admitted readout")
    };
    assert_eq!(readout.request_provenance, None);
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

#[test]
fn a_branch_at_the_present_withholds_the_future_incidence_and_moves_no_face() {
    let (cells, ticks) = passage();
    let mut egg = egg(relations(ticks));
    let opening = ticks[1] as usize;
    for &cell in &cells[..=opening] {
        egg.receive(cell)
            .expect("the request and the response's opening");
    }
    let mut present = egg.branch_at_present();
    let mut full = egg.clone();
    // The response's first part: the same face at every cell.
    for &cell in &cells[opening + 1..ticks[2] as usize] {
        assert_eq!(present.face(), full.face());
        assert_eq!(present.receive(cell), full.receive(cell));
    }
    assert_eq!(present.face(), full.face());
    // At the second part's declared letter, a drawn byte: the full incidence refuses it, the
    // present admits it.
    let byte = usize::from(b'x');
    let mut carried = Population::new(vec![Box::new(full)]).expect("the full incidence");
    assert!(carried.receive(byte).is_err(), "a declared future letter");
    let mut released = Population::new(vec![Box::new(present)]).expect("the present incidence");
    assert!(released.receive(byte).is_ok(), "no future incidence");
}

/// A part's cells: its letter and its bytes.
fn part(kind: usize, channel: usize, text: &[u8]) -> Vec<usize> {
    std::iter::once(letter(kind, channel))
        .chain(text.iter().map(|&b| usize::from(b)))
        .collect()
}

/// An exact key stream of `[0, 1)` (a declared congruence, the test's own keys).
fn keys(seed: u64) -> impl FnMut() -> Rat {
    let mut state = seed;
    move || {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        Rat::new(BigInt::from(state), BigInt::one() << 64)
    }
}

/// [THE_REBUILD U6, the audit's §4 item 1 and finding 7: the invariance test] **A withheld
/// continuation moves nothing at request time.** Two passages share a prefix through a response's
/// opening letter (its request relation present) and differ in everything after it: the response's
/// bytes and length, and the future relations (one continuation declares a further part at the very
/// next tick, the other a later part that reaches the first request again). At the request's time
/// the two eggs have the same state (their present branches' checkpoints and their readouts,
/// retention included), the same face, and the same keyed release through the general future branch.
/// Under the former retention law the second continuation's future relation held the first request's
/// span, and under the former future branch the first continuation's declared letter refused the
/// release's first byte.
#[test]
fn a_withheld_continuation_moves_nothing_at_request_time() {
    let prefix: Vec<Vec<usize>> = vec![
        part(0, HUMAN, b"Please read the file alpha.txt now."),
        part(
            2,
            AGENT,
            b"I read the file alpha.txt now, it holds two lines.",
        ),
        part(2, HUMAN, b"Now read the file beta.txt."),
        part(2, AGENT, b""),
    ];
    let mut ticks = Vec::new();
    let mut cells = Vec::new();
    for cells_of in &prefix {
        ticks.push(cells.len() as u64);
        cells.extend(cells_of);
    }
    let present = vec![
        Relation {
            letter: ticks[1],
            kind: RelationKind::Request,
            target: ticks[0],
        },
        Relation {
            letter: ticks[3],
            kind: RelationKind::Request,
            target: ticks[2],
        },
    ];
    let at = cells.len() as u64;
    // Continuation one: the response has no bytes; a further agent part opens at the next tick,
    // reading the same request, and a human return follows.
    let mut one = present.clone();
    one.push(Relation {
        letter: at,
        kind: RelationKind::Request,
        target: ticks[2],
    });
    one.push(Relation {
        letter: at + 20,
        kind: RelationKind::LaterHuman,
        target: ticks[3],
    });
    // Continuation two: a long response, then a later agent part reading the first request.
    let mut two = present.clone();
    two.push(Relation {
        letter: at + 41,
        kind: RelationKind::Request,
        target: ticks[0],
    });
    let mut eggs = [egg(one), egg(two)];
    for egg in &mut eggs {
        for &cell in &cells {
            egg.receive(cell)
                .expect("the prefix through the response's opening");
        }
    }
    let [first, second] = &eggs;
    assert_eq!(first.face(), second.face(), "the same face");
    assert_eq!(
        readout(first),
        readout(second),
        "the same readout, retention included"
    );
    assert_eq!(
        first.branch_at_present().encode_checkpoint(),
        second.branch_at_present().encode_checkpoint(),
        "the same present state"
    );
    let release = |egg: &AdmittedEgg| {
        let branch = Family::branch_future(egg).expect("the admitted egg branches its future");
        let mut alone = Population::new(vec![branch]).expect("the egg alone");
        let mut stream = keys(29);
        alone.release_response(chart(), 64, ResponseLaw::Scored, &mut stream)
    };
    let released = release(first);
    assert_eq!(released, release(second), "the same keyed release");
    assert!(
        released.refusal.is_none(),
        "no declared future letter refuses a byte"
    );
}

/// [THE_REBUILD U6: state per conversation] **A request is held across another conversation's
/// parts, and each conversation's addresses are its own.** Aeon 1's request, then aeon 2's request
/// and response, then aeon 1's response reading its request: the request is held (the human part of
/// aeon 2 began aeon 2's run, not aeon 1's), and aeon 1's response is read in aeon 1's addresses.
#[test]
fn a_request_is_held_across_another_conversations_parts() {
    let parts: Vec<(u64, Vec<usize>)> = vec![
        (1, part(0, HUMAN, b"Please read the file alpha.txt now.")),
        (2, part(0, HUMAN, b"What does beta.txt hold?")),
        (2, part(2, AGENT, b"Beta holds one line.")),
        (1, part(1, AGENT, b"I read the file alpha.txt now.")),
    ];
    let mut ticks = Vec::new();
    let mut cells: Vec<usize> = Vec::new();
    for (_, cells_of) in &parts {
        ticks.push(cells.len());
        cells.extend(cells_of);
    }
    let relations = vec![
        Relation {
            letter: ticks[2] as u64,
            kind: RelationKind::Request,
            target: ticks[1] as u64,
        },
        Relation {
            letter: ticks[3] as u64,
            kind: RelationKind::Request,
            target: ticks[0] as u64,
        },
    ];
    let mut interleaved = egg(relations);
    let mut alone = egg(vec![Relation {
        letter: (ticks[1] - ticks[0]) as u64,
        kind: RelationKind::Request,
        target: 0,
    }]);
    for (index, (aeon, cells_of)) in parts.iter().enumerate() {
        interleaved
            .enter_aeon(*aeon)
            .expect("an aeon at its letter");
        for (at, &cell) in cells_of.iter().enumerate() {
            if *aeon == 1 {
                if at > 0 {
                    assert_eq!(
                        interleaved.inner().addresses().expect("the addresses"),
                        alone.inner().addresses().expect("the addresses"),
                        "part {index}, cell {at}: aeon 1's own addresses"
                    );
                }
                alone.receive(cell).expect("aeon 1 alone");
            }
            interleaved.receive(cell).expect("the interleaved passage");
        }
    }
    let readout = readout(&interleaved);
    assert_eq!(readout.released, vec![0, 0], "both requests held");
    assert_eq!(readout.pointers[RelationKind::Request.index()].held, 2);
    assert!(
        readout.stages[0].copies > 0,
        "aeon 1's response copied its request"
    );
}
