use super::*;
use crate::compression::landmark::context::{
    Capacity, LandmarkDeclaration, Section, SectionChart, SectionSlots, Sections, StopPrior,
};
use crate::receiver::population::admitted::HUMAN;

const POPULATION_CELLS: u64 = 1 << 10;
const GRAIN: u64 = 16;

fn admitted_family() -> AdmittedEgg {
    let chart = SectionChart::curated();
    let sections = Sections::new(chart, SectionSlots::Channel).expect("channel slots");
    let bytes = TreeFamily::sectioned(
        LandmarkDeclaration {
            alphabet: chart.alphabet(),
            depth: 3,
            forced: 0,
            population: POPULATION_CELLS,
            grain: GRAIN,
            family: sections.family().clone(),
            prior: StopPrior::half(),
            capacity: Capacity::Unbounded,
        },
        1,
        sections,
    )
    .expect("sectioned byte tree");
    let inner = BoundaryEgg::new(
        "boundary".to_string(),
        1,
        bytes,
        chart,
        LandmarkDeclaration {
            alphabet: chart.letters(),
            depth: 2,
            forced: 0,
            population: POPULATION_CELLS,
            grain: GRAIN,
            family: BoundaryEgg::letter_family(POPULATION_CELLS).expect("letter family"),
            prior: StopPrior::half(),
            capacity: Capacity::Unbounded,
        },
    )
    .expect("boundary egg");
    AdmittedEgg::new(
        "admitted".to_string(),
        1,
        inner,
        chart,
        Vec::new(),
        CopyLaw::new(2, 3, 2).expect("copy law"),
    )
    .expect("admitted egg")
}

#[test]
fn branch_preserves_current_face_and_receipt_then_diverges_locally() {
    let mut source = Population::new(vec![Box::new(admitted_family())]).expect("population");
    let section = SectionChart::curated()
        .letter(Section {
            kind: 0,
            channel: HUMAN,
        })
        .expect("human section");
    source
        .receive_passage(&[section, usize::from(b'a')])
        .expect("source cell");
    let original_face = source.face().expect("face");
    let original_receipt = source.receipt().expect("receipt");
    let mut branch = source.branch_future().expect("branch");
    assert_eq!(branch.face().expect("branch face"), original_face);
    assert_eq!(branch.receipt().expect("branch receipt"), original_receipt);

    branch
        .receive_passage(&[usize::from(b'b')])
        .expect("branch cell");
    assert_eq!(source.cells(), 2);
    assert_eq!(
        source.receipt().expect("source unchanged"),
        original_receipt
    );
    assert_eq!(branch.cells(), 3);
}

#[test]
fn planned_relation_on_branch_leaves_source_untouched() {
    let source = Population::new(vec![Box::new(admitted_family())]).expect("population");
    let original = source.receipt().expect("receipt");
    let mut branch = source.branch_future().expect("branch");
    branch
        .plan_relation(Relation {
            letter: 2,
            kind: RelationKind::Request,
            target: 1,
        })
        .expect("planned relation");
    assert_eq!(source.receipt().expect("source unchanged"), original);
}
