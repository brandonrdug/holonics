use super::*;
use crate::incidence_production::{DeclaredContactFace, DeclaredOccurrence};

#[derive(Clone, Copy)]
enum ExteriorLaw {
    Sum,
    Product,
}

fn value(law: ExteriorLaw, left: i64, right: i64) -> i64 {
    match law {
        ExteriorLaw::Sum => left + right,
        ExteriorLaw::Product => left * right,
    }
}

fn section(
    identity: &str,
    lineage: &str,
    surfaces: [&str; 3],
    faces: [&str; 2],
    law: ExteriorLaw,
) -> CausalSection {
    let occurrence = DeclaredOccurrence::from_text(
        format!("{identity}:incidence"),
        0,
        BTreeSet::new(),
        surfaces.join(" "),
    )
    .expect("declared text material");
    let contact_faces = vec![faces
        .into_iter()
        .map(|face| DeclaredContactFace::new(face).unwrap())
        .collect::<Vec<_>>()];
    let incidence = IncidenceComplex::found_with_contact_faces(&[occurrence], 3, &contact_faces)
        .expect("the exterior chart founds its oriented section");
    let coordinates = [(2, 2), (3, 2), (2, 3), (3, 3)];
    let states = coordinates
        .iter()
        .enumerate()
        .map(|(at, (left, right))| {
            let mut successors = BTreeMap::new();
            match at {
                0 => {
                    successors.insert("raise-left".to_owned(), 1);
                    successors.insert("raise-right".to_owned(), 2);
                }
                1 => {
                    successors.insert("raise-right".to_owned(), 3);
                }
                2 => {
                    successors.insert("raise-left".to_owned(), 3);
                }
                _ => {}
            }
            SectionState {
                observations: BTreeMap::from([
                    ("defined".to_owned(), "yes".to_owned()),
                    ("value".to_owned(), value(law, *left, *right).to_string()),
                ]),
                successors,
            }
        })
        .collect();
    CausalSection {
        identity: identity.to_owned(),
        lineage: lineage.to_owned(),
        incidence,
        states,
        root: 0,
    }
}

fn ecology(prefix: &str) -> CausalSectionEcology {
    CausalSectionEcology::found(vec![
        section(
            &format!("{prefix}infix-sum"),
            "symbolic-infix",
            ["left", "plus", "right"],
            ["left-operand", "right-operand"],
            ExteriorLaw::Sum,
        ),
        section(
            &format!("{prefix}call-sum"),
            "function-call",
            ["add", "left", "right"],
            ["callee-argument", "argument-order"],
            ExteriorLaw::Sum,
        ),
        section(
            &format!("{prefix}infix-product"),
            "symbolic-infix",
            ["left", "times", "right"],
            ["factor", "factor"],
            ExteriorLaw::Product,
        ),
    ])
    .unwrap()
}

#[test]
fn consequence_history_founds_the_class_and_not_the_codec_or_contact_face() {
    let ecology = ecology("");
    let reading = ecology.read_on_host_for_admission().unwrap();
    assert_eq!(
        reading.root_one_shot_blocks,
        vec![BTreeSet::from([
            "call-sum".to_owned(),
            "infix-product".to_owned(),
            "infix-sum".to_owned(),
        ])],
        "all three roots return four before an intervention"
    );
    assert_eq!(reading.root_conduct_blocks.len(), 2);
    assert!(reading.root_conduct_blocks.contains(&BTreeSet::from([
        "call-sum".to_owned(),
        "infix-sum".to_owned(),
    ])));
    assert!(reading
        .root_conduct_blocks
        .contains(&BTreeSet::from(["infix-product".to_owned()])));
    assert!(reading.shortest_separators.iter().all(|separator| {
        separator.interventions.len() == 1
            && separator.receiver.as_deref() == Some("value")
            && !separator.separated_by_terminus
    }));
    assert_eq!(reading.reconstruction_fibers.len(), 2);

    let call = reading
        .presentations
        .iter()
        .find(|presentation| presentation.identity == "call-sum")
        .unwrap();
    let infix = reading
        .presentations
        .iter()
        .find(|presentation| presentation.identity == "infix-sum")
        .unwrap();
    assert_ne!(call.contact_faces, infix.contact_faces);
    assert!(reading
        .root_conduct_blocks
        .iter()
        .any(|block| { block.contains("call-sum") && block.contains("infix-sum") }));
}

#[test]
fn removing_the_value_receiver_only_coarsens_the_root_quotient() {
    let ecology = ecology("");
    let full = ecology.read_on_host_for_admission().unwrap();
    let ablated = ecology.read_without_on_host_for_admission("value").unwrap();
    assert_eq!(full.root_conduct_blocks.len(), 2);
    assert_eq!(ablated.root_conduct_blocks.len(), 1);
    assert_eq!(ablated.root_conduct_blocks[0].len(), 3);
}

#[test]
fn renaming_every_presentation_moves_no_population_shape() {
    let standing = ecology("").read_on_host_for_admission().unwrap();
    let renamed = ecology("renamed-").read_on_host_for_admission().unwrap();
    let shape = |reading: &CausalSectionReading| {
        reading
            .root_conduct_blocks
            .iter()
            .map(BTreeSet::len)
            .collect::<BTreeSet<_>>()
    };
    assert_eq!(shape(&standing), BTreeSet::from([1, 2]));
    assert_eq!(shape(&standing), shape(&renamed));
    assert_eq!(
        standing.shortest_separators.len(),
        renamed.shortest_separators.len()
    );
}

/// The host construction is an admission reader; the production read belongs to the card. This
/// gate compares the complete semantic return, never dense device class ordinals or launch order.
#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_resident_quotient_returns_the_host_admission_reading_exactly() {
    let ecology = ecology("");
    let admitted = ecology.read_on_host_for_admission().unwrap();
    let mut card = CudaRefineExecutor::new().expect("the card mounts");
    let resident = ecology
        .read(&mut card)
        .expect("the card returns the section");
    assert_eq!(resident, admitted);
    assert!(
        card.launches() > 0,
        "the admission cannot pass without a launch"
    );
}
