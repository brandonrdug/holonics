use super::*;

#[test]
fn copresent_currents_remain_open_until_a_connecting_return_arrives() {
    let mut ecology = LaboratoryResearchEcology::new(LaboratoryResearchSpec::default());
    let first = MorphologicalLanguagePassage::new(
        "first",
        "theory",
        1,
        "Every result cultivates relational morphology.",
    );
    let second = MorphologicalLanguagePassage::new(
        "second",
        "code",
        2,
        "Language episode owns relational thought current through field relational thought.",
    );
    let bridge = MorphologicalLanguagePassage::new(
        "bridge",
        "returned-interaction",
        3,
        "Relational morphology affects language episode.",
    );

    ecology.receive(&[first]).unwrap();
    let partial = ecology
        .relation
        .as_ref()
        .unwrap()
        .think_fiber(
            "What cultivates relational morphology, and what owns relational thought current?",
            16,
        )
        .unwrap()
        .unwrap();
    assert!(!partial.is_closed());

    ecology.receive(&[second]).unwrap();
    let juxtaposed = ecology
        .relation
        .as_ref()
        .unwrap()
        .think_fiber(
            "What cultivates relational morphology, and what owns relational thought current?",
            16,
        )
        .unwrap()
        .unwrap();
    assert!(!juxtaposed.is_closed());

    ecology.receive(&[bridge]).unwrap();
    let connected = ecology
        .relation
        .as_ref()
        .unwrap()
        .think_fiber(
            "What cultivates relational morphology, and what owns relational thought current?",
            16,
        )
        .unwrap()
        .unwrap();
    assert!(connected.is_closed());
}
