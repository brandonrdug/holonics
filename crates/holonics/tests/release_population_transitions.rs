//! Private captured population transitions, read only at this exterior test boundary.
//! The rows are conditional population operands, not full historical native states.
use holonics::hnn::receiving::{ReceivingStep, receiving_population};
use holonics::ratio::algebraic::ExactInterval;
use holonics::receiver::population::port::PortReading;

#[allow(
    clippy::disallowed_methods,
    reason = "private captured-corpus I/O at the exterior integration-test boundary"
)]
fn read_fixture(path: &str) -> String {
    std::fs::read_to_string(path).unwrap()
}

#[test]
#[ignore = "requires the private captured release-population transition corpus"]
fn saved_release_population_transitions_match_exact_teacher_successors() {
    let path = std::env::var("HOLONICS_RELEASE_POPULATION_TRANSITIONS")
        .expect("declare the private five-column transition corpus");
    let text = read_fixture(&path);
    let mut count = 0;
    for (index, line) in text.lines().enumerate() {
        let columns: Vec<_> = line.split('\t').collect();
        assert_eq!(columns.len(), 5, "transition row {index}");
        let before = columns[0].replace("\\n", "\n");
        let after = columns[4].replace("\\n", "\n");
        let before = PortReading::read(&mut before.lines()).unwrap();
        let after = PortReading::read(&mut after.lines()).unwrap();
        let mut population = receiving_population().with_reading(&before).unwrap();
        let step = ReceivingStep {
            ring: 0,
            tree: columns[1].parse().unwrap(),
            combined: ExactInterval::new(columns[2].parse().unwrap(), columns[3].parse().unwrap())
                .unwrap(),
        };
        population.receive(&step.faces()).unwrap();
        assert_eq!(
            population.reading(),
            after,
            "exact teacher successor at archived row {index}"
        );
        count += 1;
    }
    assert_eq!(
        count, 56,
        "the complete declared same-prefix mismatch corpus"
    );
}
