use super::super::super::tests::row_space;
use super::super::super::*;
use crate::dimensional_wave::ExactComplexWaveCurrent;
use crate::embedding_fiber::ResidentReadout;
use num_rational::BigRational as Rat;

fn phase(real: i64, imaginary: i64, denominator: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(real, imaginary, denominator).unwrap()
}

fn equal_seed(nodes: usize) -> Vec<NativeJunctionSeed> {
    (0..nodes)
        .map(|_| NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        })
        .collect()
}

fn input(left: NativePhaseCurrent, right: NativePhaseCurrent) -> Vec<NativePhaseCurrent> {
    vec![left, right]
}

fn relation_rows(body: &NativeConstitutiveField<'_>) -> Vec<Vec<Rat>> {
    let rest = body.inspect_relation().unwrap();
    rest.intervals
        .chunks_exact(rest.width)
        .map(|row| {
            row.iter()
                .map(|(lower, upper)| {
                    assert_eq!(lower, upper);
                    Rat::from_integer((*lower).into())
                })
                .collect()
        })
        .collect()
}

fn rotate_source_row(mut row: Vec<Rat>, gauges: &[NativePhaseCurrent], nodes: usize) -> Vec<Rat> {
    for node in 0..nodes {
        for branch in 0..2 {
            let at = 4 * node + 2 * branch;
            let current = ExactComplexWaveCurrent::new(row[at].clone(), row[at + 1].clone());
            let rotated = gauges[node].current().multiply(&current);
            row[at] = rotated.real;
            row[at + 1] = rotated.imaginary;
        }
    }
    row
}

fn root_source(step: &NativeFieldStep) -> Vec<ExactComplexWaveCurrent> {
    step.outgoing
        .iter()
        .zip(step.held_successor.iter())
        .zip(step.frame.root_to_local())
        .flat_map(|((outgoing, held), gauge)| {
            let inverse = gauge.current().conjugate();
            [inverse.multiply(outgoing), inverse.multiply(held)]
        })
        .collect()
}

fn root_source_remainder(remainder: &[Rat], frame: &NativeCurrentFrame) -> Vec<Rat> {
    let mut root = Vec::with_capacity(remainder.len());
    for (node, gauge) in frame.root_to_local().iter().enumerate() {
        let inverse = gauge.current().conjugate();
        for branch in 0..2 {
            let at = 4 * node + 2 * branch;
            let current =
                ExactComplexWaveCurrent::new(remainder[at].clone(), remainder[at + 1].clone());
            let transported = inverse.multiply(&current);
            root.extend([transported.real, transported.imaginary]);
        }
    }
    root
}

fn in_span(rows: &[Vec<Rat>], vector: Vec<Rat>) -> bool {
    let mut extended = rows.to_vec();
    extended.push(vector);
    row_space(extended) == row_space(rows.to_vec())
}

fn assert_same_former_receiver(
    base: &ConstitutiveReading,
    changed: &ConstitutiveReading,
    frame: &NativeCurrentFrame,
    source_root: Vec<Rat>,
    relation_before: &[Vec<Rat>],
) {
    let source_width = source_root.len();
    let domain = relation_before
        .iter()
        .map(|row| row[..source_width].to_vec())
        .collect::<Vec<_>>();
    match (base, changed) {
        (
            ConstitutiveReading::Unique { current: left },
            ConstitutiveReading::Unique { current: right },
        ) => {
            assert_eq!(left, right);
            let mut pair = source_root;
            pair.extend(left.clone());
            assert!(in_span(relation_before, pair));
        }
        (
            ConstitutiveReading::OutsideDomain {
                source_remainder: left,
            },
            ConstitutiveReading::OutsideDomain {
                source_remainder: right,
            },
        ) => {
            let root = root_source_remainder(right, frame);
            assert!(in_span(
                &domain,
                source_root
                    .iter()
                    .zip(left)
                    .map(|(source, remainder)| source - remainder)
                    .collect(),
            ));
            assert!(in_span(
                &domain,
                source_root
                    .iter()
                    .zip(&root)
                    .map(|(source, remainder)| source - remainder)
                    .collect(),
            ));
            assert!(in_span(
                &domain,
                root.iter()
                    .zip(left)
                    .map(|(changed, base)| changed - base)
                    .collect(),
            ));
            assert!(!in_span(&domain, left.clone()));
        }
        (
            ConstitutiveReading::Plural {
                particular: left,
                directions: left_directions,
            },
            ConstitutiveReading::Plural {
                particular: right,
                directions: right_directions,
            },
        ) => {
            assert_eq!(
                row_space(left_directions.clone()),
                row_space(right_directions.clone())
            );
            assert!(in_span(
                left_directions,
                right
                    .iter()
                    .zip(left)
                    .map(|(right, left)| right - left)
                    .collect(),
            ));
            let mut pair = source_root;
            pair.extend(left.clone());
            assert!(in_span(relation_before, pair));
        }
        _ => panic!("rechart changed the receiver species"),
    }
}

#[test]
#[ignore = "requires CUDA; field rechart transports old source frames through a continuing field"]
fn field_rechart_preserves_root_receiver_fibre_and_historic_source_bytes() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut base = NativeConstitutiveField::found(&surface, equal_seed(2)).unwrap();
    let mut changed = NativeConstitutiveField::found(&surface, equal_seed(2)).unwrap();
    let first_input = input(phase(1, 0, 1), phase(0, 1, 1));
    let mut base_step = base
        .advance(&mut NativeFieldOccurrence::entering(first_input.clone()))
        .unwrap();
    let mut changed_step = changed
        .advance(&mut NativeFieldOccurrence::entering(first_input))
        .unwrap();
    for pair in [
        input(phase(2, 1, 1), phase(-1, 1, 1)),
        input(phase(1, -2, 1), phase(2, 0, 1)),
    ] {
        base_step = base
            .advance(&mut NativeFieldOccurrence::through(
                base_step.source,
                pair.clone(),
            ))
            .unwrap();
        changed_step = changed
            .advance(&mut NativeFieldOccurrence::through(
                changed_step.source,
                pair,
            ))
            .unwrap();
    }
    let historic = (0..changed.occurrence_count())
        .map(|occurrence| changed.inspect_source(occurrence).unwrap())
        .collect::<Vec<_>>();
    let relation_before = relation_rows(&changed);
    let gauges = [phase(3, 4, 5), phase(0, -1, 1)];
    changed.rechart(&gauges).unwrap();
    assert_eq!(changed.current_frame().ordinal(), 1);
    assert_eq!(changed.recharts().len(), 1);
    assert_eq!(changed.recharts()[0].before.ordinal(), 0);
    assert_eq!(
        changed.recharts()[0].after.root_to_local(),
        gauges.as_slice()
    );
    for (occurrence, before) in historic.iter().enumerate() {
        assert_eq!(changed.inspect_source(occurrence).unwrap(), *before);
        assert_eq!(changed.lineage(occurrence).unwrap().frame, 0);
        assert_eq!(changed.source_frame(occurrence).unwrap().ordinal(), 0);
    }
    let transformed = relation_before
        .iter()
        .cloned()
        .map(|row| rotate_source_row(row, &gauges, 2))
        .collect::<Vec<_>>();
    assert_eq!(row_space(relation_rows(&changed)), row_space(transformed));

    let source_root = root_source(&base_step)
        .into_iter()
        .flat_map(|current| [current.real, current.imaginary])
        .collect::<Vec<_>>();
    let incoming = input(phase(2, 3, 1), phase(-1, 4, 1));
    let base_return = base
        .advance(&mut NativeFieldOccurrence::through(
            base_step.source,
            incoming.clone(),
        ))
        .unwrap();
    let changed_return = changed
        .advance(&mut NativeFieldOccurrence::through(
            changed_step.source,
            incoming,
        ))
        .unwrap();
    assert_eq!(base_return.lineage.frame, 0);
    assert_eq!(changed_return.lineage.frame, 1);
    assert_eq!(
        changed
            .source_frame(changed_return.lineage.occurrence)
            .unwrap()
            .root_to_local(),
        gauges.as_slice()
    );
    assert_eq!(root_source(&base_return), root_source(&changed_return));
    let current_source_root = root_source(&base_return)
        .into_iter()
        .flat_map(|current| [current.real, current.imaginary])
        .collect();
    assert_same_former_receiver(
        &base_return.receiver,
        &changed_return.receiver,
        &changed_return.frame,
        current_source_root,
        &relation_rows(&base),
    );
    for (body, step) in [(&base, &base_return), (&changed, &changed_return)] {
        let held = body.inspect_held().unwrap();
        for (node, words) in held.intervals.chunks_exact(3).enumerate() {
            assert!(words.iter().all(|(lo, hi)| lo == hi));
            assert_eq!(
                phase(words[0].0, words[1].0, words[2].0).current(),
                step.held_successor[node]
            );
        }
    }
    let base_difference = base_return.received_difference.as_ref().unwrap();
    let changed_difference = changed_return.received_difference.as_ref().unwrap();
    assert_eq!(
        base_difference.source_occurrence,
        changed_difference.source_occurrence
    );
    assert_eq!(base_difference.arrived, changed_difference.arrived);
    assert_same_former_receiver(
        &base_difference.former_receiver,
        &changed_difference.former_receiver,
        &changed_return.frame,
        source_root,
        &relation_before,
    );
}

#[test]
#[ignore = "requires CUDA; a physical phase change differs from a rechart"]
fn physical_field_incidence_change_preserves_history_and_changes_new_current() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut base = NativeConstitutiveField::found(&surface, equal_seed(2)).unwrap();
    let mut physical = NativeConstitutiveField::found(&surface, equal_seed(2)).unwrap();
    let first_input = input(phase(1, 0, 1), phase(0, 1, 1));
    base.advance(&mut NativeFieldOccurrence::entering(first_input.clone()))
        .unwrap();
    physical
        .advance(&mut NativeFieldOccurrence::entering(first_input))
        .unwrap();
    let source_before = physical.inspect_source(0).unwrap();
    let held_before = physical.inspect_held().unwrap();
    let relation_before = physical.inspect_relation().unwrap();
    physical
        .replace_incoming_transport(0, phase(0, 1, 1))
        .unwrap();
    assert_eq!(physical.inspect_source(0).unwrap(), source_before);
    assert_eq!(physical.inspect_held().unwrap(), held_before);
    assert_eq!(physical.inspect_relation().unwrap(), relation_before);
    assert_eq!(physical.current_frame().ordinal(), 0);
    assert_eq!(physical.incidence_changes().len(), 1);
    let next_input = input(phase(1, 1, 1), phase(1, -1, 1));
    let base_next = base
        .advance(&mut NativeFieldOccurrence::entering(next_input.clone()))
        .unwrap();
    let physical_next = physical
        .advance(&mut NativeFieldOccurrence::entering(next_input))
        .unwrap();
    // With matched admittances the immediate outgoing branch is the old held branch. The
    // physical incidence change first appears in the newly retained held successor.
    assert_eq!(base_next.outgoing, physical_next.outgoing);
    assert_ne!(base_next.held_successor[0], physical_next.held_successor[0]);
    assert_eq!(base_next.held_successor[1], physical_next.held_successor[1]);
    let base_later = base
        .advance(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::zero(),
            NativePhaseCurrent::zero(),
        ]))
        .unwrap();
    let physical_later = physical
        .advance(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::zero(),
            NativePhaseCurrent::zero(),
        ]))
        .unwrap();
    assert_ne!(base_later.outgoing[0], physical_later.outgoing[0]);
    assert_eq!(base_later.outgoing[1], physical_later.outgoing[1]);
}

#[test]
#[ignore = "requires CUDA; shape and arithmetic refusal must preserve a live field owner"]
fn refused_field_rechart_preserves_owner_and_old_source_handle() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut seed = equal_seed(2);
    seed[0].initial_held = phase(23, 17, 7);
    let mut body = NativeConstitutiveField::found(&surface, seed).unwrap();
    let first = body
        .advance(&mut NativeFieldOccurrence::entering(input(
            phase(1, 0, 1),
            phase(0, 1, 1),
        )))
        .unwrap();
    let held = body.inspect_held().unwrap();
    let relation = body.inspect_relation().unwrap();
    let source = body.inspect_source(0).unwrap();
    let before = body.census();
    assert!(matches!(
        body.rechart(&[phase(1, 1, 1), NativePhaseCurrent::unit()]),
        Err(ConstitutiveFibreError::Shape)
    ));
    assert_eq!(body.census(), before);
    assert_eq!(body.inspect_held().unwrap(), held);
    assert_eq!(body.inspect_relation().unwrap(), relation);
    assert_eq!(body.inspect_source(0).unwrap(), source);
    assert_eq!(body.current_frame().ordinal(), 0);
    assert!(body.recharts().is_empty());
    let huge = phase(
        999_999_999_999_999_999,
        2_000_000_000,
        1_000_000_000_000_000_001,
    );
    assert!(matches!(
        body.rechart(&[huge, NativePhaseCurrent::unit()]),
        Err(ConstitutiveFibreError::Arithmetic(_))
    ));
    assert_eq!(body.inspect_held().unwrap(), held);
    assert_eq!(body.inspect_relation().unwrap(), relation);
    assert_eq!(body.inspect_source(0).unwrap(), source);
    assert_eq!(body.current_frame().ordinal(), 0);
    body.advance(&mut NativeFieldOccurrence::through(
        first.source,
        input(phase(1, 0, 1), phase(0, 1, 1)),
    ))
    .unwrap();
}
