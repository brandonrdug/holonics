use super::*;
use crate::embedding_fiber::ResidentReadout;
use num_traits::Zero;
fn phase(r: i64, i: i64, d: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(r, i, d).unwrap()
}
fn seed(n: usize) -> Vec<NativeJunctionSeed> {
    vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        };
        n
    ]
}
fn dark<'c>(
    s: &'c ResidentSurface<'c>,
    gap: bool,
    n: usize,
) -> (
    NativeConstitutiveField<'c>,
    NativeFieldContinuation,
    NativeFieldSourceAnchor,
) {
    let mut b =
        NativeConstitutiveField::found_with_enclosed_junction(s, seed(n), ResidentGrain(72))
            .unwrap();
    b.enable_material_transport_source(NativeMaterialTransportSource::CompleteCurrent)
        .unwrap();
    let input = |p| {
        let mut v = vec![phase(0, 0, 1); n];
        v[0] = p;
        v
    };
    let first = b
        .advance_resident(&mut NativeFieldOccurrence::entering(input(phase(1, 0, 1))))
        .unwrap();
    let source = b.retain_source(&first.source).unwrap();
    let mut birth = None;
    for i in 0..2 {
        let next = b
            .advance_resident(&mut NativeFieldOccurrence::through_anchor(
                &source,
                input(phase(1, 0, 1)),
            ))
            .unwrap();
        if i == 0 {
            birth = Some(b.retain_source(&next.source).unwrap());
            if gap {
                b.advance_resident(&mut NativeFieldOccurrence::entering(input(phase(0, 1, 1))))
                    .unwrap();
            }
        }
    }
    b.advance_resident(&mut NativeFieldOccurrence::entering(input(phase(
        -9, 0, 10,
    ))))
    .unwrap();
    b.advance_resident(&mut NativeFieldOccurrence::entering(input(phase(0, 0, 1))))
        .unwrap();
    let last = b
        .advance_resident(&mut NativeFieldOccurrence::entering(input(phase(0, 0, 1))))
        .unwrap();
    (b, last, birth.unwrap())
}
fn column(
    matrix: &[Vec<ExactComplexWaveCurrent>],
    l: usize,
    r: usize,
) -> Vec<ExactComplexWaveCurrent> {
    matrix
        .iter()
        .map(|row| {
            row[l]
                .subtract(&row[r])
                .scaled(&Rat::new(1.into(), 2.into()))
        })
        .collect()
}
fn assert_ball(b: &NativeFieldCurrentBall, v: &[ExactComplexWaveCurrent]) {
    assert!(b.contains(v), "{b:?} does not contain {v:?}");
}

#[test]
#[ignore = "requires CUDA; one actual reception learns the hidden mode's emission contribution"]
fn actual_return_makes_a_dark_source_mode_productive() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let (mut b, last, _) = dark(&s, false, 1);
    let at = last.lineage.occurrence;
    let source = b.retain_source(&last.source).unwrap();
    let old_exact = b
        .inspect_exact_complete_material_transport(at)
        .unwrap()
        .unwrap();
    let internal = b.inspect_internal_currents().unwrap().unwrap();
    let q = internal[0].current.subtract(&internal[1].current);
    assert_eq!(q.real, Rat::new(2.into(), 3.into()));
    let before = b.census();
    let mode = b.condense_shared_drive_mode(1, 2).unwrap();
    let old = b.read_material_mode_using(at, &mode).unwrap();
    assert_eq!(b.census().section_read_outs, before.section_read_outs);
    let old_read = old.inspect().unwrap();
    assert_eq!(old_read.producing_coefficient.radius, Rat::zero());
    assert_eq!(
        old_read.producing_coefficient.center,
        vec![ExactComplexWaveCurrent::zero()]
    );
    assert_eq!(old_read.mode_change.radius, Rat::zero());
    b.advance_resident(&mut NativeFieldOccurrence::through(
        last.source,
        vec![phase(0, 1, 1)],
    ))
    .unwrap();
    let before = b.census();
    let result = b.read_material_mode_using(at, &mode).unwrap();
    assert_eq!(b.census().section_read_outs, before.section_read_outs);
    let future = result.unfold_current(3).unwrap();
    assert_eq!(b.census().section_read_outs, before.section_read_outs);
    let reading = result.inspect().unwrap();
    assert_ball(&reading.source_mode, &[q.clone()]);
    let exact = b
        .inspect_exact_complete_material_transport(at + 1)
        .unwrap()
        .unwrap();
    let old_k = column(&old_exact.coefficients, 3, 4);
    let new_k = column(&exact.coefficients, 3, 4);
    let old_y = old_k.iter().map(|k| k.multiply(&q)).collect::<Vec<_>>();
    let new_y = new_k.iter().map(|k| k.multiply(&q)).collect::<Vec<_>>();
    assert_eq!(new_y, vec![phase(0, 2, 11).current()]);
    assert_ball(&reading.producing_coefficient, &old_k);
    assert_ball(&reading.current_coefficient, &new_k);
    assert_ball(&reading.coefficient_change, &subtract(&new_k, &old_k));
    assert_ball(&reading.producing_mode, &old_y);
    assert_ball(&reading.current_mode, &new_y);
    assert_ball(&reading.mode_change, &subtract(&new_y, &old_y));
    assert_ball(
        &reading.producing_remainder,
        &[ExactComplexWaveCurrent::zero()],
    );
    assert_ball(
        &reading.current_remainder,
        &[ExactComplexWaveCurrent::zero()],
    );
    assert_ball(&reading.current_full, &new_y);
    assert_ball(
        reading.actual_received.as_ref().unwrap(),
        &[phase(0, 1, 1).current()],
    );
    assert_ball(
        reading.whole_returned_difference.as_ref().unwrap(),
        &[phase(0, 1, 1).current()],
    );
    assert_eq!(reading.direct_receiving_occurrence, Some(at + 1));
    assert_ball(&future.inspect().unwrap(), &[phase(0, -2, 11).current()]);
    assert_eq!(
        old.inspect().unwrap().current_mode.center,
        old_read.current_mode.center
    );
    let (mut other, last, _) = dark(&s, false, 1);
    assert!(
        other
            .read_material_mode_using(last.lineage.occurrence, &mode)
            .is_err()
    );
    assert!(other.read_material_mode(&source, 1, 2).is_err());
    let detached = NativeSharedDriveMode::remount(&s, mode.rest().unwrap()).unwrap();
    assert!(b.read_material_mode_using(at, &detached).is_err());
}

#[test]
#[ignore = "requires CUDA; factor chronology before/between/after births and reversed orientation survive archive"]
fn mode_coefficients_match_the_existing_full_operator_and_preserve_the_source_remainder() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let (mut b, last, birth) = dark(&s, true, 1);
    let source = b.retain_source(&last.source).unwrap();
    let at = last.lineage.occurrence;
    let exact_source = b.inspect_exact_junction(at).unwrap().unwrap();
    let internal = b.inspect_internal_currents().unwrap().unwrap();
    let mut x = exact_source.outgoing;
    x.extend(internal.iter().map(|x| x.current.clone()));
    let q = internal[0].current.subtract(&internal[1].current);
    b.advance_resident(&mut NativeFieldOccurrence::through_anchor(
        &source,
        vec![phase(1, 1, 1)],
    ))
    .unwrap();
    // A later return at source 1 uses a column where the left mode member existed and the right
    // did not. Read-only source addresses do not manufacture an available receiving capability.
    b.advance_resident(&mut NativeFieldOccurrence::through_anchor(
        &birth,
        vec![phase(-1, 0, 1)],
    ))
    .unwrap();
    let record = b
        .read_material_mode(&source, 1, 3)
        .unwrap()
        .inspect()
        .unwrap();
    let exact = b
        .inspect_exact_complete_material_transport(b.occurrence_count() - 1)
        .unwrap()
        .unwrap();
    x.resize(exact.coefficients[0].len(), ExactComplexWaveCurrent::zero());
    let full = apply(&exact.coefficients, &x);
    let k = column(&exact.coefficients, 3, 4);
    let projected = k.iter().map(|k| k.multiply(&q)).collect::<Vec<_>>();
    assert_ball(&record.current_coefficient, &k);
    assert_ball(&record.current_mode, &projected);
    assert_ball(&record.current_full, &full);
    assert_ball(&record.current_remainder, &subtract(&full, &projected));
    let reverse = b
        .read_material_mode(&source, 3, 1)
        .unwrap()
        .inspect()
        .unwrap();
    assert_eq!(reverse.numerical_modes, record.numerical_modes);
    assert_eq!(
        reverse.numerical_coefficients[1],
        record.numerical_coefficients[1]
            .iter()
            .map(|v| v.negated())
            .collect::<Vec<_>>()
    );
    let path = std::env::temp_dir().join(format!(
        "holonics-mode-material-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    b.enable_history_archive(&path).unwrap();
    b.archive_history_before(b.occurrence_count()).unwrap();
    assert_eq!(
        b.read_material_mode(&source, 1, 3)
            .unwrap()
            .inspect()
            .unwrap()
            .numerical_modes,
        record.numerical_modes
    );
    assert!(b.read_material_mode_at(1, 1, 3).is_err());
    drop(b);
    std::fs::remove_file(path).unwrap();
}

#[test]
#[ignore = "requires CUDA; a bounded material-mode generator supplies exact differential receivers without a point seal"]
fn learned_mode_unfolding_reaches_a_native_receiver() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let (mut b, last, _) = dark(&s, false, 2);
    let source = b.retain_source(&last.source).unwrap();
    b.advance_resident(&mut NativeFieldOccurrence::through(
        last.source,
        vec![phase(1, 0, 1), phase(-1, 0, 1)],
    ))
    .unwrap();
    let mode = b.read_material_mode(&source, 1, 2).unwrap();
    let now = mode
        .read_pairs(NativeMaterialModeComponent::CurrentMode, 1)
        .unwrap();
    assert_eq!((now.positive, now.negative, now.unresolved), (0, 1, 0));
    let future = mode.unfold_current(1).unwrap();
    drop(b);
    let read = future.read_pairs(1).unwrap();
    assert_eq!((read.positive, read.negative, read.unresolved), (1, 0, 0));
    assert_eq!(read.future_steps, 1);
    assert_ball(
        &future.inspect().unwrap(),
        &[phase(-2, 0, 11).current(), phase(2, 0, 11).current()],
    );
    assert!(
        mode.read_pairs(NativeMaterialModeComponent::CurrentMode, 2)
            .is_err()
    );
}
