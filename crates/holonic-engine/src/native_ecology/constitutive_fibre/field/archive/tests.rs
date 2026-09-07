use super::*;
use crate::embedding_fiber::ResidentReadout;

fn path(label: &str) -> std::path::PathBuf {
    std::env::temp_dir().join(format!(
        "holonics-history-{label}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ))
}
fn seed() -> Vec<NativeJunctionSeed> {
    vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero()
        };
        2
    ]
}
fn input(n: i64) -> Vec<NativePhaseCurrent> {
    vec![
        NativePhaseCurrent::new(n, 1, 1).unwrap(),
        NativePhaseCurrent::new(1, -n, 1).unwrap(),
    ]
}
fn develop(body: &mut NativeConstitutiveField<'_>, archive: bool) {
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(input(1)))
        .unwrap();
    let anchor = body.retain_source(&first.source).unwrap();
    let mut source = first.source;
    for at in 1..12 {
        if at == 3 {
            body.rechart(&[
                NativePhaseCurrent::new(0, 1, 1).unwrap(),
                NativePhaseCurrent::new(-1, 0, 1).unwrap(),
            ])
            .unwrap();
        }
        if at == 8 {
            body.replace_incoming_transport(1, NativePhaseCurrent::new(0, -1, 1).unwrap())
                .unwrap();
        }
        let mut occurrence = if at == 4 || at == 10 {
            NativeFieldOccurrence::through_anchor(&anchor, input(at + 1))
        } else {
            NativeFieldOccurrence::through(source, input(at + 1))
        };
        let before = body.census();
        source = body.advance_resident(&mut occurrence).unwrap().source;
        assert_eq!(body.census().section_read_outs, before.section_read_outs);
        if archive && at % 3 == 2 {
            body.archive_history_before(body.occurrence_count())
                .unwrap();
        }
    }
}

#[test]
#[ignore = "requires CUDA; complete archived carriers preserve frames, delayed sources and learned transport"]
fn exterior_history_returns_the_same_complete_successor_and_cold_rest() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut reference =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(), ResidentGrain(72))
            .unwrap();
    reference.enable_material_transport().unwrap();
    develop(&mut reference, false);
    let expected = reference.rest(&[], &[]).unwrap();
    let expected_reading = reference.read_material_transport_pairs(0, 1).unwrap();
    drop(reference);
    let archive_path = path("equality");
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(), ResidentGrain(72))
            .unwrap();
    body.enable_material_transport().unwrap();
    body.enable_history_archive(&archive_path).unwrap();
    develop(&mut body, true);
    let placement = body.history_placement();
    assert_eq!(placement.resident_occurrences, 1);
    assert_eq!(placement.archived_occurrences, 11);
    assert_eq!(placement.restored_sources, 2);
    assert_eq!(
        body.read_material_transport_pairs(0, 1).unwrap(),
        expected_reading
    );
    assert_eq!(body.history_placement(), placement);
    assert_eq!(body.rest(&[], &[]).unwrap(), expected);
    let rest = body.rest(&[], &[]).unwrap();
    drop(body);
    let remount_path = path("remount");
    let before = surface.census();
    let (resumed, _, _) =
        NativeConstitutiveField::remount_with_history_archive(&surface, rest, &remount_path)
            .unwrap();
    assert_eq!(resumed.census().deed_launches, before.deed_launches);
    assert_eq!(resumed.history_placement().resident_occurrences, 1);
    assert_eq!(resumed.rest(&[], &[]).unwrap(), expected);
    drop(resumed);
    std::fs::remove_file(archive_path).unwrap();
    std::fs::remove_file(remount_path).unwrap();
}

#[test]
#[ignore = "requires CUDA; archive I/O failure and source corruption cannot enact a native return"]
fn failed_placement_keeps_residency_and_corrupt_source_refuses_before_native_work() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let archive_path = path("failure");
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(), ResidentGrain(72))
            .unwrap();
    body.enable_material_transport().unwrap();
    body.enable_history_archive(&archive_path).unwrap();
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(input(1)))
        .unwrap();
    let anchor = body.retain_source(&first.source).unwrap();
    let second = body
        .advance_resident(&mut NativeFieldOccurrence::through(first.source, input(2)))
        .unwrap();
    let before = body
        .rest(&[Some(&second.source)], &[Some(&anchor)])
        .unwrap();
    *body.archive.as_mut().unwrap().file.borrow_mut() = File::open(&archive_path).unwrap();
    assert!(body.archive_history_before(2).is_err());
    assert_eq!(body.history_placement().resident_occurrences, 2);
    assert_eq!(
        body.rest(&[Some(&second.source)], &[Some(&anchor)])
            .unwrap(),
        before
    );
    *body.archive.as_mut().unwrap().file.borrow_mut() = OpenOptions::new()
        .read(true)
        .write(true)
        .open(&archive_path)
        .unwrap();
    body.archive_history_before(2).unwrap();
    let entry = body.history[0].archived.as_ref().unwrap().clone();
    let mut file = OpenOptions::new()
        .read(true)
        .write(true)
        .open(&archive_path)
        .unwrap();
    file.seek(SeekFrom::Start(entry.offset + 10)).unwrap();
    let mut original = [0];
    file.read_exact(&mut original).unwrap();
    file.seek(SeekFrom::Start(entry.offset + 10)).unwrap();
    file.write_all(&[original[0] ^ 1]).unwrap();
    let count = body.occurrence_count();
    let census = body.census();
    let mut incoming = NativeFieldOccurrence::through_anchor(&anchor, input(3));
    assert!(body.advance_resident(&mut incoming).is_err());
    assert_eq!(body.occurrence_count(), count);
    assert_eq!(body.census().deed_launches, census.deed_launches);
    file.seek(SeekFrom::Start(entry.offset + 10)).unwrap();
    file.write_all(&original).unwrap();
    assert_eq!(
        body.rest(&[Some(&second.source)], &[Some(&anchor)])
            .unwrap(),
        before
    );
    body.advance_resident(&mut incoming).unwrap();
    drop(body);
    drop(entry);
    drop(file);
    std::fs::remove_file(archive_path).unwrap();
}
