//! Internal-current source, learned local generator, and an independently executable mode.
//! The driver supplies declared interventions; the engine owns every inference and condensation.
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        ConstitutiveReading, NativeConstitutiveField, NativeFieldOccurrence, NativeJunctionSeed,
        NativePhaseCurrent, NativeSharedDriveMode, NativeSharedDriveModeRest,
        ResidentConstitutiveCurrent, ResidentConstitutiveFibre,
    },
    resident_section::{
        ResidentGrain, ResidentSection, ResidentSectionRest, ResidentSurface, TransferCensus,
    },
};
use serde_json::{Value, json};
use std::{error::Error, fs::OpenOptions, io::Write, path::PathBuf, time::Instant};
type E = Box<dyn Error>;
fn mount<'c>(s: &'c ResidentSurface<'c>, v: &[i64]) -> Result<ResidentSection<'c>, E> {
    Ok(s.mount_section_rest(&ResidentSectionRest::found(
        1,
        v.len(),
        ResidentGrain(0),
        64,
        v.iter().map(|x| (*x, *x)).collect(),
    )?)?)
}
fn current<'a, 'c>(s: &'a ResidentSection<'c>) -> Result<ResidentConstitutiveCurrent<'a, 'c>, E> {
    Ok(ResidentConstitutiveCurrent::rational(s)?)
}
fn seeds() -> Vec<NativeJunctionSeed> {
    vec![NativeJunctionSeed {
        incoming_admittance: 1,
        held_admittance: 1,
        incoming_transport: NativePhaseCurrent::unit(),
        initial_held: NativePhaseCurrent::zero(),
    }]
}
fn work(a: TransferCensus, b: TransferCensus) -> Value {
    json!({"deeds":b.deed_launches-a.deed_launches,
    "section_readouts":b.section_read_outs-a.section_read_outs,"ingress_octets":b.ingress_octets-a.ingress_octets,
    "numerical_egress_octets":b.egress_section_octets-a.egress_section_octets,
    "receipt_egress_octets":b.egress_receipt_octets-a.egress_receipt_octets})
}
fn write_new(path: &std::path::Path, bytes: &[u8]) -> Result<(), E> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut f = options.open(path)?;
    f.write_all(bytes)?;
    f.sync_all()?;
    Ok(())
}
fn main() -> Result<(), E> {
    let path = PathBuf::from(
        std::env::args()
            .nth(1)
            .ok_or("usage: native_internal_mode NEW.json")?,
    );
    let model_path = path.with_extension("hnm");
    if path.exists() || model_path.exists() {
        return Err("output already exists".into());
    }
    let start = Instant::now();
    let r = ResidentReadout::new()?;
    let s = ResidentSurface::on(&r)?;
    // All source-field owners and their derived current snapshots leave this scope. Only the
    // serialized mode and explicit cold evidence survive into independent generator execution.
    let (body_record, bytes, expected) = {
        let mut body = NativeConstitutiveField::found_with_paired_junction(&s, seeds())?;
        let one = mount(&s, &[1, 0, 1])?;
        let zero = mount(&s, &[0, 0, 1])?;
        let cancel = mount(&s, &[-9, 0, 10])?;
        let first = body.advance_current_resident(
            &mut NativeFieldOccurrence::entering(vec![]),
            current(&one)?,
        )?;
        let source = body.retain_source(&first.source)?;
        for _ in 0..2 {
            body.advance_current_resident(
                &mut NativeFieldOccurrence::through_anchor(&source, vec![]),
                current(&one)?,
            )?;
        }
        body.advance_current_resident(
            &mut NativeFieldOccurrence::entering(vec![]),
            current(&cancel)?,
        )?;
        for _ in 0..2 {
            body.advance_current_resident(
                &mut NativeFieldOccurrence::entering(vec![]),
                current(&zero)?,
            )?;
        }
        let mut law = ResidentConstitutiveFibre::found(&s, 2, 2)?;
        let before = body.census();
        let a = body.read_internal_current_at(1)?;
        body.advance_current_resident(
            &mut NativeFieldOccurrence::entering(vec![]),
            current(&zero)?,
        )?;
        let b = body.read_internal_current_at(1)?;
        law.advance_resident(a.current(), Some(b.current()))?;
        let prediction = law.advance_resident(b.current(), None)?;
        let learning_work = work(before, body.census());
        body.advance_current_resident(
            &mut NativeFieldOccurrence::entering(vec![]),
            current(&zero)?,
        )?;
        let actual = body.read_internal_current_at(1)?.inspect()?;
        let ConstitutiveReading::Unique { current: predicted } =
            prediction.inspect()?.predecessor_reading
        else {
            return Err("local generator remains open".into());
        };
        if predicted
            != vec![
                actual.current.center[0].real.clone(),
                actual.current.center[0].imaginary.clone(),
            ]
        {
            return Err("learned internal generator disagrees".into());
        }
        let before = body.census();
        let mode = body.condense_shared_drive_mode(1, 2)?;
        let formation_work = work(before, body.census());
        let initial = mode.unfold(0)?.inspect()?;
        let before = body.census();
        let future = mode.unfold(3)?;
        let future_work = work(before, body.census());
        let interventions = [[2, 1, 1], [-1, 2, 1], [0, -1, 1]];
        for words in interventions {
            let input = mount(&s, &words)?;
            body.advance_current_resident(
                &mut NativeFieldOccurrence::entering(vec![]),
                current(&input)?,
            )?;
        }
        let full = body
            .inspect_internal_currents()?
            .ok_or("missing internal current")?;
        let actual_mode = full[0].current.subtract(&full[1].current);
        let expected = future.inspect()?;
        if !expected.current.contains(&[actual_mode.clone()]) {
            return Err("mode disagrees after independent forcing".into());
        }
        let mut bytes = Vec::new();
        mode.rest()?.write(&mut bytes)?;
        let record = json!({"first_internal":a.inspect()?,"second_internal":b.inspect()?,
            "learned_prediction":predicted,"actual_next_internal":actual,"learning_work":learning_work,
            "mode_initial":initial,"mode_formation_work":formation_work,"future_steps":3,"future_work":future_work,
            "later_interventions":interventions,"actual_future_difference":actual_mode,
            "captured_future":expected,"source_occurrences_executed":body.occurrence_count()});
        (record, bytes, expected)
    };
    let rest = NativeSharedDriveModeRest::read(&mut bytes.as_slice(), bytes.len() as u64)?;
    let before = s.census();
    let mode = NativeSharedDriveMode::remount(&s, rest)?;
    let remount_work = work(before, s.census());
    let mut receiver = NativeConstitutiveField::found(&s, seeds())?;
    let before = s.census();
    let restored = mode.unfold(3)?;
    receiver.advance_current_resident(
        &mut NativeFieldOccurrence::entering(vec![]),
        restored.current(),
    )?;
    let independent_work = work(before, s.census());
    if restored.inspect()? != expected {
        return Err("independent mode return disagrees".into());
    }
    let report = json!({"schema":"holonics.internal-mode-study.v1","truth_status":"established-bounded",
        "evidence_tags":["measured"],"body":body_record,"mode_artifact":model_path,"mode_octets":bytes.len(),
        "remount_work":remount_work,"independent_unfold_and_field_work":independent_work,
        "restored_future":restored.inspect()?,"actual_recipient_input":receiver.inspect_incoming(0)?,
        "source_field_dropped_before_remount":true,"whole_seconds":start.elapsed().as_secs_f64(),
        "conversation_quality_established":false,"acoustic_model_established":false});
    let mut report_bytes = serde_json::to_vec_pretty(&report)?;
    report_bytes.push(b'\n');
    write_new(&model_path, &bytes)?;
    write_new(&path, &report_bytes)?;
    println!(
        "{}",
        json!({"report":path,"mode":model_path,"mode_octets":bytes.len(),"independent_equal":true})
    );
    Ok(())
}
