//! One actual reception makes an internal mode productive through the existing material map.
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        NativeConstitutiveField, NativeFieldOccurrence, NativeJunctionSeed,
        NativeMaterialModeComponent, NativeMaterialTransportSource, NativePhaseCurrent,
    },
    resident_section::{ResidentGrain, ResidentSurface, TransferCensus},
};
use serde_json::{Value, json};
use std::{error::Error, fs::OpenOptions, io::Write, path::PathBuf, time::Instant};
fn input(r: i64, i: i64, d: i64) -> Vec<NativePhaseCurrent> {
    vec![
        NativePhaseCurrent::new(r, i, d).unwrap(),
        NativePhaseCurrent::zero(),
    ]
}
fn work(a: TransferCensus, b: TransferCensus) -> Value {
    json!({"deeds":b.deed_launches-a.deed_launches,
    "section_readouts":b.section_read_outs-a.section_read_outs,"ingress_octets":b.ingress_octets-a.ingress_octets,
    "numerical_egress_octets":b.egress_section_octets-a.egress_section_octets,
    "receipt_egress_octets":b.egress_receipt_octets-a.egress_receipt_octets})
}
fn main() -> Result<(), Box<dyn Error>> {
    let path = PathBuf::from(
        std::env::args()
            .nth(1)
            .ok_or("usage: native_material_mode NEW.json")?,
    );
    if path.exists() {
        return Err("output exists".into());
    }
    let start = Instant::now();
    let readout = ResidentReadout::new()?;
    let s = ResidentSurface::on(&readout)?;
    let mut b = NativeConstitutiveField::found_with_enclosed_junction(
        &s,
        vec![
            NativeJunctionSeed {
                incoming_admittance: 1,
                held_admittance: 1,
                incoming_transport: NativePhaseCurrent::unit(),
                initial_held: NativePhaseCurrent::zero()
            };
            2
        ],
        ResidentGrain(72),
    )?;
    b.enable_material_transport_source(NativeMaterialTransportSource::CompleteCurrent)?;
    let first = b.advance_resident(&mut NativeFieldOccurrence::entering(input(1, 0, 1)))?;
    let source = b.retain_source(&first.source)?;
    for _ in 0..2 {
        b.advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &source,
            input(1, 0, 1),
        ))?;
    }
    b.advance_resident(&mut NativeFieldOccurrence::entering(input(-9, 0, 10)))?;
    b.advance_resident(&mut NativeFieldOccurrence::entering(input(0, 0, 1)))?;
    let last = b.advance_resident(&mut NativeFieldOccurrence::entering(input(0, 0, 1)))?;
    let source_at = last.lineage.occurrence;
    let mode = b.condense_shared_drive_mode(1, 2)?;
    let before = b.census();
    let old = b.read_material_mode_using(source_at, &mode)?;
    let old_work = work(before, b.census());
    let received = vec![
        NativePhaseCurrent::unit(),
        NativePhaseCurrent::new(-1, 0, 1)?,
    ];
    b.advance_resident(&mut NativeFieldOccurrence::through(
        last.source,
        received.clone(),
    ))?;
    let before = b.census();
    let current = b.read_material_mode_using(source_at, &mode)?;
    let current_work = work(before, b.census());
    let old_read = old.inspect()?;
    let current_read = current.inspect()?;
    let original = current.read_pairs(NativeMaterialModeComponent::CurrentMode, 1)?;
    if original.negative != 1 || original.unresolved != 0 {
        return Err("current material mode did not produce the negative differential".into());
    }
    drop(b);
    let before = s.census();
    let future = current.unfold_current(1)?;
    let future_work = work(before, s.census());
    let future_receiver = future.read_pairs(1)?;
    if future_receiver.positive != 1 || future_receiver.unresolved != 0 {
        return Err("unfolded material mode did not produce the positive differential".into());
    }
    let report = json!({"schema":"holonics.material-mode-study.v1","truth_status":"established-bounded","evidence_tags":["measured"],
        "source_occurrence":source_at,"actual_received":received,"before":old_read,"after":current_read,
        "before_work":old_work,"after_work":current_work,"current_receiver":original,
        "future_work":future_work,"future_current":future.inspect()?,"future_receiver":future_receiver,
        "source_field_dropped_before_unfolding":true,"whole_seconds":start.elapsed().as_secs_f64(),
        "conversation_quality_established":false,"model_persisted":false});
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options.open(&path)?;
    serde_json::to_writer_pretty(&mut file, &report)?;
    file.write_all(b"\n")?;
    file.sync_all()?;
    println!(
        "{}",
        json!({"report":path,"current_negative":true,"future_positive":true})
    );
    Ok(())
}
