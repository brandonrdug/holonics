//! SKE4, the apparatus obligation's measurement: the transfer census of one cycle of the resident
//! operator, read from the traces the session already carries.  The contract of 2026-08-18 is
//! measured here, not argued: deed launches, synchronizations, allocations, section read-outs,
//! and section egress per cycle, against the number of operations.

use std::path::Path;

use athena_alpha::AthenaTokenApplication;
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::holonic_intelligence::{
        NativeFullOperatorSession, NativeOperatorResidence, dismantle_full_native_operator,
        mount_operator_surface,
    },
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let root = args.first().cloned().unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let material = args.get(1).cloned().unwrap_or_else(|| "7 + 5 =".to_owned());
    let application = AthenaTokenApplication::open(Path::new(&root))?;
    let addresses = application.encode_turn(&material)?;
    let returned = dismantle_full_native_operator(Path::new(&root))?;
    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let mut residence = NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
    let cycles: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1);
    let mut session = NativeFullOperatorSession::found(&returned.native, &mut residence)?;
    // Earlier cycles of the same line: the census below is the last cycle's alone.
    for _ in 1..cycles {
        let earlier = session.advance_cycle(&addresses)?;
        eprintln!("cycle census: {}", serde_json::to_string(&earlier.successor.census())?);
        session = earlier.successor;
    }
    let before = session.census();
    let started = std::time::Instant::now();
    let cycle = session.advance_cycle(&addresses)?;
    let elapsed = started.elapsed().as_millis();
    let first = &before;
    // After the cycle: the terminal face has crossed to the host, once.
    let after = cycle.successor.census();
    let last = &after;
    let face = application.render(&cycle.final_emission)?;
    let receipt = serde_json::json!({
        "material": material,
        "addresses": addresses.len(),
        "operations": cycle.traces.len(),
        "cycle_milliseconds": elapsed,
        "face": face.rendered,
        "deed_launches": last.deed_launches - first.deed_launches,
        "captured_launches": last.captured_launches - first.captured_launches,
        "synchronizations": last.synchronizations - first.synchronizations,
        "allocations": last.allocations - first.allocations,
        "section_read_outs": last.section_read_outs - first.section_read_outs,
        "egress_section_octets": last.egress_section_octets - first.egress_section_octets,
        "egress_receipt_octets": last.egress_receipt_octets - first.egress_receipt_octets,
        "ingress_octets": last.ingress_octets - first.ingress_octets,
        "resident_octets_peak": last.resident_octets_peak,
        "passages": cycle.traces.iter().map(|t| t.census_after.deed_launches).collect::<std::collections::BTreeSet<_>>().len(),
    });
    println!("{}", serde_json::to_string_pretty(&receipt)?);
    Ok(())
}
