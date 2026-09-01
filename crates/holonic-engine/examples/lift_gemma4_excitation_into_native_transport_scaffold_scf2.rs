use std::{env, error::Error, path::PathBuf};

use holonic_engine::{
    native_ecology::holonic_intelligence::{
        Bf16ExcitationDismantling, profile_dismantling_return,
        read_complete_gemma4_excitation_receipt,
    },
    receiver_exact_compression::ReceiverId,
    soulkiller::dismantle,
};
use serde_json::json;

fn main() -> Result<(), Box<dyn Error>> {
    let root = env::args()
        .nth(1)
        .map(PathBuf::from)
        .ok_or("usage: lift_gemma4_excitation_into_native_transport_scaffold_scf2 RETURN_DIR")?;
    let receipt = read_complete_gemma4_excitation_receipt(&root)?;
    let open_exterior = receipt.open_exterior.clone();
    let excitations = receipt
        .families
        .into_iter()
        .flat_map(|family| family.excitations)
        .collect();
    let returned = dismantle(Bf16ExcitationDismantling {
        receiver: ReceiverId(1),
        excitations,
    })?;
    let profile = profile_dismantling_return(&returned)?;
    let native_wire = returned.native.canonical_bytes()?;
    let native_text = String::from_utf8(native_wire.clone())?.to_ascii_lowercase();
    let cold_coordinates_absent = ["text", "image", "audio", "video", "source_sha256"]
        .iter()
        .all(|coordinate| !native_text.contains(coordinate));
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "native_scaffold_octets": native_wire.len(),
            "spool_population": returned.native.spools.len(),
            "thread_population": returned.native.spools.iter().map(|spool| spool.threads.len()).sum::<usize>(),
            "native_population": returned.native.spools.iter().map(|spool| spool.native_population.len()).sum::<usize>(),
            "winding_population": returned.native.spools.iter().map(|spool| spool.generator_family.len()).sum::<usize>(),
            "open_generator_faces": returned.native.spools.iter().flat_map(|spool| &spool.generator_descents).map(|descent| descent.open_domain.len()).sum::<usize>(),
            "factorized_section_blocks": returned.native.spools.iter().flat_map(|spool| &spool.threads).flat_map(|thread| &thread.sections).map(|section| section.entering.blocks.len() + section.returned.blocks.len()).sum::<usize>(),
            "factorized_section_coordinates": returned.native.spools.iter().flat_map(|spool| &spool.threads).flat_map(|thread| &thread.sections).map(|section| section.entering.coordinate_population + section.returned.coordinate_population).sum::<u64>(),
            "profiled_holons": profile.productive_profile.holons.len(),
            "cold_excitation_population": returned.exterior.excitations.len(),
            "cold_coordinates_absent_from_native_wire": cold_coordinates_absent,
            "insufficiency_retained_fibre": returned.insufficiency.retained_fibre.len(),
            "open_exterior": open_exterior,
        }))?
    );
    Ok(())
}
