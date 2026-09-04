//! M5: one authenticated physical fold returns as an exact constraint complex.

#[path = "m5/artifact.rs"]
mod artifact;
#[path = "m5/cif.rs"]
mod cif;
#[path = "m5/fold.rs"]
mod fold;
#[path = "m5/input.rs"]
mod input;
#[path = "m5/npy.rs"]
mod npy;
#[path = "m5/visual.rs"]
mod visual;

fn run() -> Result<(), String> {
    if std::env::args().nth(1).as_deref() == Some("--refresh-visual") {
        let root = artifact::refresh_visual()?;
        println!("M5 refreshed the vector/mesh apparatus face from {root}");
        return Ok(());
    }
    let returned = fold::enact()?;
    let artifacts = artifact::emit(&returned)?;
    println!(
        "M5 enacted {} on {}: contacts={}, shared={}, separator={:?}; grade={}, artifacts={}",
        returned.source_mount.family.full_name,
        returned.device_receipt.device,
        returned.device_receipt.contact_population,
        returned.cross_presentation_fibre.shared_inside.len(),
        returned.cross_presentation_fibre.shortest_separator,
        artifacts.grade.score,
        artifacts.root,
    );
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("M5 refused: {error}");
        std::process::exit(1);
    }
}
