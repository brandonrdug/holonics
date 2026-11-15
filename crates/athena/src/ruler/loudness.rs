//! [measurement; Brandon, November 15 00:58Z; the record of November 13, "A medium's two stores set its clock and its impedance … loudness
//! over surprise is a temperature …", §4 and its test 1] **`read-loudness`, loudness beside surprise**: each held place's lane powers beside
//! its code, the reading that tells how many nats a place costs from what they cost and whether a quiet place was thinned, stretched or
//! absorbed (§4.2). A ruler of the line: it reads a state on the card and changes nothing.

use crate::exterior::*;
use crate::ruler::cavity::held_stretches;
use crate::store::{refuse_variables, role_names, store_counts};
use holonics_engine::codec::Codec;
use holonics_engine::field::{Learner, Realization};
use holonics_engine::field::TowerFace;
use holonics_engine::passage::Kind;
use holonics_engine::region::{views_of, OwnedRegion};
use std::path::Path;

/// The rank of `class` in `face`: one more than the classes whose mass stands above its own (1 is the face's loudest class).
fn rank_of(face: &TowerFace, class: usize) -> usize {
    let m = face.masses[class];
    1 + face.masses.iter().filter(|&&v| v > m).count()
}

/// `read-loudness UNITS UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA CODEC CODEC_SHA PLACES STATE STATE_SHA OUT [ROLE]`: the held places of
/// [`crate::ruler::cavity::read_cavity`], cut the same way (each slice afresh from stretch 1 with the key file's seed, whole stretches until
/// at least `PLACES` places), each place `t` read as the stretch with every place written but `t` (rows `P`), and each slice's whole masks as
/// the cut gives them (rows `W`). For each open place: its code at its written class on `2^(−20)` bits (the face after the declared ticks, by
/// the realization), the rank of that class in its face, its unit and its written neighbours' (two before, one after, as hex of their bytes,
/// so a ruler can read a place inside its recurring pieces: Brandon's lens of November 15 01:08Z, a piece such as `th` or `sty` being a
/// geometric part whose stability a place's surprise and loudness show), and its lanes' powers `‖r_ℓ‖_rms` at every stage (each tick's opening, then after the
/// last tick, the stage the faces read; [`Realization::read_tick_scales`]), on the state's grain. One line a place to `OUT/loudness.tsv`
/// (numbers only; `tools/loudness_table.py` reads it by region and rank); a line a slice with the card's time. The output directory is private:
/// it holds no text, but it is the held passage's places.
pub fn read_loudness(args: &[String], realization: &mut dyn Realization) -> Result<()> {
    if args.len() != 13 && args.len() != 14 {
        return Err("read-loudness UNITS UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA CODEC CODEC_SHA PLACES STATE STATE_SHA OUT [ROLE]".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("read-loudness")?;
    let units = units_of(&args[1], &args[2])?;
    if !units.merges().is_empty() {
        return Err("the store's cut is on bytes: a units file of merges is refused".into());
    }
    let store = Path::new(&args[3]);
    let counts = store_counts(std::str::from_utf8(&pinned_read(&store.join("STORE.tsv").to_string_lossy(), &args[4], READ_BUDGET as usize)?)?)?;
    let keys = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?, units)?;
    let places = positive(&args[9])?;
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[10], &args[11], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let law = learner.pass.clone().ok_or("a state with no pass line: read-loudness reads a state of the store's line")?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    let out = Path::new(&args[12]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let role = match args.get(13).map(String::as_str) {
        None | Some("held") => "held",
        Some("prefix") => "prefix",
        Some(other) => return Err(format!("read-loudness reads the held or the prefix role, not {other}").into()),
    };
    std::fs::create_dir_all(out)?;
    let (lanes, stages) = (learner.field.declaration.lanes, learner.field.declaration.ticks + 1);
    let mut tsv = std::io::BufWriter::new(std::fs::File::create(out.join("loudness.tsv"))?);
    use std::io::Write as _;
    let power_cols: Vec<String> = (0..stages).flat_map(|s| (0..lanes).map(move |l| format!("s{s}_l{l}"))).collect();
    writeln!(tsv, "row\tslice\tstretch\tt\tclass\tcode\trank\tprev2\tprev\tunit\tnext\t{}", power_cols.join("\t"))?;
    println!("LOUDNESS_LAW role={role} places={places} lanes={lanes} stages={stages} ticks={} alphabet={} ms={}", learner.field.declaration.ticks, codec.alphabet(), started.elapsed().as_millis());
    // One batch of regions on the realization under the pass's two bounds, each region's open places written out.
    let mut read_rows = |row: &str, name: &str, jobs: &[(usize, OwnedRegion)], tsv: &mut std::io::BufWriter<std::fs::File>| -> Result<(usize, usize)> {
        let (mut at, mut batches, mut placed) = (0usize, 0usize, 0usize);
        while at < jobs.len() {
            let (mut in_pairs, mut in_sites, mut end) = (0u64, 0u64, at);
            while end < jobs.len() {
                let s = jobs[end].1.classes.len() as u64;
                if in_sites > 0 && (in_pairs + s * s > law.pairs || in_sites + s > law.sites) {
                    break;
                }
                (in_pairs, in_sites, end) = (in_pairs + s * s, in_sites + s, end + 1);
            }
            let regions: Vec<OwnedRegion> = jobs[at..end].iter().map(|(_, r)| r.clone()).collect();
            let (faces, scales) = realization.read_tick_scales(&learner.field, &views_of(&regions)).map_err(|e| e.to_string())?;
            for (((k, region), f), st) in jobs[at..end].iter().zip(&faces).zip(&scales) {
                if st.len() != stages {
                    return Err("a region's lane powers by stage that are not one of each stage".into());
                }
                for (open, t) in (0..region.classes.len()).filter(|&t| region.unresolved[t]).enumerate() {
                    let class = region.classes[t];
                    let face = f[t].as_ref().ok_or("an open place without a face")?;
                    let powers: Vec<String> = st.iter().flat_map(|s| s[open * lanes..(open + 1) * lanes].iter().map(i128::to_string)).collect();
                    let unit = |at: Option<usize>| at.and_then(|i| region.classes.get(i)).map_or("-".to_string(), |&c| codec.decode(&[c]).iter().map(|b| format!("{b:02x}")).collect());
                    let (p2, p1, nx) = (unit(t.checked_sub(2)), unit(t.checked_sub(1)), unit(Some(t + 1)));
                    writeln!(tsv, "{row}\t{name}\t{k}\t{t}\t{class}\t{}\t{}\t{p2}\t{p1}\t{}\t{nx}\t{}", face.code(class), rank_of(face, class), unit(Some(t)), powers.join("\t"))?;
                    placed += 1;
                }
            }
            batches += 1;
            at = end;
        }
        Ok((batches, placed))
    };
    for &name in &role_names(&counts, role) {
        let card_start = std::time::Instant::now();
        let cut = held_stretches(store, role, name, &counts, &args[4], seed, &law, &codec, places)?;
        let mut one: Vec<(usize, OwnedRegion)> = Vec::new();
        let mut wholes: Vec<(usize, OwnedRegion)> = Vec::new();
        for (k, s) in cut.iter().enumerate() {
            for t in 0..s.region.classes.len() {
                let mut mask = vec![false; s.region.classes.len()];
                mask[t] = true;
                one.push((k, OwnedRegion::plain(s.region.classes.clone(), mask)));
            }
            if s.kind == Kind::MaskWhole {
                wholes.push((k, s.region.clone()));
            }
        }
        let (batches, placed) = read_rows("P", name, &one, &mut tsv)?;
        let (w_batches, w_placed) = read_rows("W", name, &wholes, &mut tsv)?;
        println!("LOUDNESS_SLICE slice={name} stretches={} places={placed} batches={batches} whole_masks={} whole_places={w_placed} whole_batches={w_batches} card_ms={}", cut.len(), wholes.len(), card_start.elapsed().as_millis());
    }
    tsv.flush()?;
    println!("LOUDNESS_DONE ms={}", started.elapsed().as_millis());
    Ok(())
}
