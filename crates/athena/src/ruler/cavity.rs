//! The store line's live reading (§7 of THE_CONSOLIDATION, #603): `read-cavity`, which scores every lap of the four-lane line
//! at its mean (`lane/line/chain7.sh`). Moved from the store's commands (`crate::store`) by C6.

use crate::exterior::*;
use crate::store::{open_slice, refuse_variables, role_names, store_counts};
use holonics_engine::codec::Codec;
use holonics_engine::field::{Learner, Realization, PassSlice, StorePass, NEAR};
use holonics_engine::passage::{Cut, Kind};
use holonics_engine::region::{views_of, OwnedRegion};
use std::path::Path;

/// One stretch of a slice as the store's cut draws it for a read: its region, its bytes, whether it ends a piece, and its kind.
pub(crate) struct HeldStretch {
    pub(crate) region: OwnedRegion,
    pub(crate) bytes: Vec<u8>,
    pub(crate) ends: bool,
    pub(crate) kind: Kind,
}

/// A slice of `role` cut afresh from stretch 1 with the key file's seed, whole stretches until at least `places` places (the cut every
/// reading of the line's held places shares: [`read_cavity`] and the loudness ruler).
#[allow(clippy::too_many_arguments, reason = "the cut's declared inputs, each a pinned file's reading or the pass's law")]
pub(crate) fn held_stretches(store: &Path, role: &str, name: &str, counts: &std::collections::HashMap<(String, String), (u64, u128)>, store_sha: &str, seed: u64, law: &StorePass, codec: &Codec, places: usize) -> Result<Vec<HeldStretch>> {
    let slice = open_slice(store, role, name, counts)?;
    let pass = StorePass { role: role.to_string(), store: store_sha.to_string(), stretches: 0, least: law.least, octaves: law.octaves, pairs: law.pairs, sites: law.sites, own: false, slices: vec![PassSlice { name: name.to_string(), piece: 0, cursor: 0, taken: 0 }], world: None };
    let mut cut = Cut { seed, slices: vec![slice], pass };
    let mut out = Vec::new();
    let mut taken = 0usize;
    while taken < places {
        let Some(drawn) = cut.next() else { break };
        let at = cut.pass.slices[drawn.slice].clone();
        let bytes = cut.slices[drawn.slice].bytes(at.piece as usize, at.cursor, drawn.q + drawn.a)?;
        let ends = drawn.ends;
        let stretch = cut.take(drawn, codec)?;
        taken += stretch.region.classes.len();
        out.push(HeldStretch { region: stretch.region, bytes, ends, kind: stretch.kind });
    }
    Ok(out)
}

/// [measurement; theory, November 13, P55 part B; the design record of November 13, §4.4] `read-cavity UNITS UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA
/// CODEC CODEC_SHA PLACES STATE STATE_SHA OUT [ROLE]`: **a held place's news at its cavity opening**, a reading (with `ROLE` = `prefix`, the
/// same reading on the documents the line trains on, G187). Each slice of the held role, alone and in the
/// store's order, is cut afresh from stretch 1 with the key file's seed (as `read-store`, retired by C6 of #603, cut it), whole stretches until at least `PLACES` places.
/// For each place `t` of a stretch: the stretch as a region with every place written but `t`; `c0`, the face at the built opening with no tick
/// ([`holonics_engine::field::Constitution::opening_face`], on the host) at `t`'s written class; `cK`, the face after the declared ticks by the
/// realization's read (`read_faces`, the regions batched under the pass's two bounds) at the same class. On the code slice each stretch is also
/// read with the leading spaces of each line that begins inside it doubled (the copy cut at the stretch's bound of 1,022 places), `c0` at every
/// place of the copy. Codes are on `2^(−20)` bits. One line a place to `OUT/cavity.tsv` (numbers only); a line a slice with the devices' times.
///
/// [measurement; theory, November 13, P57 item 2 (G132)] With the faces, the realization reads each open place's chart `r̂` (64 words on
/// `2^(−16)`) at the opening, after ticks 1, 2 and 3 (each tick's opening) and after the last tick ([`Realization::read_tick_charts`]); the
/// trained readout's code at each stage, `c0` to `c3` and `cK`, is the face of that chart at the written class (`c0` checked against the host's
/// opening face, `cK` against the realization's face). The charts go to `OUT/words.bin` (the place rows' order, five stages of 64 little-endian
/// 32-bit words a place). The same is read at the open places of each slice's whole masks, as `read-store` cut them (rows `W`,
/// `OUT/words_whole.bin`). The output directory is private: it holds no text, but it is the held passage's places.
pub fn read_cavity(args: &[String], realization: &mut dyn Realization) -> Result<()> {
    // [measurement; the lead, November 16 23:10Z] A last word `carry=MILLI` reads the held passage with every open row carrying its lock along
    // the ticks ([`holonics_engine::field::Constitution::lock_carry`]): a ruler's forward on the host's realization, before the stage is a law.
    let (args, carry) = match args.last().and_then(|w| w.strip_prefix("carry=")) {
        Some(m) => (&args[..args.len() - 1], Some(crate::ruler::tension::carry_of(m)?)),
        None => (args, None),
    };
    if args.len() != 13 && args.len() != 14 {
        return Err("read-cavity UNITS UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA CODEC CODEC_SHA PLACES STATE STATE_SHA OUT [ROLE]".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("read-cavity")?;
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
    let mut learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[10], &args[11], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    learner.field.lock_carry = carry;
    let law = learner.pass.clone().ok_or("a state with no pass line: read-cavity reads a state of the store's line")?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    let out = Path::new(&args[12]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    std::fs::create_dir_all(out)?;
    let mut tsv = std::io::BufWriter::new(std::fs::File::create(out.join("cavity.tsv"))?);
    use std::io::Write as _;
    writeln!(tsv, "row\tslice\tstretch\tt\tclass\tc0\tcK\tsource\tc1\tc2\tc3\tcO")?;
    let mut words = std::io::BufWriter::new(std::fs::File::create(out.join("words.bin"))?);
    let mut words_whole = std::io::BufWriter::new(std::fs::File::create(out.join("words_whole.bin"))?);
    let dw = learner.field.declaration.width;
    let stages_expected = learner.field.declaration.ticks + 1;
    // [P60 item 7] The opening's code through its lift at every place of a region (cavity openings only, no tick), where the field has the lift;
    // `-` where it has not. At a written place it is the place's code with it alone open among the others (the cavity opening is the opening of
    // the region masked there, §4.4a's check), so one region of every place written gives the one-place masks' codes.
    let opened = learner.field.declaration.opening;
    let opening_of = |classes: &[usize], unresolved: &[bool]| -> std::result::Result<Vec<Option<i64>>, String> {
        if !opened {
            return Ok(vec![None; classes.len()]);
        }
        let region = [OwnedRegion::plain(classes.to_vec(), unresolved.to_vec())];
        let views = views_of(&region);
        learner.field.opening_codes(&views[0]).map_err(|e| e.to_string())
    };
    let cell = |v: Option<i64>| v.map_or("-".to_string(), |c| c.to_string());
    // [Brandon, November 15 02:06Z] A face that reads its sites' loudness is read from a chart and its lanes' powers at the same stage
    // (`face_of_chart`); the powers are read beside the charts only on such a field, so a field without it reads as before.
    let loud = learner.field.declaration.loud;
    let lanes = learner.field.declaration.lanes;
    let code_of_read = |r: &[i32], s: &[i128], class: usize| -> std::result::Result<i64, String> { Ok(learner.field.face_of_chart(r, s).map_err(|e| e.to_string())?.code(class)) };
    let powers = |realization: &mut dyn Realization, regions: &[OwnedRegion]| -> std::result::Result<Vec<Vec<Vec<i128>>>, String> {
        if loud { Ok(realization.read_tick_scales(&learner.field, &views_of(regions)).map_err(|e| e.to_string())?.1) } else { Ok(vec![Vec::new(); regions.len()]) }
    };
    let put_words = |w: &mut std::io::BufWriter<std::fs::File>, rows: &[Vec<i32>], at: usize| -> std::io::Result<()> {
        for stage in rows {
            for &v in &stage[at * dw..(at + 1) * dw] {
                w.write_all(&v.to_le_bytes())?;
            }
        }
        Ok(())
    };
    // [measurement; G187] The role read: the held documents by default (the line's reads, every line kept), or `prefix`, the documents the line
    // trains on, cut and read the same way, so the codes on text the field has met stand beside the codes on text it has not.
    let role = match args.get(13).map(String::as_str) {
        None | Some("held") => "held",
        Some("prefix") => "prefix",
        Some(other) => return Err(format!("read-cavity reads the held or the prefix role, not {other}").into()),
    };
    let names = role_names(&counts, role);
    println!("CAVITY_LAW role={role} places={places} least={} octaves={} pairs_bound={} sites_bound={} ticks={} alphabet={} ms={}", law.least, law.octaves, law.pairs, law.sites, learner.field.declaration.ticks, codec.alphabet(), started.elapsed().as_millis());
    const COPY_BOUND: usize = 1022;
    for &name in &names {
        let cut = held_stretches(store, role, name, &counts, &args[4], seed, &law, &codec, places as usize)?;
        let taken: usize = cut.iter().map(|s| s.region.classes.len()).sum();
        let mut stretches: Vec<(Vec<usize>, Vec<u8>, bool)> = Vec::new();
        let mut wholes: Vec<(usize, OwnedRegion)> = Vec::new();
        for s in cut {
            if s.kind == Kind::MaskWhole {
                wholes.push((stretches.len(), s.region.clone()));
            }
            stretches.push((s.region.classes, s.bytes, s.ends));
        }
        // c0 on the host, a region a place; the first stretch's places checked against the whole opening.
        // [the ring record §4] On a field that reads twice the opening a place's chart begins from is the second read's, marked by the first
        // read's face, so c0 is read from the realization's chart at that opening (its parity with the host's charts is on record, the card's
        // `the_field_that_reads_twice_on_the_card_reads_the_hosts_bits`), and the host reads no opening of its own.
        let marked = learner.field.declaration.mark;
        let host_start = std::time::Instant::now();
        let mut c0: Vec<Vec<i64>> = Vec::with_capacity(stretches.len());
        // (the places of a stretch read on the host's threads: a reading, each place's region its own)
        use rayon::prelude::*;
        for (k, (classes, _, _)) in stretches.iter().enumerate().filter(|_| !marked) {
            let codes: Vec<std::result::Result<i64, String>> = (0..classes.len())
                .into_par_iter()
                .map(|t| {
                    let mut mask = vec![false; classes.len()];
                    mask[t] = true;
                    let region = [OwnedRegion::plain(classes.clone(), mask)];
                    let views = views_of(&region);
                    let face = learner.field.opening_face(&views[0], t).map_err(|e| e.to_string())?;
                    if k == 0 {
                        let whole = learner.field.opening_face_whole(&views[0], t).map_err(|e| e.to_string())?;
                        if whole.code(classes[t]) != face.code(classes[t]) {
                            return Err(format!("the opening's face at a place differs from the whole opening's (stretch 1, place {t})"));
                        }
                    }
                    Ok(face.code(classes[t]))
                })
                .collect();
            c0.push(codes.into_iter().collect::<std::result::Result<Vec<i64>, String>>()?);
        }
        let host_ms = host_start.elapsed().as_millis();
        // cK on the realization, the regions batched under the pass's two bounds.
        let card_start = std::time::Instant::now();
        let mut ck: Vec<Vec<i64>> = stretches.iter().map(|(c, _, _)| vec![0i64; c.len()]).collect();
        // [P57 item 2] Each place's charts by stage (its one open row at each stage) and the trained readout's codes c1 to c3.
        let mut charts: Vec<Vec<Vec<Vec<i32>>>> = stretches.iter().map(|(c, _, _)| vec![Vec::new(); c.len()]).collect();
        let mut mid: Vec<Vec<[i64; 3]>> = stretches.iter().map(|(c, _, _)| vec![[0i64; 3]; c.len()]).collect();
        let mut opening_powers: Vec<Vec<Vec<i128>>> = stretches.iter().map(|(c, _, _)| vec![Vec::new(); c.len()]).collect();
        let jobs: Vec<(usize, usize)> = stretches.iter().enumerate().flat_map(|(k, (c, _, _))| (0..c.len()).map(move |t| (k, t))).collect();
        let mut at = 0usize;
        let mut batches = 0usize;
        while at < jobs.len() {
            let (mut in_pairs, mut in_sites, mut end) = (0u64, 0u64, at);
            while end < jobs.len() {
                let s = stretches[jobs[end].0].0.len() as u64;
                if in_sites > 0 && (in_pairs + s * s > law.pairs || in_sites + s > law.sites) {
                    break;
                }
                (in_pairs, in_sites, end) = (in_pairs + s * s, in_sites + s, end + 1);
            }
            let regions: Vec<OwnedRegion> = jobs[at..end]
                .iter()
                .map(|&(k, t)| {
                    let classes = &stretches[k].0;
                    let mut mask = vec![false; classes.len()];
                    mask[t] = true;
                    OwnedRegion::plain(classes.clone(), mask)
                })
                .collect();
            let (faces, stages) = realization.read_tick_charts(&learner.field, &views_of(&regions)).map_err(|e| e.to_string())?;
            let scales = powers(&mut *realization, &regions)?;
            for (((&(k, t), f), st), sc) in jobs[at..end].iter().zip(&faces).zip(stages).zip(scales) {
                let sc_at = |s: usize| -> &[i128] { sc.get(s).map_or(&[][..], |v| &v[..lanes.min(v.len())]) };
                let class = stretches[k].0[t];
                ck[k][t] = f[t].as_ref().ok_or("an open place without a face")?.code(class);
                if st.len() != stages_expected || st.iter().any(|s| s.len() != dw) {
                    return Err("a place's charts by stage that are not one row of each stage".into());
                }
                if code_of_read(&st[stages_expected - 1], sc_at(stages_expected - 1), class)? != ck[k][t] {
                    return Err(format!("the face of the last chart differs from the realization's face (stretch {k}, place {t})").into());
                }
                mid[k][t] = [code_of_read(&st[1], sc_at(1), class)?, code_of_read(&st[2], sc_at(2), class)?, code_of_read(&st[3], sc_at(3), class)?];
                opening_powers[k][t] = sc_at(0).to_vec();
                charts[k][t] = st;
            }
            batches += 1;
            at = end;
        }
        let card_ms = card_start.elapsed().as_millis();
        if marked {
            for (k, (classes, _, _)) in stretches.iter().enumerate() {
                c0.push((0..classes.len()).map(|t| code_of_read(&charts[k][t][0], &opening_powers[k][t], classes[t])).collect::<std::result::Result<Vec<i64>, _>>()?);
            }
        }
        let opening_start = std::time::Instant::now();
        let co: Vec<Vec<Option<i64>>> = stretches.par_iter().map(|(classes, _, _)| opening_of(classes, &vec![false; classes.len()])).collect::<std::result::Result<_, String>>()?;
        let opening_ms = opening_start.elapsed().as_millis();
        for (k, (classes, _, _)) in stretches.iter().enumerate() {
            for t in 0..classes.len() {
                if code_of_read(&charts[k][t][0], &opening_powers[k][t], classes[t])? != c0[k][t] {
                    return Err(format!("the face of the opening's chart differs from the host's opening face (stretch {k}, place {t})").into());
                }
                let [c1, c2, c3] = mid[k][t];
                writeln!(tsv, "P\t{name}\t{k}\t{t}\t{}\t{}\t{}\t-\t{c1}\t{c2}\t{c3}\t{}", classes[t], c0[k][t], ck[k][t], cell(co[k][t]))?;
                put_words(&mut words, &charts[k][t], 0)?;
            }
        }
        // [P57 item 2] The slice's whole masks as the cut gives them, their open places' charts by stage and codes.
        let whole_start = std::time::Instant::now();
        let mut whole_places = 0usize;
        let mut w_at = 0usize;
        while w_at < wholes.len() {
            let (mut in_pairs, mut in_sites, mut end) = (0u64, 0u64, w_at);
            while end < wholes.len() {
                let s = wholes[end].1.classes.len() as u64;
                if in_sites > 0 && (in_pairs + s * s > law.pairs || in_sites + s > law.sites) {
                    break;
                }
                (in_pairs, in_sites, end) = (in_pairs + s * s, in_sites + s, end + 1);
            }
            let regions: Vec<OwnedRegion> = wholes[w_at..end].iter().map(|(_, r)| r.clone()).collect();
            let (faces, stages) = realization.read_tick_charts(&learner.field, &views_of(&regions)).map_err(|e| e.to_string())?;
            let scales = powers(&mut *realization, &regions)?;
            for (((k, region), (f, st)), sc) in wholes[w_at..end].iter().zip(faces.iter().zip(&stages)).zip(&scales) {
                let wo = opening_of(&region.classes, &region.unresolved)?;
                if st.len() != stages_expected {
                    return Err("a whole mask's charts by stage that are not one of each stage".into());
                }
                for (row, t) in (0..region.classes.len()).filter(|&t| region.unresolved[t]).enumerate() {
                    let class = region.classes[t];
                    let cw = f[t].as_ref().ok_or("an open place without a face")?.code(class);
                    let at_row = |s: usize| &st[s][row * dw..(row + 1) * dw];
                    let sc_row = |s: usize| -> &[i128] { sc.get(s).map_or(&[][..], |v| &v[row * lanes..(row + 1) * lanes]) };
                    if code_of_read(at_row(stages_expected - 1), sc_row(stages_expected - 1), class)? != cw {
                        return Err(format!("a whole mask's last chart's face differs from the realization's face (stretch {k}, place {t})").into());
                    }
                    let (w0, w1, w2, w3) = (code_of_read(at_row(0), sc_row(0), class)?, code_of_read(at_row(1), sc_row(1), class)?, code_of_read(at_row(2), sc_row(2), class)?, code_of_read(at_row(3), sc_row(3), class)?);
                    writeln!(tsv, "W\t{name}\t{k}\t{t}\t{class}\t{w0}\t{cw}\t-\t{w1}\t{w2}\t{w3}\t{}", cell(wo[t]))?;
                    put_words(&mut words_whole, st, row)?;
                    whole_places += 1;
                }
            }
            w_at = end;
        }
        let whole_ms = whole_start.elapsed().as_millis();
        // The code slice's copies: each line's leading spaces doubled, c0 on the host at every place of the copy.
        let mut copy_places = 0usize;
        let copy_start = std::time::Instant::now();
        if name == "code" {
            for (k, (_, bytes, ends)) in stretches.iter().enumerate() {
                let (mut copy, mut source) = (Vec::with_capacity(2 * bytes.len()), Vec::with_capacity(2 * bytes.len()));
                let mut leading = false;
                for (t, &b) in bytes.iter().enumerate() {
                    if b == b'\n' {
                        leading = true;
                    } else if b != b' ' {
                        leading = false;
                    }
                    copy.push(b);
                    source.push(t);
                    if leading && b == b' ' {
                        copy.push(b);
                        source.push(t);
                    }
                }
                let mut classes = codec.encode(&copy)?;
                if *ends {
                    let first_void = bytes.len();
                    classes.resize(classes.len() + NEAR, codec.void());
                    source.extend((0..NEAR).map(|v| first_void + v));
                }
                classes.truncate(COPY_BOUND);
                source.truncate(COPY_BOUND);
                let codes: Vec<std::result::Result<i64, String>> = (0..classes.len())
                    .into_par_iter()
                    .map(|t| {
                        let mut mask = vec![false; classes.len()];
                        mask[t] = true;
                        let region = [OwnedRegion::plain(classes.clone(), mask)];
                        let views = views_of(&region);
                        Ok(learner.field.opening_face(&views[0], t).map_err(|e| e.to_string())?.code(classes[t]))
                    })
                    .collect();
                let cc = opening_of(&classes, &vec![false; classes.len()])?;
                for (t, code) in codes.into_iter().enumerate() {
                    writeln!(tsv, "C\t{name}\t{k}\t{t}\t{}\t{}\t-\t{}\t-\t-\t-\t{}", classes[t], code?, source[t], cell(cc[t]))?;
                }
                copy_places += classes.len();
            }
        }
        // [P60 item 7c] Each stretch begun seven places later (its bytes from the eighth on, a true end's voids kept), the opening's code at every
        // place of the copy, `source` the place of the stretch it stands at; where the field has the lift.
        let mut later_places = 0usize;
        if opened {
            const LATER: usize = 7;
            let later: Vec<(usize, Vec<usize>, Vec<Option<i64>>)> = stretches
                .par_iter()
                .enumerate()
                .filter(|(_, (_, bytes, _))| bytes.len() > LATER)
                .map(|(k, (_, bytes, ends))| -> std::result::Result<_, String> {
                    let mut classes = codec.encode(&bytes[LATER..]).map_err(|e| e.to_string())?;
                    if *ends {
                        classes.resize(classes.len() + NEAR, codec.void());
                    }
                    let codes = opening_of(&classes, &vec![false; classes.len()])?;
                    Ok((k, classes, codes))
                })
                .collect::<std::result::Result<_, String>>()?;
            for (k, classes, codes) in later {
                for (t, (class, code)) in classes.iter().zip(codes).enumerate() {
                    writeln!(tsv, "S\t{name}\t{k}\t{t}\t{class}\t-\t-\t{}\t-\t-\t-\t{}", t + LATER, cell(code))?;
                }
                later_places += classes.len();
            }
        }
        println!(
            "CAVITY_SLICE slice={name} stretches={} places={taken} host_c0_ms={host_ms} card_cK_ms={card_ms} card_batches={batches} host_opening_ms={opening_ms} whole_masks={} whole_places={whole_places} whole_ms={} copy_places={copy_places} later_places={later_places} host_copy_ms={} elapsed_ms={}",
            stretches.len(),
            wholes.len(),
            whole_ms,
            copy_start.elapsed().as_millis(),
            started.elapsed().as_millis()
        );
    }
    tsv.flush()?;
    words.flush()?;
    words_whole.flush()?;
    println!("CAVITY_DONE ms={}", started.elapsed().as_millis());
    Ok(())
}
