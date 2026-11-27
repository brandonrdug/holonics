//! [measurement; the lead, November 16 21:40Z; atlas `contact.effective-tension`, `contact.pool-founding`] **`read-tension`, the tension at the
//! strand's return**: what the present faces cannot bridge at a place, written out so that a ruler on the host can read it against a pool of
//! products of the place's own faces.
//!
//! Why: the crossing triad entered the line at lap 75 with drawn legs and its return at zero, and after a lap the digits of a held sum coded
//! as before, with the return zeroed or not (`receipts/2026-11-16_worldcross/`). With `W_T = 0` the legs' covectors vanish, and a law that
//! lives wholly in a product is read by no pair term (`code.triad-character-of-composition`), so drawn legs meet it only by a walk. The
//! founding law of October 24 reads the remainder against a pool instead (`contact.pool-founding`): the best face is the reduced-rank regression
//! of the covector on the pool. The engine had no reading of that covector beside the pool's operands. This is it.
//!
//! A reading on the host's threads (it opens no card): the state is read, never written. A ruler: it names places by a table's layout,
//! outside the machine.

use crate::exterior::*;
use crate::store::{open_slice, refuse_variables, role_names, store_counts};
use holonics_engine::codec::Codec;
use holonics_engine::field::Learner;
use holonics_engine::passage::{Cut, Stretch};
use holonics_engine::region::{view_of, OwnedRegion};
use rayon::prelude::*;
use std::io::Write;
use std::path::Path;

/// `read-tension UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA FORMS FORMS_SHA STATE STATE_SHA OUT`. `FORMS` is a table of rows
/// `label<TAB>prompt<TAB>run[<TAB>places]` (a line feed written `\n`; `read-forms`' table with one field more): each named place of the run
/// (a comma list of indices into the run; every place where the field is absent) is opened alone with the rest of the record known, the
/// one-place receiver, and the region's forward and reverse are read ([`holonics_engine::field::Constitution::crossing_tension`]). For each
/// such place and each tick, `OUT` takes one row: in `rows.tsv` its `label`, `place`, `tick` and the place's code on `2^(−20)` bits, and in
/// `lambda.i64`, `read.i32`, `current.i64` and `products.i64` (little-endian, row after row) the covector the tick's reverse receives at the
/// place (`D` entries on `2^(−24)`), the pair chart `r̂′` there (`D` on `2^(−16)`), the current the tick gathered there (`2M` on `2^(−16)`) and
/// the triads' products there (`2J` on `2^(−16)`). `dims.tsv` names the four widths.
pub fn read_tension(args: &[String]) -> Result<()> {
    // [measurement; the lead, November 16 22:30Z] With `all`, every site of each region is written at every tick (`rows.tsv` then gives the
    // row's `site` and whether it is the open one), with the tick's opening chart beside the pair chart (`chart.i32`, what the tick's keys,
    // probes and values read) and, in `shares.tsv`, the open place's row by tick and head: each source site and its share of the row's
    // weight in millionths. A ruler traces a far symbol's way to the open place link by link from them.
    // [measurement; the lead, November 16 23:00Z] With `carry=MILLI`, every open row carries its lock along the ticks at `γ = MILLI/1000`
    // ([`holonics_engine::field::Constitution::lock_carry`]): a ruler's forward, read before the stage is a law.
    // [measurement; the lead, November 17 10:25Z] With `shares`, `shares.tsv` alone of `all`'s files is written (the open place's row by tick
    // and head), for a ruler that closes a menu of the rows on longer regions without every site's charts on disk.
    let usage = "read-tension UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA FORMS FORMS_SHA STATE STATE_SHA OUT [all] [shares] [mixed] [carry=MILLI]";
    if args.len() < 12 || args.len() > 16 {
        return Err(usage.into());
    }
    let (mut all, mut carry, mut shares_alone) = (false, None, false);
    // [measurement; the lead, November 17] With `mixed`, each named place is opened with a keyed half of its run's other places open beside it
    // (a place joins where [`keyed_bit`] of `label:place:other` is odd), so a place is read as a release meets it, some of
    // its run written and some not; `all` then writes every open site of the region as an open row.
    let mut mixed = false;
    for word in &args[12..] {
        match (word.as_str(), word.strip_prefix("carry=")) {
            ("all", _) => all = true,
            ("mixed", _) => mixed = true,
            ("shares", _) => shares_alone = true,
            (_, Some(m)) => carry = Some(crate::ruler::tension::carry_of(m)?),
            _ => return Err(usage.into()),
        }
    }
    let started = std::time::Instant::now();
    refuse_variables("read-tension")?;
    let units = units_of(&args[1], &args[2])?;
    let _keys = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?, units)?;
    let table = String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?;
    let mut learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[9], &args[10], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    learner.field.lock_carry = carry;
    let out = Path::new(&args[11]);
    let unescape = |t: &str| t.replace("\\n", "\n");
    // (label, the place's index in its run, the place's site, the region)
    let mut work: Vec<(String, usize, usize, OwnedRegion)> = Vec::new();
    for line in table.lines() {
        let w: Vec<&str> = line.split('\t').collect();
        let (label, prompt, run, places) = match w[..] {
            [label, prompt, run] => (label, prompt, run, None),
            [label, prompt, run, places] => (label, prompt, run, Some(places)),
            _ => return Err("a tension row that is not three or four fields".into()),
        };
        let (p, r) = (codec.encode(unescape(prompt).as_bytes())?, codec.encode(unescape(run).as_bytes())?);
        if p.is_empty() || r.is_empty() {
            return Err("a tension row with an empty prompt or run".into());
        }
        let places: Vec<usize> = match places {
            None => (0..r.len()).collect(),
            Some(text) => text.split(',').map(|s| s.parse::<usize>().map_err(|_| "a place that is not an index")).collect::<std::result::Result<_, _>>()?,
        };
        let mut classes = p.clone();
        classes.extend_from_slice(&r);
        for j in places {
            if j >= r.len() {
                return Err("a place past its run".into());
            }
            let mut open = vec![false; classes.len()];
            open[p.len() + j] = true;
            if mixed {
                for other in (0..r.len()).filter(|&o| o != j) {
                    open[p.len() + other] = keyed_bit(&format!("{label}:{j}:{other}")) & 1 == 1;
                }
            }
            work.push((label.to_string(), j, p.len() + j, OwnedRegion::plain(classes.clone(), open)));
        }
    }
    if work.is_empty() {
        return Err("a tension table of no places".into());
    }
    let d = learner.field.declaration;
    let (dw, m2, j2, c2, ticks) = (d.width, 2 * d.heads * d.modes, 2 * d.triads, 2 * d.carry, d.ticks);
    std::fs::create_dir(out)?;
    write_new(&out.join("dims.tsv"), format!("lambda\t{dw}\nread\t{dw}\ncurrent\t{m2}\nproducts\t{j2}\nticks\t{ticks}\ncharge\t{c2}\n").as_bytes())?;
    println!("TENSION_LAW places={} ticks={ticks} width={dw} current={m2} products={j2} circles={} carry={} threads={} ms={}", work.len(), d.carry, carry.map_or("-".to_string(), |g| g.to_string()), rayon::current_num_threads(), started.elapsed().as_millis());
    // The locks' temperatures as the state holds them: `log₂ T` on the material's grain, one a head and receiver kind (a class receiver, a listener).
    let temper = learner.field.layout().temper;
    println!("TENSION_TEMPER log2_on_2^-24 {}", (0..2 * d.heads).map(|k| learner.field.theta[temper + k].to_string()).collect::<Vec<_>>().join(" "));
    let create = |name: &str| -> Result<std::io::BufWriter<std::fs::File>> { Ok(std::io::BufWriter::new(std::fs::OpenOptions::new().write(true).create_new(true).open(out.join(name))?)) };
    let (mut rows, mut lambda, mut read, mut current, mut products) = (create("rows.tsv")?, create("lambda.i64")?, create("read.i32")?, create("current.i64")?, create("products.i64")?);
    // [the lead, November 17] With `shares` the named place's opening chart is written beside its row (`chart.i32`, what the site's leg reads).
    let (mut chart, mut shares) = (if all || shares_alone { Some(create("chart.i32")?) } else { None }, if all || shares_alone { Some(create("shares.tsv")?) } else { None });
    // With `all`, each site's value word beside its chart (`value.i64`, `2M` entries on `2^(−16)`): what the site offers a row that meets it.
    let mut value = if all { Some(create("value.i64")?) } else { None };
    // The open place's whole face, a record a place in the table's order (`faces.i64`, the code of each of the `A` classes on `2^(−20)` bits).
    let mut faces = create("faces.i64")?;
    // [measurement; the lead, November 17] Each row's carry circles (`charge.i64` and `gate.i64`, `2C` entries a row, the real parts then the
    // imaginary: the charge arriving at the site on `2^(−16)` and the site's gate on `2^(−30)`), for a ruler's read of a circle's phase by its
    // harmonics; `dims.tsv` names their width as `charge`.
    let (mut charge, mut gate) = (create("charge.i64")?, create("gate.i64")?);
    let mut written = 0usize;
    // Regions in blocks, so that what is held before it is written stays bounded; rows in the table's order.
    for block in work.chunks(1024) {
        let reads: Vec<std::result::Result<holonics_engine::field::CrossingTension, String>> =
            block.par_iter().map(|(_, _, _, region)| learner.field.crossing_tension(&view_of(region)).map_err(|e| e.to_string())).collect();
        for ((label, place, site, _), tension) in block.iter().zip(reads) {
            let tension = tension?;
            let code = tension.codes[*site].ok_or("an open place without a face")?;
            for &v in tension.faces[*site].as_ref().ok_or("an open place without a face")? {
                faces.write_all(&v.to_le_bytes())?;
            }
            let sites = if all { 0..tension.codes.len() } else { *site..*site + 1 };
            for k in 0..ticks {
                for s in sites.clone() {
                    if all {
                        writeln!(rows, "{label}\t{place}\t{k}\t{code}\t{s}\t{}", u8::from(s == *site))?;
                    } else {
                        writeln!(rows, "{label}\t{place}\t{k}\t{code}")?;
                    }
                    for &v in &tension.lambda[k][s * dw..(s + 1) * dw] {
                        lambda.write_all(&v.to_le_bytes())?;
                    }
                    for &v in &tension.read[k][s * dw..(s + 1) * dw] {
                        read.write_all(&v.to_le_bytes())?;
                    }
                    for &v in &tension.current[k][s * m2..(s + 1) * m2] {
                        current.write_all(&v.to_le_bytes())?;
                    }
                    if j2 > 0 {
                        for &v in &tension.products[k][s * j2..(s + 1) * j2] {
                            products.write_all(&v.to_le_bytes())?;
                        }
                    }
                    if let Some(c) = chart.as_mut() {
                        for &v in &tension.chart[k][s * dw..(s + 1) * dw] {
                            c.write_all(&v.to_le_bytes())?;
                        }
                    }
                    if let Some(c) = value.as_mut() {
                        for &v in &tension.value[k][s * m2..(s + 1) * m2] {
                            c.write_all(&v.to_le_bytes())?;
                        }
                    }
                    if c2 > 0 {
                        for &v in &tension.charge[k][s * c2..(s + 1) * c2] {
                            charge.write_all(&v.to_le_bytes())?;
                        }
                        for &v in &tension.gate[k][s * c2..(s + 1) * c2] {
                            gate.write_all(&v.to_le_bytes())?;
                        }
                    }
                    written += 1;
                }
                if let Some(f) = shares.as_mut() {
                    for (h, i, srcs) in tension.sources[k].iter().filter(|(_, i, _)| i == site) {
                        let line: Vec<String> = srcs.iter().map(|&(j, p, s)| format!("{j}:{}:{s}", (p * 1_000_000) >> holonics_engine::width::SHARE_BITS)).collect();
                        writeln!(f, "{label}\t{place}\t{k}\t{h}\t{i}\t{}", line.join(" "))?;
                    }
                }
            }
        }
        println!("TENSION_BLOCK rows={written} ms={}", started.elapsed().as_millis());
    }
    for w in [&mut rows, &mut lambda, &mut read, &mut current, &mut products, &mut faces, &mut charge, &mut gate] {
        w.flush()?;
    }
    if let Some(c) = chart.as_mut() {
        c.flush()?;
    }
    if let Some(c) = value.as_mut() {
        c.flush()?;
    }
    if let Some(f) = shares.as_mut() {
        f.flush()?;
    }
    println!("TENSION_DONE rows={written} places={} ms={}", work.len(), started.elapsed().as_millis());
    Ok(())
}

/// `read-tension-store UNITS UNITS_SHA STORE STORE_SHA ROLE KEYS KEYS_SHA CODEC CODEC_SHA SECTIONS STATE STATE_SHA OUT [EVERY]`: **the tension
/// over the sections a lap would meet next.** The store's `ROLE` is cut from the state's own pass as `train-store` cuts it (the same keyed
/// stretches and states, under the pass's two bounds; a world's acts are not posed: every stretch is read as the passage wrote it), `SECTIONS`
/// sections, and each region's forward and reverse are read. Every open site is written at every tick, and every written site whose index in
/// its region is a multiple of `EVERY` (one by default: all of them). `rows.tsv` gives a row's `slice`, `section`, `region`, `site`, `tick`,
/// whether the site is open, its class, and an open site's code on `2^(−20)` bits (`-1` at a written one); the four files of
/// [`read_tension`] hold the row's covector, pair chart, current and triads' products. The directory is private: it holds no text, but its
/// rows are the passage's places.
pub fn read_tension_store(args: &[String]) -> Result<()> {
    if args.len() != 14 && args.len() != 15 {
        return Err("read-tension-store UNITS UNITS_SHA STORE STORE_SHA ROLE KEYS KEYS_SHA CODEC CODEC_SHA SECTIONS STATE STATE_SHA OUT [EVERY]".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("read-tension-store")?;
    let units = units_of(&args[1], &args[2])?;
    if !units.merges().is_empty() {
        return Err("the store's cut is on bytes: a units file of merges is refused".into());
    }
    let store = Path::new(&args[3]);
    let counts = store_counts(std::str::from_utf8(&pinned_read(&store.join("STORE.tsv").to_string_lossy(), &args[4], READ_BUDGET as usize)?)?)?;
    let role = args[5].as_str();
    let keys = pinned_read(&args[6], &args[7], READ_BUDGET as usize)?;
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[8], &args[9], READ_BUDGET as usize)?)?, units)?;
    let sections = positive(&args[10])?;
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[11], &args[12], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let pass = learner.pass.clone().ok_or("a state with no pass line: read-tension-store reads a state of the store's line")?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    let out = Path::new(&args[13]);
    let every = match args.get(14) {
        Some(e) => positive(e)?,
        None => 1,
    };
    let names = role_names(&counts, role);
    if pass.role != role || pass.slices.iter().map(|s| s.name.as_str()).ne(names.iter().copied()) {
        return Err("a state whose pass is of another role or slices".into());
    }
    let mut slices = Vec::with_capacity(names.len());
    for &name in &names {
        slices.push(open_slice(store, role, name, &counts)?);
    }
    let d = learner.field.declaration;
    let (dw, m2, j2, ticks) = (d.width, 2 * d.heads * d.modes, 2 * d.triads, d.ticks);
    std::fs::create_dir(out)?;
    write_new(&out.join("dims.tsv"), format!("lambda\t{dw}\nread\t{dw}\ncurrent\t{m2}\nproducts\t{j2}\nticks\t{ticks}\n").as_bytes())?;
    println!("TENSION_LAW role={role} sections={sections} every={every} ticks={ticks} width={dw} current={m2} products={j2} threads={} ms={}", rayon::current_num_threads(), started.elapsed().as_millis());
    let create = |name: &str| -> Result<std::io::BufWriter<std::fs::File>> { Ok(std::io::BufWriter::new(std::fs::OpenOptions::new().write(true).create_new(true).open(out.join(name))?)) };
    let (mut rows, mut lambda, mut read, mut current, mut products) = (create("rows.tsv")?, create("lambda.i64")?, create("read.i32")?, create("current.i64")?, create("products.i64")?);
    // [measurement; the lead, November 16 23:00Z] Beside them, each row's opening chart (`chart.i32`, what a tick's probes read) and, for every
    // open site at every tick and head, its row's temperature covector as the reverse forms it before the rows are summed into the head's one
    // entry (`temper.tsv`: `slice`, `section`, `region`, `site`, `tick`, `head`, `δℓ` on `2^(−40)`): the premise of a row's own temperature.
    let (mut chart, mut temper) = (create("chart.i32")?, create("temper.tsv")?);
    let mut cut = Cut { seed, slices, pass };
    let (mut done, mut written) = (0usize, 0usize);
    while done < sections {
        let mut regions: Vec<(usize, OwnedRegion)> = Vec::new();
        let (mut in_pairs, mut in_sites) = (0u64, 0u64);
        // [the lead, November 22] The section's terrain first, as `train-store` draws it ([`crate::store::terrain_section`]), its rows named
        // `terrain`: the tension a lap would meet next includes the terrain's share.
        let mut stretches = 0usize;
        if cut.pass.terrain.is_some() {
            let drawn = crate::store::terrain_section(&mut cut.pass, &codec, seed)?;
            (in_pairs, in_sites) = (drawn.pairs, drawn.sites);
            regions.extend(drawn.regions.into_iter().map(|(region, _)| (usize::MAX, region)));
        }
        while let Some(drawn) = cut.next() {
            let n = drawn.sites();
            stretches += 1;
            if in_sites > 0 && (in_pairs + n * n > cut.pass.pairs || in_sites + n > cut.pass.sites) {
                break;
            }
            let slice = drawn.slice;
            let Stretch { region, .. } = cut.take(drawn, &codec)?;
            (in_pairs, in_sites) = (in_pairs + n * n, in_sites + n);
            regions.push((slice, region));
        }
        if regions.is_empty() || stretches == 0 {
            break;
        }
        // [the lead, November 22] A stretch the pass reads by two streams is read on that regime ([`Constitution::strand_tension`]): its rows are
        // its open places, every place past the first, each compared at its own frontier as the writer compares it.
        let reads: Vec<std::result::Result<holonics_engine::field::CrossingTension, String>> = regions
            .par_iter()
            .map(|(_, region)| if region.strand { learner.field.strand_tension(&region.classes, region.past) } else { learner.field.crossing_tension(&view_of(region)) }.map_err(|e| e.to_string()))
            .collect();
        for (r, ((slice, region), tension)) in regions.iter().zip(reads).enumerate() {
            let tension = tension?;
            for site in 0..region.classes.len() {
                let open = if region.strand { site > 0 } else { region.unresolved[site] };
                if region.strand && !open {
                    continue;
                }
                if !open && site % every != 0 {
                    continue;
                }
                let code = if open { tension.codes[site].ok_or("an open place without a face")? } else { -1 };
                for k in 0..ticks {
                    writeln!(rows, "{}\t{done}\t{r}\t{site}\t{k}\t{}\t{}\t{code}", if *slice == usize::MAX { "terrain" } else { names[*slice] }, u8::from(open), region.classes[site])?;
                    for &v in &tension.lambda[k][site * dw..(site + 1) * dw] {
                        lambda.write_all(&v.to_le_bytes())?;
                    }
                    for &v in &tension.read[k][site * dw..(site + 1) * dw] {
                        read.write_all(&v.to_le_bytes())?;
                    }
                    for &v in &tension.chart[k][site * dw..(site + 1) * dw] {
                        chart.write_all(&v.to_le_bytes())?;
                    }
                    for &v in &tension.current[k][site * m2..(site + 1) * m2] {
                        current.write_all(&v.to_le_bytes())?;
                    }
                    if j2 > 0 {
                        for &v in &tension.products[k][site * j2..(site + 1) * j2] {
                            products.write_all(&v.to_le_bytes())?;
                        }
                    }
                    written += 1;
                }
            }
            for (k, rows_k) in tension.temper.iter().enumerate() {
                for &(h, i, dl) in rows_k {
                    writeln!(temper, "{}\t{done}\t{r}\t{i}\t{k}\t{h}\t{dl}", if *slice == usize::MAX { "terrain" } else { names[*slice] })?;
                }
            }
        }
        done += 1;
        println!("TENSION_SECTION n={done} regions={} sites={in_sites} rows={written} ms={}", regions.len(), started.elapsed().as_millis());
    }
    for w in [&mut rows, &mut lambda, &mut read, &mut current, &mut products, &mut chart, &mut temper] {
        w.flush()?;
    }
    println!("TENSION_DONE rows={written} sections={done} ms={}", started.elapsed().as_millis());
    Ok(())
}

/// A ruler's carried-lock gain from thousandths, on `2^(−30)`: `carry=1000` is a row that keeps its whole lock.
pub fn carry_of(milli: &str) -> Result<i64> {
    let m: i64 = milli.parse().map_err(|_| "carry=MILLI is a count of thousandths")?;
    if !(0..=1000).contains(&m) {
        return Err("carry=MILLI stands between 0 and 1000".into());
    }
    Ok((m << 30) / 1000)
}

/// [measurement; the lead, November 17, the founding records and the record of the step back] `try-passes UNITS UNITS_SHA KEYS KEYS_SHA CODEC
/// CODEC_SHA FORMS FORMS_SHA STATE STATE_SHA PASSES RECORDS OUT`: **passes over a small table by the learner's own section step**: the
/// state's learner takes `PASSES` passes over a forms table (`label<TAB>prompt<TAB>run`, and `suffix` as a fourth field where a row's run
/// is opened from a keyed place to its end), `RECORDS` records a section, each record a region
/// with a keyed half of its run's places open (a place is open where [`keyed_bit`] of `label:pass:place` is odd, and one place where none
/// is), on the realization it is called through (the card under `train`, the host's threads under `host`), and the learner is
/// written to `OUT`. One line a pass: its sections, its sites and its code in nats a place.
///
/// Why: the tempering study (the record of the step back, §6) reads what many passes over little do to the machine, law by law, on tables
/// of a few thousand records. A field the card does not realize (closed characters) is tried on the host's threads as a premise's trial,
/// reported as one. The state it writes is a study's: it is no line's state and no lap trains from it.
///
/// With `READ READ_SHA EVERY SAVE` after `OUT` (the long trial of November 17, the step back's record §11): every `EVERY` passes, and before
/// the first, the rows of a second table are read with nothing deposited, gathered by the first field of their labels, and one line a
/// group is printed (`TRIAL_READ`): the code of the answer's last digit open alone (the one-place receiver), the same digit's code with
/// the whole run open (the state a free release's first read meets), and the answer's first digit open alone where the answer has two
/// digits or more, in millionths of a nat a place, with the mean density at the written last digit in thousandths. Every `SAVE` passes
/// the learner is written to `OUT.pN`. A row whose run holds no line feed past its first place is a plain row (a stretch of text): its
/// two reads are a keyed half of its run open (the key the row's label and the place, the same at every pass) and the whole run open,
/// each a mean over the open places; its third is the whole run open again, coded at the run's first place alone (the next place on
/// its left context, the state a write's first place meets). With `ROWS` after `SAVE`, each pass takes the table's next `ROWS` rows
/// and never a row twice: a stream, the arm that tells a world dwelt on from records repeated.
pub fn try_passes(args: &[String], realization: &mut dyn holonics_engine::realization::Realization) -> Result<()> {
    if args.len() != 14 && args.len() != 18 && args.len() != 19 {
        return Err("try-passes UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA FORMS FORMS_SHA STATE STATE_SHA PASSES RECORDS OUT [READ READ_SHA EVERY SAVE [ROWS]]".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("try-passes")?;
    let units = units_of(&args[1], &args[2])?;
    let _keys = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?, units)?;
    let table = String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?;
    let mut learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[9], &args[10], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    let (sweeps, records): (usize, usize) = (args[11].parse()?, args[12].parse()?);
    // With `ROWS`, a pass takes the table's next `ROWS` rows where it would take the table whole, so no row is met twice (a stream).
    let stride: Option<usize> = match args.get(18) {
        Some(w) => Some(w.parse::<usize>().ok().filter(|&n| n > 0).ok_or("ROWS is a count of one or more")?),
        None => None,
    };
    let out = Path::new(&args[13]);
    if out.exists() || sweeps == 0 || records == 0 {
        return Err("try-passes writes a new state from one pass or more of one record or more a section".into());
    }
    let unescape = |t: &str| t.replace("\\n", "\n");
    // A row's fourth field, where it stands, names its opening: `suffix` opens the run from a keyed place to its end (the state a write
    // in place order meets: every earlier place known, every later one open); absent, a keyed half of the run's places.
    // `first` opens the row's prompt and holds its run known: a place compared on what stands to its right (the backward reader's state).
    // `strand` reads the row by two streams, every place compared at its own frontier.
    let mut rows: Vec<(String, Vec<usize>, Vec<usize>, u8)> = Vec::new();
    for line in table.lines() {
        let w: Vec<&str> = line.split('\t').collect();
        if w.len() < 3 {
            return Err("a forms row that is not label, prompt and run".into());
        }
        let (p, r) = (codec.encode(unescape(w[1]).as_bytes())?, codec.encode(unescape(w[2]).as_bytes())?);
        if p.is_empty() || r.is_empty() {
            return Err("a forms row with an empty prompt or run".into());
        }
        let opening = match w.get(3).copied() {
            None | Some("") => 0u8,
            Some("suffix") => 1,
            Some("first") => 2,
            // [the lead, November 21] `strand`: the row read by two streams as the pass reads its frontier ([`OwnedRegion::strand`], with
            // the pass's `past` and `second`), every place compared at its own frontier: the regime the writer (`write-next`) reads a state
            // in whose pass reads so. Why: the dwell on plain rows founded the held sums' digit (0.0005 nats) and its free writes came out
            // 0 of 95, because L76's pass reads by two streams and the writer reads there.
            Some("strand") => 3,
            Some(_) => return Err("a forms row whose opening is not `suffix`, `first` or `strand`".into()),
        };
        rows.push((w[0].to_string(), p, r, opening));
    }
    if stride.is_some_and(|n| n * sweeps > rows.len()) {
        return Err("a stream of fewer rows than its passes take".into());
    }
    println!("TRIAL_PASSES records={} passes={sweeps} records_a_section={records} closed={} leak={} threads={}", rows.len(), learner.field.declaration.closed, learner.leak.map_or("none".to_string(), |k| k.to_string()), rayon::current_num_threads());
    // The read table, where one is given: each row's group, prompt, run and the place of its answer's last digit in the run.
    let mut read_rows: Vec<(String, Vec<usize>, Vec<usize>, Option<usize>, String, bool)> = Vec::new();
    let (mut every, mut save) = (0usize, 0usize);
    if args.len() >= 18 {
        let feed = codec.encode(b"\n")?;
        if feed.len() != 1 {
            return Err("a codec whose line feed is not one class".into());
        }
        for line in String::from_utf8(pinned_read(&args[14], &args[15], READ_BUDGET as usize)?)?.lines() {
            let w: Vec<&str> = line.split('\t').collect();
            if w.len() < 3 {
                return Err("a read row that is not label, prompt and run".into());
            }
            let (p, r) = (codec.encode(unescape(w[1]).as_bytes())?, codec.encode(unescape(w[2]).as_bytes())?);
            if p.is_empty() || r.is_empty() {
                return Err("a read row with an empty prompt or run".into());
            }
            let last = r.iter().position(|&c| c == feed[0]).filter(|&at| at > 0).map(|at| at - 1);
            // A read row with `first` as its fourth field is read with its prompt open and its run known, at each of its three reads.
            let first = w.get(3).copied() == Some("first");
            read_rows.push((w[0].split(':').next().unwrap_or("").to_string(), p, r, if first { None } else { last }, w[0].to_string(), first));
        }
        (every, save) = (args[16].parse()?, args[17].parse()?);
        if every == 0 || save == 0 || read_rows.is_empty() {
            return Err("try-passes reads a table of one row or more every pass or more, and saves every pass or more".into());
        }
    }
    // One read of the read table: the last digit open alone, the whole run open, the first digit open alone.
    let read_table = |learner: &Learner, realization: &mut dyn holonics_engine::realization::Realization, pass: usize| -> Result<()> {
        if read_rows.is_empty() {
            return Ok(());
        }
        let region_of = |(_, p, r, last, label, first): &(String, Vec<usize>, Vec<usize>, Option<usize>, String, bool), kind: usize| {
            let mut classes = p.clone();
            classes.extend_from_slice(r);
            let mut open = vec![false; classes.len()];
            if *first {
                open[..p.len()].fill(true);
                return OwnedRegion::plain(classes, open);
            }
            match (kind, last) {
                (0, Some(last)) => open[p.len() + last] = true,
                (0, None) => {
                    for j in 0..r.len() {
                        open[p.len() + j] = keyed_bit(&format!("{label}:read:{j}")) & 1 == 1;
                    }
                    if !open.iter().any(|&o| o) {
                        open[p.len()] = true;
                    }
                }
                (1, _) | (2, None) => open[p.len()..].fill(true),
                _ => open[p.len()] = true,
            }
            OwnedRegion::plain(classes, open)
        };
        let mut groups: std::collections::BTreeMap<String, [(i128, usize); 3]> = std::collections::BTreeMap::new();
        // The density at the written class, each place's on 2^(−20) (a reading's width), summed a group.
        let mut mass: std::collections::BTreeMap<String, u128> = std::collections::BTreeMap::new();
        for kind in 0..3usize {
            let regions: Vec<OwnedRegion> = read_rows.iter().map(|row| region_of(row, kind)).collect();
            let views: Vec<_> = regions.iter().map(view_of).collect();
            let faces = realization.read_faces(&learner.field, &views).map_err(|e| e.to_string())?;
            for ((row, face), region) in read_rows.iter().zip(&faces).zip(&regions) {
                // A plain row sums every open place of its two reads; a sum's row reads its one place.
                let places: Vec<usize> = match (kind, row.3) {
                    _ if row.5 => (0..row.1.len()).collect(),
                    (2, Some(0)) => continue,
                    // A plain row's third read: its whole run open, coded at its first place alone (the next place on its left context).
                    (2, None) => vec![row.1.len()],
                    (2, Some(_)) => vec![row.1.len()],
                    (_, Some(last)) => vec![row.1.len() + last],
                    (_, None) => (row.1.len()..region.classes.len()).filter(|&t| region.unresolved[t]).collect(),
                };
                for at in places {
                    let f = face[at].as_ref().ok_or("a read place that carries no face")?;
                    let (m, t) = (f.masses[region.classes[at]], f.total);
                    let slot = &mut groups.entry(row.0.clone()).or_insert([(0, 0); 3])[kind];
                    slot.0 += i128::from(holonics_engine::field::ratio_code(m, t));
                    slot.1 += 1;
                    if kind == 0 {
                        *mass.entry(row.0.clone()).or_insert(0) += (m << 20) / t.max(1);
                    }
                }
            }
        }
        for (group, sums) in &groups {
            let nats = |(code, n): (i128, usize)| ((code * holonics_engine::field::ln2_face() * 1_000_000) >> 50) / n.max(1) as i128;
            println!(
                "TRIAL_READ pass={pass} group={group} rows={} last_alone={} last_run_open={} first_alone={} first_rows={} density_at_last_milli={}",
                sums[0].1,
                nats(sums[0]),
                nats(sums[1]),
                nats(sums[2]),
                sums[2].1,
                (mass.get(group).copied().unwrap_or(0) * 1000 / sums[0].1.max(1) as u128) >> 20
            );
        }
        Ok(())
    };
    read_table(&learner, realization, 0)?;
    let mut section = 0usize;
    for sweep in 0..sweeps {
        let (mut sites, mut code) = (0usize, 0i128);
        let taken = match stride {
            Some(n) => &rows[sweep * n..(sweep + 1) * n],
            None => &rows[..],
        };
        for chunk in taken.chunks(records) {
            let regions: Vec<OwnedRegion> = chunk
                .iter()
                .map(|(label, p, r, opening)| {
                    let bit = |j: usize| keyed_bit(&format!("{label}:{sweep}:{j}"));
                    let mut classes = p.clone();
                    classes.extend_from_slice(r);
                    let mut open = vec![false; classes.len()];
                    if *opening == 3 {
                        let (past, second) = learner.pass.as_ref().map_or((false, false), |q| (q.past, q.second));
                        let n = classes.len();
                        return OwnedRegion { strand: true, past, second, ..OwnedRegion::plain(classes, vec![false; n]) };
                    }
                    if *opening == 2 {
                        open[..p.len()].fill(true);
                    } else if *opening == 1 {
                        let from = (bit(r.len()) % r.len() as u64) as usize;
                        open[p.len() + from..].fill(true);
                    } else {
                        for j in 0..r.len() {
                            open[p.len() + j] = bit(j) & 1 == 1;
                        }
                    }
                    if !open.iter().any(|&o| o) {
                        open[p.len() + (bit(r.len()) % r.len() as u64) as usize] = true;
                    }
                    OwnedRegion::plain(classes, open)
                })
                .collect();
            let views: Vec<_> = regions.iter().map(view_of).collect();
            let receipt = learner.section_realized(&views, realization).map_err(|e| e.to_string())?;
            sites += receipt.sites;
            code += receipt.code_before as i128;
            section += 1;
        }
        // The pass's code in millionths of a nat a place (ln 2 on 2^(−30), the code on 2^(−20) bits).
        let nats = (code * holonics_engine::field::ln2_face() * 1_000_000) >> 50;
        println!("TRIAL_PASS pass={sweep} sections={section} sites={sites} micronats_a_place={} ms={}", nats / sites.max(1) as i128, started.elapsed().as_millis());
        if every > 0 && (sweep + 1) % every == 0 {
            read_table(&learner, realization, sweep + 1)?;
        }
        if save > 0 && (sweep + 1) % save == 0 && sweep + 1 < sweeps {
            write_new(Path::new(&format!("{}.p{}", out.display(), sweep + 1)), learner.to_text().as_bytes())?;
        }
    }
    write_new(out, learner.to_text().as_bytes())?;
    println!("TRIAL_DONE sections={section} ms={}", started.elapsed().as_millis());
    Ok(())
}

/// [measurement; the lead, November 17, corrected on Codex's audit of that day] **A keyed draw for a ruler's openings**: the FNV-1a fold of
/// a key's bytes, finished by a 64-bit mixer (the SplitMix64 finalizer). Why the finish: the openings of the first trials took bit 17 of
/// the bare fold, and a fold whose last multiplication takes adjacent ASCII digits gives adjacent places nearly the same bit, so 97.8% of
/// the regions opened one place or the whole run where a half was meant (19,024 whole, 19,347 one place and 859 between, of 39,230; the
/// runs of `receipts/2026-11-17_founding` and `2026-11-17_tempering` were made with that draw and are read as such).
fn keyed_bit(key: &str) -> u64 {
    let mut x = key.bytes().fold(0xcbf29ce484222325u64, |h, b| (h ^ u64::from(b)).wrapping_mul(0x100000001b3));
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d049bb133111eb);
    x ^ (x >> 31)
}

/// The key stream's word at `counter` from `seed` (the splitmix finalizer), the writer's and her acts' draws.
pub(crate) fn key_mix(seed: u64, counter: u64) -> u64 {
    let mut z = seed.wrapping_add(counter.wrapping_mul(0x9E37_79B9_7F4A_7C15));
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// [definition; the lead, November 21, drawn out on November 24 for her acts' drafts] **A keyed draw from a face at its own temperature**:
/// a uniform under the letters' mass (`letters`, the void left out unless `stop`) from two draws of the key stream `mix` at the row `k` and
/// the step, and the class whose cumulative mass passes it. The writer's draw (`write_next`) and her acts' (`store::write_strand`).
pub(crate) fn keyed_draw(f: &holonics_engine::field::TowerFace, void: usize, stop: bool, letters: u128, mix: &dyn Fn(u64) -> u64, k: usize, step: usize) -> Option<usize> {
    // A keyed uniform under the letters' mass: two draws make its 128 bits.
    let u = ((u128::from(mix(((k as u64) << 24) ^ step as u64)) << 64) | u128::from(mix(((k as u64) << 24) ^ step as u64 ^ (1 << 60)))) % letters;
    let mut acc = 0u128;
    (0..f.masses.len()).filter(|&c| stop || c != void).find(|&c| {
        acc += f.masses[c];
        acc > u
    })
}

/// [measurement; the lead, November 17, the night's text run] `write-next UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA FORMS FORMS_SHA RUN
/// OUT STATE STATE_SHA [WINDOW]`: **a write of one place a read, each place the last of its region**: after each prompt `RUN` places are
/// written one at a time, the place written being the single open site of a region that ends there (the prompt and what was written
/// before it known, nothing to its right), drawn from its face over the letters by a keyed uniform (the key file's last eight bytes, the
/// row and the place). With `WINDOW`, the region keeps the last `WINDOW` known places. It writes `OUT/forms.written` in `write-forms`'
/// form. Why: a field compared only on the next place of a region that ends there (the trial's rows of a one-place run) is read by the
/// law's writer in a state it was never compared on, a place with a run of open places to its right, and its first panel came out as
/// marks (the record of the night's run); this writer meets the compared state place for place. A ruler's writer on a study's states:
/// the release's law is unchanged. [the lead, November 18] A state whose pass reads its frontier as known streams
/// ([`holonics_engine::field::StorePass::before`]) is written so: each region's known places hear only what stands before them.
pub fn write_next(args: &[String], realization: &mut dyn holonics_engine::realization::Realization) -> Result<()> {
    // [measurement; the lead, November 21, Brandon's 09:00Z] With the last word `stop`, the writer draws the void like any symbol and a
    // row's write ends where the void is drawn: where she would stop if she were let.
    let stop = args.last().map(String::as_str) == Some("stop");
    let args = if stop { &args[..args.len() - 1] } else { args };
    if args.len() != 13 && args.len() != 14 {
        return Err("write-next UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA FORMS FORMS_SHA RUN OUT STATE STATE_SHA [WINDOW] [stop]".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("write-next")?;
    let units = units_of(&args[1], &args[2])?;
    let keys = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?, units)?;
    let table = String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?;
    let run = positive(&args[9])?;
    let out = Path::new(&args[10]);
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[11], &args[12], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let window = match args.get(13) {
        Some(w) => Some(positive(w)?),
        None => None,
    };
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    // [the lead, November 26] A row's prompt and reference may be `hex:` and their octets, two hex digits each, for a passage of any
    // octets (the wave's held documents); such a row's prompt, write and reference are written back as `hex:` too.
    let unhex = |h: &str| -> std::result::Result<Vec<u8>, String> {
        if h.len() % 2 != 0 {
            return Err("a hex row of an odd count of digits".into());
        }
        (0..h.len()).step_by(2).map(|k| u8::from_str_radix(&h[k..k + 2], 16).map_err(|e| e.to_string())).collect()
    };
    let unescape = |t: &str| -> std::result::Result<String, String> { Ok(t.replace("\\n", "\n")) };
    let escape = |b: &[u8]| String::from_utf8_lossy(b).replace('\n', "\\n").replace('\t', "\\t");
    let hexed = |b: &[u8]| format!("hex:{}", b.iter().map(|o| format!("{o:02x}")).collect::<String>());
    let mut rows: Vec<(String, Vec<u8>, Vec<usize>, Vec<u8>)> = Vec::new();
    let mut hex_rows: Vec<bool> = Vec::new();
    for line in table.lines() {
        let w: Vec<&str> = line.split('\t').collect();
        let [label, prompt, reference] = w[..] else { return Err("a forms row that is not three fields".into()) };
        let hex = prompt.starts_with("hex:");
        hex_rows.push(hex);
        let field = |t: &str| -> std::result::Result<Vec<u8>, String> { if hex { unhex(t.strip_prefix("hex:").unwrap_or(t)) } else { unescape(t).map(String::into_bytes) } };
        let bytes = field(prompt)?;
        let classes = codec.encode(&bytes)?;
        if classes.is_empty() {
            return Err("a forms row with an empty prompt".into());
        }
        rows.push((label.to_string(), bytes, classes, field(reference)?));
    }
    std::fs::create_dir(out)?;
    let void = codec.void();
    let mix = |counter: u64| -> u64 { key_mix(seed, counter) };
    let known = learner.pass.as_ref().is_some_and(|p| p.before);
    // [the lead, November 18] A state whose pass reads its frontier by two streams ([`holonics_engine::field::StorePass::strand`]) is
    // written by them: the region is the known places and one more site holding the void (heard by no one: a known site hears only what
    // stands before it), and the face read is the open place's at that last place, which hears every known place.
    let strand = learner.pass.as_ref().is_some_and(|p| p.strand);
    let past = learner.pass.as_ref().is_some_and(|p| p.past);
    let second = learner.pass.as_ref().is_some_and(|p| p.second);
    let mut written: Vec<Vec<usize>> = vec![Vec::new(); rows.len()];
    let mut voids: Vec<Vec<u64>> = vec![Vec::new(); rows.len()];
    let mut stopped: Vec<Option<usize>> = vec![None; rows.len()];
    let mut spreads: Vec<Vec<i128>> = vec![Vec::new(); rows.len()];
    for step in 0..run {
        let regions: Vec<OwnedRegion> = rows
            .iter()
            .zip(&written)
            .map(|(row, w)| {
                let mut classes: Vec<usize> = row.2.iter().chain(w.iter()).copied().collect();
                if let Some(n) = window {
                    let from = classes.len().saturating_sub(n);
                    classes.drain(..from);
                }
                classes.push(void);
                let mut open = vec![false; classes.len()];
                *open.last_mut().expect("a region of one place or more") = true;
                if strand {
                    let n = classes.len();
                    return OwnedRegion { strand: true, past, second, ..OwnedRegion::plain(classes, vec![false; n]) };
                }
                OwnedRegion { before: known, past: known && past, second: known && second, ..OwnedRegion::plain(classes, open) }
            })
            .collect();
        let views: Vec<_> = regions.iter().map(view_of).collect();
        let faces = realization.read_faces(&learner.field, &views).map_err(|e| e.to_string())?;
        for (k, (face, w)) in faces.iter().zip(written.iter_mut()).enumerate() {
            if stopped[k].is_some() {
                continue;
            }
            let f = face.last().and_then(|f| f.as_ref()).ok_or("a written place that carries no face")?;
            let letters = if stop { f.total } else { f.total - f.masses[void] };
            if letters == 0 {
                return Err("a face with no mass on a letter".into());
            }
            // [measurement; the lead, November 21, Brandon's 09:00Z (whether she seeks the stop the writer withholds)] The face's share on
            // the void at each written place, in millionths, beside the draw (`OUT/void.tsv`); the draw itself is unchanged.
            voids[k].push(u64::try_from(f.masses[void].saturating_mul(1_000_000) / f.total.max(1)).unwrap_or(u64::MAX));
            // [measurement; the lead, November 21, Brandon's 09:15Z (halting by least action)] The face's spread at the place, its entropy
            // `Σ p·code(p)` on `2^(−20)` bits (each class's code by the face's own law, its mass on `2^(−40)` of the total), beside the draw.
            let spread: i128 = (0..f.masses.len()).filter(|&c| f.masses[c] > 0).map(|c| (i128::try_from((f.masses[c] << 20) / f.total.max(1)).unwrap_or(0) * i128::from(f.code(c))) >> 20).sum();
            spreads[k].push(spread);
            let class = keyed_draw(f, void, stop, letters, &mix, k, step).ok_or("a draw past the letters' mass")?;
            if class == void {
                stopped[k] = Some(step);
                continue;
            }
            w.push(class);
        }
    }
    let mut text = String::new();
    for (((label, prompt, _, reference), w), &hex) in rows.iter().zip(&written).zip(&hex_rows) {
        let out_of = |b: &[u8]| if hex { hexed(b) } else { escape(b) };
        text.push_str(&format!("{label}\t{}\t{}\t{}\n", out_of(prompt), out_of(&codec.decode(w)), out_of(reference)));
    }
    write_new(&out.join("forms.written"), text.as_bytes())?;
    let mut void_text = String::from("label\tplace\twritten\tvoid_ppm\tspread_millibits\n");
    for (((label, ..), (w, v)), e) in rows.iter().zip(written.iter().zip(&voids)).zip(&spreads) {
        for (t, ((&c, &share), &h)) in w.iter().zip(v).zip(e).enumerate() {
            void_text.push_str(&format!("{label}\t{t}\t{}\t{share}\t{}\n", escape(&codec.decode(&[c])), (h * 1000) >> 20));
        }
    }
    write_new(&out.join("void.tsv"), void_text.as_bytes())?;
    if stop {
        let stops: String = rows.iter().zip(&stopped).map(|((label, ..), s)| format!("{label}\t{}\n", s.map_or("-".to_string(), |t| t.to_string()))).collect();
        write_new(&out.join("stops.tsv"), stops.as_bytes())?;
    }
    println!("NEXT_WRITE_DONE rows={} run={run} window={} ms={}", rows.len(), window.map_or("-".to_string(), |n| n.to_string()), started.elapsed().as_millis());
    Ok(())
}

/// [the lead, November 26] A row's text as its octets: escaped (`\\n` a line's end), or `hex:` and its octets two hex digits each, for a
/// passage of any octets (the wave's held documents), as `read-reach` reads its rows.
fn row_octets(t: &str) -> std::result::Result<Vec<u8>, String> {
    match t.strip_prefix("hex:") {
        Some(h) if h.len() % 2 == 0 => (0..h.len()).step_by(2).map(|k| u8::from_str_radix(&h[k..k + 2], 16).map_err(|e| e.to_string())).collect(),
        Some(_) => Err("a hex row of an odd count of digits".into()),
        None => Ok(t.replace("\\n", "\n").into_bytes()),
    }
}

/// [measurement; the lead, November 18, the record of the two streams §14] `read-strand-states UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA
/// ROWS ROWS_SHA STATE STATE_SHA OUT [past]`: **what a strand's sites hold, written out for a ruler**. Each row of `ROWS` (`read-far`'s
/// table: `label<TAB>known text<TAB>next symbol`) is read whole as a passage by two streams, every place known
/// ([`holonics_engine::field::Constitution::strand_reads`]), with the word `past` its odd contacts facing the past. `OUT/rows.tsv` takes a
/// line a place (`row`, `group`, `place`, `class`); `OUT/known.i32` each known site's read after the last tick and `OUT/open_K.i32`
/// each open place's read after tick `K` (little-endian, `D` words a place, in the lines' order); `OUT/gates_K.i64` each known site's
/// gate on every carry circle at tick `K` (`2C` words a place, real parts then imaginary, on `2^(−30)`;
/// [`holonics_engine::field::Constitution::strand_gates`]); `OUT/dims.tsv` names `D`, the ticks and the carry circles. On the host's
/// threads; the state is read, never written. The directory is private: its rows are the passage's places. [the lead, November 19, the
/// frontier record §23] With the word `carries` (after `past` where both are given) it writes, in place of the gates and the open places'
/// reads (at 512 circles they are 4 KB a place a tick), `OUT/carries.i32`: each known site's carried product before it at the last tick
/// on every sixteenth circle (`k = 0, 16, 32, …`), real parts then imaginary, on `2^(−16)`
/// ([`holonics_engine::field::Constitution::strand_carries`]), `OUT/open_last.i32` each open place's read after the last tick (`D` words
/// a place, the operand its face is linear in), and `dims.tsv` names the circles written and `D`. [the lead, November 21, the reach] With the
/// word `rows` (after `past` where both are given) it writes, in place of the known reads and the gates, `OUT/shares.tsv`: each open
/// place's row at every tick and head (`row`, `tick`, `head`, `place`, the source's place, its share in millionths, the sources under a
/// thousandth left out; [`holonics_engine::field::Constitution::strand_open_rows`]), beside `OUT/open_K.i32`.
pub fn read_strand_states(args: &[String]) -> Result<()> {
    let words: Vec<&str> = args.iter().skip(12).map(String::as_str).collect();
    let (past, carries, open_rows) = (words.contains(&"past"), words.contains(&"carries"), words.contains(&"rows"));
    if args.len() < 12
        || words.len() != usize::from(past) + usize::from(carries) + usize::from(open_rows)
        || (past && carries && words != ["past", "carries"])
        || (open_rows && carries)
        || (past && open_rows && words != ["past", "rows"])
    {
        return Err("read-strand-states UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA ROWS ROWS_SHA STATE STATE_SHA OUT [past] [carries | rows]".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("read-strand-states")?;
    let units = units_of(&args[1], &args[2])?;
    let _keys = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?, units)?;
    let table = String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?;
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[9], &args[10], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    let out = Path::new(&args[11]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let mut rows: Vec<(String, Vec<usize>)> = Vec::new();
    for line in table.lines() {
        let w: Vec<&str> = line.split('\t').collect();
        let [label, known, next] = w[..] else { return Err("a row that is not its label, its known text and its next symbol".into()) };
        let mut classes = codec.encode(&row_octets(known)?)?;
        classes.extend(codec.encode(&row_octets(next)?)?.into_iter().take(1));
        if classes.len() < 2 {
            return Err("a row of fewer than two places".into());
        }
        rows.push((label.splitn(3, ':').take(2).collect::<Vec<_>>().join(":"), classes));
    }
    let field = &learner.field;
    if carries {
        let circles = field.declaration.carry;
        let every: Vec<usize> = (0..circles).step_by(16).collect();
        let products: Vec<Vec<i64>> = rows.par_iter().map(|(_, classes)| field.strand_carries(classes, past).map_err(|e| e.to_string())).collect::<std::result::Result<_, _>>()?;
        let opens: Vec<Vec<i32>> = rows.par_iter().map(|(_, classes)| field.strand_reads(classes, past).map(|(_, o)| o.last().cloned().unwrap_or_default()).map_err(|e| e.to_string())).collect::<std::result::Result<_, _>>()?;
        let open_bytes: Vec<u8> = opens.iter().flat_map(|o| o.iter().flat_map(|v| v.to_le_bytes())).collect();
        std::fs::create_dir_all(out)?;
        let mut lines = String::new();
        let mut bytes: Vec<u8> = Vec::new();
        for (r, ((group, classes), q)) in rows.iter().zip(&products).enumerate() {
            for (t, class) in classes.iter().enumerate() {
                lines.push_str(&format!("{r}\t{group}\t{t}\t{class}\n"));
                for part in 0..2 {
                    for &k in &every {
                        let v = i32::try_from(q[t * 2 * circles + part * circles + k]).map_err(|_| "a carried product past 32 bits")?;
                        bytes.extend(v.to_le_bytes());
                    }
                }
            }
        }
        write_new(&out.join("rows.tsv"), lines.as_bytes())?;
        write_new(&out.join("carries.i32"), &bytes)?;
        write_new(&out.join("open_last.i32"), &open_bytes)?;
        write_new(&out.join("dims.tsv"), format!("circles\t{circles}\nwritten\t{}\nevery\t16\nread\t{}\n", every.len(), field.declaration.width).as_bytes())?;
        println!("STRAND_CARRIES rows={} places={} circles_written={} past={past} ms={}", rows.len(), rows.iter().map(|(_, c)| c.len()).sum::<usize>(), every.len(), started.elapsed().as_millis());
        return Ok(());
    }
    if open_rows {
        // [the lead, November 21] Each open place's row at every tick and head, each source's place and its share in millionths, the
        // sources under a thousandth of the row left out, beside each open place's read after every tick.
        let reads: Vec<(Vec<i32>, Vec<Vec<i32>>)> = rows.par_iter().map(|(_, classes)| field.strand_reads(classes, past).map_err(|e| e.to_string())).collect::<std::result::Result<_, _>>()?;
        let opened: Vec<Vec<Vec<Vec<Vec<(u32, u64)>>>>> = rows.par_iter().map(|(_, classes)| field.strand_open_rows(classes, past).map_err(|e| e.to_string())).collect::<std::result::Result<_, _>>()?;
        std::fs::create_dir_all(out)?;
        let ticks = field.declaration.ticks;
        let (mut lines, mut shares) = (String::new(), String::new());
        let mut open: Vec<Vec<u8>> = vec![Vec::new(); ticks];
        for (r, (((group, classes), (_, o)), by_tick)) in rows.iter().zip(&reads).zip(&opened).enumerate() {
            for (t, class) in classes.iter().enumerate() {
                lines.push_str(&format!("{r}\t{group}\t{t}\t{class}\n"));
            }
            for (tick, slot) in open.iter_mut().enumerate() {
                slot.extend(o[tick].iter().flat_map(|v| v.to_le_bytes()));
            }
            for (tick, by_head) in by_tick.iter().enumerate() {
                for (h, by_place) in by_head.iter().enumerate() {
                    for (p, row) in by_place.iter().enumerate() {
                        for &(j, share) in row {
                            let milli = (u128::from(share) * 1_000_000) >> holonics_engine::field::SHARE_BITS;
                            if milli >= 1_000 {
                                shares.push_str(&format!("{r}\t{tick}\t{h}\t{p}\t{j}\t{milli}\n"));
                            }
                        }
                    }
                }
            }
        }
        write_new(&out.join("rows.tsv"), lines.as_bytes())?;
        write_new(&out.join("shares.tsv"), shares.as_bytes())?;
        for (tick, bytes) in open.iter().enumerate() {
            write_new(&out.join(format!("open_{tick}.i32")), bytes)?;
        }
        write_new(&out.join("dims.tsv"), format!("read\t{}\nticks\t{ticks}\nheads\t{}\nstill\t{}\nframes\t{}\n", field.declaration.width, field.declaration.heads, field.declaration.still, field.declaration.frames).as_bytes())?;
        println!("STRAND_ROWS rows={} places={} past={past} ms={}", rows.len(), rows.iter().map(|(_, c)| c.len()).sum::<usize>(), started.elapsed().as_millis());
        return Ok(());
    }
    let reads: Vec<(Vec<i32>, Vec<Vec<i32>>)> = rows.par_iter().map(|(_, classes)| field.strand_reads(classes, past).map_err(|e| e.to_string())).collect::<std::result::Result<_, _>>()?;
    let gates: Vec<Vec<Vec<i64>>> = rows.par_iter().map(|(_, classes)| field.strand_gates(classes, past).map_err(|e| e.to_string())).collect::<std::result::Result<_, _>>()?;
    std::fs::create_dir_all(out)?;
    let ticks = field.declaration.ticks;
    let mut lines = String::new();
    let mut known: Vec<u8> = Vec::new();
    let mut open: Vec<Vec<u8>> = vec![Vec::new(); ticks];
    for (r, ((group, classes), (k, o))) in rows.iter().zip(&reads).enumerate() {
        for (t, class) in classes.iter().enumerate() {
            lines.push_str(&format!("{r}\t{group}\t{t}\t{class}\n"));
        }
        known.extend(k.iter().flat_map(|v| v.to_le_bytes()));
        for (tick, slot) in open.iter_mut().enumerate() {
            slot.extend(o[tick].iter().flat_map(|v| v.to_le_bytes()));
        }
    }
    write_new(&out.join("rows.tsv"), lines.as_bytes())?;
    write_new(&out.join("known.i32"), &known)?;
    for (tick, bytes) in open.iter().enumerate() {
        write_new(&out.join(format!("open_{tick}.i32")), bytes)?;
    }
    for tick in 0..ticks {
        let bytes: Vec<u8> = gates.iter().flat_map(|g| g[tick].iter().flat_map(|v| v.to_le_bytes())).collect();
        write_new(&out.join(format!("gates_{tick}.i64")), &bytes)?;
    }
    write_new(&out.join("dims.tsv"), format!("read\t{}\nticks\t{ticks}\ncircles\t{}\n", field.declaration.width, field.declaration.carry).as_bytes())?;
    println!("STRAND_STATES rows={} places={} past={past} ms={}", rows.len(), rows.iter().map(|(_, c)| c.len()).sum::<usize>(), started.elapsed().as_millis());
    Ok(())
}

/// [measurement; the lead, November 21, the precision pass (G-W5)] `read-section-covectors UNITS UNITS_SHA STORE STORE_SHA ROLE KEYS KEYS_SHA
/// CODEC CODEC_SHA SECTIONS STATE STATE_SHA`: **how long a block's covector stays coherent**. The store's `ROLE` is cut from the state's own pass
/// as [`read_tension_store`] cuts it (no world's acts, no terrain's records), `SECTIONS` sections, and each section's material covector is read
/// on the host at the state (`Constitution::read_and_return`, the deposit's operand, every section at the same state). One `SECTION_COSINE` line a
/// pair of successive sections: the cosine of the whole covector, and by family the cosine and its entries. A ruler: nothing is deposited.
pub fn read_section_covectors(args: &[String]) -> Result<()> {
    if args.len() != 13 {
        return Err("read-section-covectors UNITS UNITS_SHA STORE STORE_SHA ROLE KEYS KEYS_SHA CODEC CODEC_SHA SECTIONS STATE STATE_SHA".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("read-section-covectors")?;
    let units = units_of(&args[1], &args[2])?;
    let store = Path::new(&args[3]);
    let counts = store_counts(std::str::from_utf8(&pinned_read(&store.join("STORE.tsv").to_string_lossy(), &args[4], READ_BUDGET as usize)?)?)?;
    let role = args[5].as_str();
    let keys = pinned_read(&args[6], &args[7], READ_BUDGET as usize)?;
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[8], &args[9], READ_BUDGET as usize)?)?, units)?;
    let sections = positive(&args[10])?;
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[11], &args[12], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let pass = learner.pass.clone().ok_or("a state with no pass line")?;
    let names = role_names(&counts, role);
    let mut slices = Vec::with_capacity(names.len());
    for &name in &names {
        slices.push(open_slice(store, role, name, &counts)?);
    }
    let families = learner.field.families_all();
    let mut cut = Cut { seed, slices, pass };
    let mut last: Option<Vec<i128>> = None;
    for done in 0..sections {
        let mut regions: Vec<OwnedRegion> = Vec::new();
        let (mut in_pairs, mut in_sites) = (0u64, 0u64);
        while let Some(drawn) = cut.next() {
            let n = drawn.sites();
            if in_sites > 0 && (in_pairs + n * n > cut.pass.pairs || in_sites + n > cut.pass.sites) {
                break;
            }
            let Stretch { region, .. } = cut.take(drawn, &codec)?;
            (in_pairs, in_sites) = (in_pairs + n * n, in_sites + n);
            regions.push(region);
        }
        if regions.is_empty() {
            break;
        }
        let views: Vec<holonics_engine::field::Region> = regions.iter().map(view_of).collect();
        let (_, g) = learner.field.read_and_return(&views).map_err(|e| e.to_string())?;
        if let Some(prev) = &last {
            // A cosine read at the host's exterior: floats are a ruler's here.
            #[allow(clippy::float_arithmetic, clippy::cast_precision_loss)]
            let cos = |a: &[i128], b: &[i128]| -> String {
                let (mut ab, mut aa, mut bb) = (0f64, 0f64, 0f64);
                for (&x, &y) in a.iter().zip(b) {
                    let (x, y) = (x as f64, y as f64);
                    ab += x * y;
                    aa += x * x;
                    bb += y * y;
                }
                if aa == 0.0 || bb == 0.0 { "-".to_string() } else { format!("{:.4}", ab / (aa * bb).sqrt()) }
            };
            let by: Vec<String> = families.iter().enumerate().filter(|(_, f)| f.1 > 0).map(|(k, &(start, len, _))| format!("{k}:{len}:{}", cos(&prev[start..start + len], &g[start..start + len]))).collect();
            println!("SECTION_COSINE section={done} regions={} sites={in_sites} all={} families={} ms={}", regions.len(), cos(prev, &g), by.join(","), started.elapsed().as_millis());
        }
        last = Some(g);
    }
    Ok(())
}

/// [measurement; the lead, November 25, G-M1 (a)] `read-slice-fades UNITS UNITS_SHA STORE STORE_SHA ROLE KEYS KEYS_SHA CODEC CODEC_SHA
/// SECTIONS STATE STATE_SHA`: **each ring's fade covector summed slice by slice**. The pass's own cut draws `SECTIONS` sections from the state's
/// place as training draws them; each section's regions are read and returned on the host a slice at a time (`read_and_return` on that slice's
/// regions alone, nothing deposited), and each turned ring's fade covector (`2^40 ∂L/∂ℓ_s`, the skin's homogeneity) and second fade's, where the
/// rings hold them, are summed by slice with the slice's sites. A positive sum asks the ring to fade more slowly there (the deposit descends it, `γ = 2^ℓ`), a negative one faster.
/// One `SLICE_FADES` line a slice and kind (`fade`, `twin`): its sites and `period:sum` for every turned ring; one `RINGS` line first with the
/// rings' periods by slot. A ruler's read of a saved state; nothing is written back.
pub fn read_slice_fades(args: &[String]) -> Result<()> {
    if args.len() != 13 && !(args.len() == 14 && args[13] == "breaks") {
        return Err("read-slice-fades UNITS UNITS_SHA STORE STORE_SHA ROLE KEYS KEYS_SHA CODEC CODEC_SHA SECTIONS STATE STATE_SHA [breaks]".into());
    }
    let halves = args.len() == 14;
    let started = std::time::Instant::now();
    refuse_variables("read-slice-fades")?;
    let units = units_of(&args[1], &args[2])?;
    let store = Path::new(&args[3]);
    let counts = store_counts(std::str::from_utf8(&pinned_read(&store.join("STORE.tsv").to_string_lossy(), &args[4], READ_BUDGET as usize)?)?)?;
    let role = args[5].as_str();
    let keys = pinned_read(&args[6], &args[7], READ_BUDGET as usize)?;
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[8], &args[9], READ_BUDGET as usize)?)?, units)?;
    let sections = positive(&args[10])?;
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[11], &args[12], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let pass = learner.pass.clone().ok_or("a state with no pass line")?;
    let names = role_names(&counts, role);
    let mut slices = Vec::with_capacity(names.len());
    for &name in &names {
        slices.push(open_slice(store, role, name, &counts)?);
    }
    let (d, l) = (learner.field.declaration, learner.field.layout().clone());
    if !d.fade && !d.twin {
        return Err("a state whose rings hold no fade".into());
    }
    let slots = d.turned_slots();
    let periods: Vec<usize> = learner.field.rings().iter().map(|(n, _)| *n).collect();
    println!("RINGS slots={slots} periods={}", periods.iter().map(|p| p.to_string()).collect::<Vec<_>>().join(","));
    let breaks: Vec<usize> = [&b" "[..], &b"\n"[..]].iter().filter_map(|t| codec.encode(t).ok().filter(|c| c.len() == 1).map(|c| c[0])).collect();
    if halves {
        println!("BREAKS classes={breaks:?}");
    }
    let mut cut = Cut { seed, slices, pass };
    let (mut fade, mut twin, mut sites) = (vec![vec![0i128; slots]; names.len()], vec![vec![0i128; slots]; names.len()], vec![0u64; names.len()]);
    for done in 0..sections {
        let mut regions: Vec<(usize, OwnedRegion)> = Vec::new();
        let (mut in_pairs, mut in_sites) = (0u64, 0u64);
        while let Some(drawn) = cut.next() {
            let n = drawn.sites();
            if in_sites > 0 && (in_pairs + n * n > cut.pass.pairs || in_sites + n > cut.pass.sites) {
                break;
            }
            let slice = drawn.slice;
            let Stretch { region, .. } = cut.take(drawn, &codec)?;
            (in_pairs, in_sites) = (in_pairs + n * n, in_sites + n);
            regions.push((slice, region));
        }
        if regions.is_empty() {
            break;
        }
        // [measurement; the lead, November 26, the formal record's §5.3] With `breaks`, each slice's regions of the section are parted at
        // the slice's median count of breaks a place (a space or a line's end, as the codec writes them) into its sparser and denser
        // half, each half read and returned alone: a ring's fade covector against the count of breaks a passage holds.
        if halves {
            for s in 0..names.len() {
                let mut views: Vec<(u64, u64, holonics_engine::field::Region)> = regions
                    .iter()
                    .filter(|(k, _)| *k == s)
                    .map(|(_, r)| {
                        let v = view_of(r);
                        let b = v.classes.iter().filter(|c| breaks.contains(c)).count() as u64;
                        (b, v.classes.len() as u64, v)
                    })
                    .collect();
                if views.len() < 2 {
                    continue;
                }
                // The order is by breaks a place, `b_1 n_2 < b_2 n_1`, ties by place count: a partition of the section's regions.
                views.sort_by(|a, b| (a.0 * b.1).cmp(&(b.0 * a.1)).then(a.1.cmp(&b.1)));
                let half = views.len() / 2;
                for (name_h, part) in [("sparse", &views[..half]), ("dense", &views[half..])] {
                    let (b, n) = (part.iter().map(|v| v.0).sum::<u64>(), part.iter().map(|v| v.1).sum::<u64>());
                    let rs: Vec<holonics_engine::field::Region> = part.iter().map(|v| v.2.clone()).collect();
                    let (_, g) = learner.field.read_and_return(&rs).map_err(|e| e.to_string())?;
                    for (kind, base, on) in [("fade", l.fade, d.fade), ("twin", l.twin_fade, d.twin)] {
                        if on {
                            println!("SLICE_FADES_HALF section={done} slice={} half={name_h} regions={} sites={n} breaks={b} kind={kind} {}", names[s], part.len(), (0..slots).map(|slot| format!("{}:{}", periods[slot], g[base + slot])).collect::<Vec<_>>().join(" "));
                        }
                    }
                }
            }
            println!("SLICE_FADES_SECTION section={done} regions={} sites={in_sites} ms={}", regions.len(), started.elapsed().as_millis());
            continue;
        }
        for s in 0..names.len() {
            let views: Vec<holonics_engine::field::Region> = regions.iter().filter(|(k, _)| *k == s).map(|(_, r)| view_of(r)).collect();
            if views.is_empty() {
                continue;
            }
            sites[s] += views.iter().map(|v| v.classes.len() as u64).sum::<u64>();
            let (_, g) = learner.field.read_and_return(&views).map_err(|e| e.to_string())?;
            for slot in 0..slots {
                if d.fade {
                    fade[s][slot] += g[l.fade + slot];
                }
                if d.twin {
                    twin[s][slot] += g[l.twin_fade + slot];
                }
            }
        }
        println!("SLICE_FADES_SECTION section={done} regions={} sites={in_sites} ms={}", regions.len(), started.elapsed().as_millis());
    }
    for (s, name) in names.iter().enumerate() {
        for (kind, sums, on) in [("fade", &fade, d.fade), ("twin", &twin, d.twin)] {
            if on {
                println!("SLICE_FADES slice={name} kind={kind} sites={} {}", sites[s], (0..slots).map(|slot| format!("{}:{}", periods[slot], sums[s][slot])).collect::<Vec<_>>().join(" "));
            }
        }
    }
    Ok(())
}

/// [measurement; the lead, November 21, the precision pass (G-W0, G-W2, G-W4)] `read-widths END END_SHA MEAN MEAN_SHA OUT`: **each family's
/// words, their spread and their silent steps**. `OUT/families.tsv` takes a line a family of the whole material (fine, level and glue): its
/// name, entries, grain, the 50th, 99th and 99.9th hundredths and the largest of `|θ|` at the end (on `2^(−24)` whatever the grain), the root
/// mean square of the end less the mean (on `2^(−24)`), and of the entries with a nonzero first moment the count whose deposit step
/// releases to zero at rates 12, 16 and 20 (`deposit_over` on the end's moments). A ruler's read of saved states; nothing is written back.
/// [measurement; the lead, November 22, the second precision pass (G-R2, G-R3, G-E4 (c))] Each family's line also takes the mean of
/// `deposit_root` of the end's second moment over its moving entries (`root_mean`, in the second moment's own units, rounded down), and the
/// moving entries whose step remainder is nonzero at the end (`rest_nonzero`, `-` where the end carries none); `OUT/rows.tsv` takes a line
/// a row of every family whose fan-in is over one and divides its entries (`Constitution::fan_ins`; a map's row is one output): the
/// family, its name, the row and the row's root mean square of the end less the mean (on `2^(−24)`). Every entry is read as its whole word
/// (its read part plus its rest where a lattice is set), so a lattice's end is read against its whole words' mean (`WHOLE.k`).
pub fn read_widths(args: &[String]) -> Result<()> {
    if args.len() != 6 {
        return Err("read-widths END END_SHA MEAN MEAN_SHA OUT".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("read-widths")?;
    let end = Learner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let mean = Learner::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let out = Path::new(&args[5]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    if end.field.material_len() != mean.field.material_len() {
        return Err("an end and a mean of different material".into());
    }
    let named = |l: &holonics_engine::field::Loci| -> Vec<(usize, &'static str)> {
        vec![(l.enc, "enc"), (l.before, "before"), (l.after, "after"), (l.q, "q"), (l.q_bias, "q_bias"), (l.v, "v"), (l.v_bias, "v_bias"), (l.out, "out"), (l.out_bias, "out_bias"), (l.a, "a"), (l.a_bias, "a_bias"), (l.b, "b"), (l.b_bias, "b_bias"), (l.w, "w"), (l.w_bias, "w_bias"), (l.read, "read"), (l.read_bias, "read_bias"), (l.moment_before, "moment_before"), (l.moment_after, "moment_after"), (l.temper, "temper"), (l.probe, "probe"), (l.probe_bias, "probe_bias"), (l.pace, "pace"), (l.moment_face, "moment_face"), (l.moment_face_bias, "moment_face_bias"), (l.lift_bias, "lift_bias"), (l.carry, "carry"), (l.carry_bias, "carry_bias"), (l.triad, "triad"), (l.triad_bias, "triad_bias"), (l.w_triad, "w_triad"), (l.opening, "opening"), (l.opening_bias, "opening_bias"), (l.junction, "junction"), (l.junction_bias, "junction_bias"), (l.mark, "mark"), (l.loud, "loud"), (l.closed_key, "closed_key"), (l.closed_odds, "closed_odds"), (l.closed_odds_bias, "closed_odds_bias"), (l.pump, "pump"), (l.pump_bias, "pump_bias"), (l.lane_leak, "lane_leak"), (l.friction, "friction"), (l.friction_gate, "friction_gate")]
    };
    let field = &end.field;
    let fine = field.theta.len();
    let level_at = fine;
    let glue_at = fine + field.scale.as_ref().map_or(0, |s| s.coarse.theta.len());
    let name_of = |start: usize, len: usize| -> String {
        let pick = |l: &holonics_engine::field::Loci, at: usize| named(l).into_iter().filter(|&(o, _)| o == at).map(|(_, n)| n).last().unwrap_or("?").to_string();
        if start < fine {
            pick(field.layout(), start)
        } else if start < glue_at {
            format!("level:{}", field.scale.as_ref().map_or("?".to_string(), |s| pick(s.coarse.layout(), start - level_at)))
        } else {
            format!("glue:{}:{len}", start - glue_at)
        }
    };
    // [the lead, November 22] Each entry's whole word (its read part plus its rest under a lattice, `Learner::whole_material`).
    let ve: Vec<i64> = end.whole_material();
    let vm: Vec<i64> = mean.whole_material();
    let (first, second) = end.moments();
    let fan_ins = field.fan_ins();
    let mut rows = String::from("family\tname\trow\trms_end_less_mean\n");
    let mut lines = String::from("family\tname\tentries\tgrain\tp50\tp99\tp999\tmax\trms_end_less_mean\tmoving\tsilent12\tsilent16\tsilent20\troot_mean\trest_nonzero\n");
    for (k, &(start, len, grain)) in field.families_all().iter().enumerate() {
        if len == 0 {
            continue;
        }
        let up = |v: i64| -> i64 { if grain < MATERIAL_BITS_ { v << (MATERIAL_BITS_ - grain) } else { v } };
        let mut mags: Vec<i64> = ve[start..start + len].iter().map(|&v| up(v.abs())).collect();
        mags.sort_unstable();
        let q = |f: usize| mags[((len - 1) * f) / 1000];
        let sq: i128 = (start..start + len).map(|i| { let d = i128::from(up(ve[i] - vm[i])); d * d }).sum();
        let rms = (sq / len as i128).max(0) as u128;
        let rms = rms.isqrt();
        let (mut moving, mut silent, mut roots, mut rested) = (0usize, [0usize; 3], 0i128, 0usize);
        for i in start..start + len {
            if first[i] == 0 {
                continue;
            }
            moving += 1;
            let root = holonics_engine::field::deposit_root(second[i]);
            roots += root;
            rested += usize::from(end.remainder.as_ref().is_some_and(|r| r[i] != 0));
            for (s, rate) in silent.iter_mut().zip([12u32, 16, 20]) {
                *s += usize::from(holonics_engine::field::deposit_over(first[i], root, grain, rate) == 0);
            }
        }
        let root_mean = if moving == 0 { 0 } else { roots / moving as i128 };
        let rest_nonzero = if end.remainder.is_some() { rested.to_string() } else { "-".to_string() };
        lines.push_str(&format!("{k}\t{}\t{len}\t{grain}\t{}\t{}\t{}\t{}\t{rms}\t{moving}\t{}\t{}\t{}\t{root_mean}\t{rest_nonzero}\n", name_of(start, len), q(500), q(990), q(999), mags[len - 1], silent[0], silent[1], silent[2]));
        let x = usize::try_from(fan_ins.get(k).copied().unwrap_or(1)).unwrap_or(1);
        if x > 1 && len % x == 0 {
            for (row, at) in (start..start + len).step_by(x).enumerate() {
                let sq: i128 = (at..at + x).map(|i| { let d = i128::from(up(ve[i] - vm[i])); d * d }).sum();
                rows.push_str(&format!("{k}\t{}\t{row}\t{}\n", name_of(start, len), ((sq / x as i128).max(0) as u128).isqrt()));
            }
        }
    }
    std::fs::create_dir_all(out)?;
    write_new(&out.join("families.tsv"), lines.as_bytes())?;
    write_new(&out.join("rows.tsv"), rows.as_bytes())?;
    println!("WIDTHS families={} material={} rate={} ms={}", field.families_all().len(), field.material_len(), end.rate_bits, started.elapsed().as_millis());
    Ok(())
}

const MATERIAL_BITS_: u32 = holonics_engine::field::MATERIAL_BITS;

/// [measurement; the lead, November 21, the reach] `read-reach UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA ROWS ROWS_SHA STATE STATE_SHA OUT
/// SETTINGS…`: **the code of every place by two streams under a ruler's friction of distance**. Each row of `ROWS` (`read-far`'s table) is
/// read whole as a passage by two streams with its odd contacts facing the past, every place at its own frontier
/// ([`holonics_engine::field::Constitution::strand_codes`]), once a setting. A setting is `law` (none) or a list `h:kind:milli,…`, head `h`'s
/// receivers of kind `kind` (one a listener) scoring a source `milli` thousandths of a bit lower an octave of its distance
/// ([`holonics_engine::field::Constitution::ruler_friction`]). `OUT/codes.tsv` takes a line a place (`row`, `group`, `place`, then each
/// setting's code on `2^(−20)` bits); one `REACH` line a setting and group gives the code in millionths of a nat a place. A ruler's forward:
/// the state is read, never written. `cut:C:MASK` reads every place from `C` on as the region that begins there, but for the stores `MASK`
/// lets across the cut, and `from:C` the places from `C` on as a passage of their own (what a region hands the next, November 25).
pub fn read_reach(args: &[String]) -> Result<()> {
    if args.len() < 13 {
        return Err("read-reach UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA ROWS ROWS_SHA STATE STATE_SHA OUT SETTINGS…".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("read-reach")?;
    let units = units_of(&args[1], &args[2])?;
    let _keys = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?, units)?;
    let table = String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?;
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[9], &args[10], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    let out = Path::new(&args[11]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let heads = learner.field.declaration.heads;
    let mut settings: Vec<(String, Option<Vec<i64>>)> = Vec::new();
    for word in &args[12..] {
        if word == "law" || word == "lanes" || word == "moves" || word == "hands" || word.starts_with("round:") || word.starts_with("state:") || word.starts_with("places:") || word.starts_with("lane:") || word.starts_with("lanept:") || word.starts_with("fade:") || word == "skin:places" || word.starts_with("cut:") || word.starts_with("from:") {
            settings.push((word.clone(), None));
            continue;
        }
        let mut f = vec![0i64; 2 * heads];
        for part in word.split(',') {
            let w: Vec<&str> = part.split(':').collect();
            let [h, kind, milli] = w[..] else { return Err("a setting that is not h:kind:milli,…".into()) };
            let (h, kind, milli): (usize, usize, i64) = (h.parse()?, kind.parse()?, milli.parse()?);
            if h >= heads || kind > 1 {
                return Err("a setting past the field's heads or kinds".into());
            }
            f[2 * h + kind] = holonics_engine::field::div_nearest(i128::from(milli) << holonics_engine::field::FACE_BITS, 1000) as i64;
        }
        settings.push((word.clone(), Some(f)));
    }
    // A row's text is escaped (`\\n` a line's end), or `hex:` and its octets two hex digits each, for a passage of any octets (the
    // lead, November 26: the wave's held rows).
    let unescape = |t: &str| -> std::result::Result<Vec<u8>, String> {
        match t.strip_prefix("hex:") {
            Some(h) if h.len() % 2 == 0 => (0..h.len()).step_by(2).map(|k| u8::from_str_radix(&h[k..k + 2], 16).map_err(|e| e.to_string())).collect(),
            Some(_) => Err("a hex row of an odd count of digits".into()),
            None => Ok(t.replace("\\n", "\n").into_bytes()),
        }
    };
    let mut rows: Vec<(String, Vec<usize>)> = Vec::new();
    for line in table.lines() {
        let w: Vec<&str> = line.split('\t').collect();
        let [label, known, next] = w[..] else { return Err("a row that is not its label, its known text and its next symbol".into()) };
        let mut classes = codec.encode(&unescape(known)?)?;
        classes.extend(codec.encode(&unescape(next)?)?.into_iter().take(1));
        if classes.len() < 2 {
            return Err("a row of fewer than two places".into());
        }
        rows.push((label.splitn(3, ':').take(2).collect::<Vec<_>>().join(":"), classes));
    }
    // [the lead, November 22, the chirality pass's second read] The word `hands` among the settings: the circles' hands along their scans
    // summed over every row ([`holonics_engine::field::Constitution::strand_chirality`]), printed as `REACH_HANDS` lines and each circle's
    // line in `OUT/hands.tsv` (`circle`, `scan`, `turns`, `s_positive`, `bias` and `spread` of the turn chart on its `2^(−16)`), no code read.
    if let Some(at) = settings.iter().position(|(n, _)| n == "hands") {
        settings.remove(at);
        let parts: Vec<holonics_engine::field::Chirality> = rows.par_iter().map(|(_, classes)| learner.field.strand_chirality(classes, true).map_err(|e| e.to_string())).collect::<std::result::Result<_, _>>()?;
        let c = learner.field.declaration.carry;
        let mut all = holonics_engine::field::Chirality { circle_turns: vec![0; c], circle_right: vec![0; c], circle_square: vec![0; c], circle_count: vec![0; c], ..Default::default() };
        for p in &parts {
            (all.pairs, all.s_agree, all.os_agree) = (all.pairs + p.pairs, all.s_agree + p.s_agree, all.os_agree + p.os_agree);
            (all.left_turns, all.left_right, all.right_turns, all.right_right) = (all.left_turns + p.left_turns, all.left_right + p.left_right, all.right_turns + p.right_turns, all.right_right + p.right_right);
            for k in 0..c {
                all.circle_turns[k] += p.circle_turns[k];
                all.circle_right[k] += p.circle_right[k];
                all.circle_square[k] += p.circle_square[k];
                all.circle_count[k] += p.circle_count[k];
            }
        }
        let thousandths = |a: u64, b: u64| if b == 0 { 0 } else { a * 1000 / b };
        println!("REACH_HANDS pairs={} s_agree_milli={} os_agree_milli={} left_turns={} left_right_milli={} right_turns={} right_right_milli={}", all.pairs, thousandths(all.s_agree, all.pairs), thousandths(all.os_agree, all.pairs), all.left_turns, thousandths(all.left_right, all.left_turns), all.right_turns, thousandths(all.right_right, all.right_turns));
        std::fs::create_dir_all(out)?;
        let (l, first) = (learner.field.layout(), learner.field.declaration.carry_first());
        let mut text = String::from("circle\tscan\tturns\ts_positive\tbias\tspread\n");
        for k in 0..c {
            let spread = if all.circle_count[k] == 0 { 0 } else { (all.circle_square[k] / u128::from(all.circle_count[k])).isqrt() };
            text.push_str(&format!("{k}\t{}\t{}\t{}\t{}\t{spread}\n", if (first + k) % 2 == 0 { "left" } else { "right" }, all.circle_turns[k], all.circle_right[k], learner.field.theta[l.carry_bias + k]));
        }
        write_new(&out.join("hands.tsv"), text.as_bytes())?;
        // [the lead, November 22, the chirality pass's third read] Each circle's row of the turn chart `Q` (`D` words on the material's grain,
        // little-endian), so a ruler reads which circles' rows stand near which.
        let dw = learner.field.declaration.width;
        let rows_q: Vec<u8> = learner.field.theta[l.carry..l.carry + c * dw].iter().flat_map(|v| v.to_le_bytes()).collect();
        write_new(&out.join("carry_rows.i32"), &rows_q)?;
    }
    // [the lead, November 22, the chirality pass] The word `moves` among the settings: each known site's pumped-circle moves by kind and hand
    // ([`holonics_engine::field::Constitution::strand_moves`]), written to `OUT/moves.tsv` (`row`, `group`, `place`, `class`, then turn+,
    // turn−, shear+, shear−, lock+, lock−, flip+, flip− over every tick and circle), no code read.
    if let Some(at) = settings.iter().position(|(n, _)| n == "moves") {
        settings.remove(at);
        let moves: Vec<Vec<[u32; 8]>> = rows.par_iter().map(|(_, classes)| learner.field.strand_moves(classes, true).map_err(|e| e.to_string())).collect::<std::result::Result<_, _>>()?;
        std::fs::create_dir_all(out)?;
        let mut text = String::new();
        for (r, ((group, classes), m)) in rows.iter().zip(&moves).enumerate() {
            for (t, counts) in m.iter().enumerate() {
                text.push_str(&format!("{r}\t{group}\t{t}\t{}\t{}\n", classes[t], counts.iter().map(u32::to_string).collect::<Vec<_>>().join("\t")));
            }
        }
        write_new(&out.join("moves.tsv"), text.as_bytes())?;
        println!("REACH_MOVES rows={} ms={}", rows.len(), started.elapsed().as_millis());
    }
    // [the lead, November 22, G-R4] The word `lanes` among the settings: each lane's root mean square in the states after every tick, over
    // every site of every row, one `REACH_LANE` line a tick and lane (on the state's `2^(−16)`, and its power of two's place), no code read.
    if let Some(at) = settings.iter().position(|(n, _)| n == "lanes") {
        settings.remove(at);
        let squares: Vec<Vec<Vec<(u128, u64)>>> = rows.par_iter().map(|(_, classes)| learner.field.strand_lane_squares(classes, true).map_err(|e| e.to_string())).collect::<std::result::Result<_, _>>()?;
        let (ticks, lanes) = (squares.first().map_or(0, Vec::len), learner.field.declaration.lanes);
        for t in 0..ticks {
            for j in 0..lanes {
                let (sq, n) = squares.iter().fold((0u128, 0u64), |(a, b), r| (a + r[t][j].0, b + r[t][j].1));
                let rms = (sq / u128::from(n.max(1))).isqrt();
                println!("REACH_LANE tick={t} lane={j} coordinates={n} rms={rms} rms_place={}", if rms == 0 { "-".to_string() } else { rms.ilog2().to_string() });
            }
        }
    }
    let mut codes: Vec<Vec<Vec<i64>>> = Vec::new();
    for (name, friction) in &settings {
        let mut field = learner.field.clone();
        field.ruler_friction = friction.clone();
        // [the lead, November 21, the precision pass] `round:g`: every material entry on its family's grain `b` rounded to `2^(−g)` where `b > g`
        // (G-W1); `state:g`: every state rounded to `2^(−g)` after each tick (G-W3, [`holonics_engine::field::Constitution::ruler_state_grain`]).
        if let Some(g) = name.strip_prefix("round:") {
            let g: u32 = g.parse()?;
            let families = field.families_all();
            let mut grain = vec![0u32; field.material_len()];
            for &(start, len, b) in &families {
                grain[start..start + len].fill(b);
            }
            for (v, &b) in field.material_mut().zip(&grain) {
                if b > g {
                    let k = b - g;
                    *v = i32::try_from(holonics_engine::field::release(i128::from(*v), k) << k).map_err(|_| "a rounded entry past 32 bits")?;
                }
            }
        }
        // [the lead, November 22, the second precision pass (G-R1)] `places:g₀,g₁,…`: one count a family of `families_all`, each entry on its
        // family's grain `b` rounded to `2^(−g)` where `b > g`, and a family whose count is `-` kept as it is.
        if let Some(list) = name.strip_prefix("places:") {
            let families = field.families_all();
            let counts: Vec<&str> = list.split(',').collect();
            if counts.len() != families.len() {
                return Err("a places setting that is not one count a family".into());
            }
            let mut drop = vec![0u32; field.material_len()];
            for (&(start, len, b), c) in families.iter().zip(&counts) {
                if *c != "-" {
                    drop[start..start + len].fill(b.saturating_sub(c.parse::<u32>()?));
                }
            }
            for (v, &k) in field.material_mut().zip(&drop) {
                if k > 0 {
                    *v = i32::try_from(holonics_engine::field::release(i128::from(*v), k) << k).map_err(|_| "a rounded entry past 32 bits")?;
                }
            }
        }
        if let Some(g) = name.strip_prefix("state:") {
            field.ruler_state_grain = Some(g.parse()?);
        }
        // [the lead, November 24, the calendar record §6 item 1, a read before the fade is a law] `fade:FROM:MILLI`: every turned ring of
        // period `FROM` or more faded at `γ = 2^(MILLI/1000)` e-folds a radian of its own turn ([`holonics_engine::field::Constitution::set_ruler_fade`]),
        // the others at one; on the host, where this read runs.
        if name == "skin:places" {
            field.ruler_skin_places = true;
        }
        // [theory, November 25, what a region hands the next] `cut:C:MASK`: every place from `C` on read as the region that begins at `C`
        // would read it, but for what `MASK` lets across the cut ([`holonics_engine::field::Constitution::ruler_cut`]: 1 the rings' moments
        // and the opening's rows, 2 the carry circles' charges, 4 the near field and the strand mates, 8 a definite receiver's octave
        // crowds, 16 the level's epochs, 32 the sites in a receiver's probed classes, 64 every site to an open place, 128 the octave crowds
        // to an open place, 256 the sites before the cut held at their opening, 512 the class hairs: each probed class's definite sites before the cut heard as
        // one term at no fade, 1024 at the law's weights, 2048 only where coherent, the rest by address); a row of fewer than `C + 2` places is read by the law.
        // `from:C`: the row's places from `C` on read as a passage of their own, the places before it coded zero: the control `cut:C:0`
        // is held to (`cut:C:95` is the law's bits).
        let mut from = 0usize;
        if let Some(cm) = name.strip_prefix("cut:") {
            let (c, mask) = cm.split_once(':').ok_or("a cut setting that is not cut:C:MASK")?;
            field.ruler_cut = Some((c.parse()?, mask.parse()?));
        }
        if let Some(c) = name.strip_prefix("from:") {
            from = c.parse()?;
        }
        if let Some(fm) = name.strip_prefix("fade:") {
            let words: Vec<&str> = fm.split(':').collect();
            let (from, milli, to) = match words[..] {
                [f, m] => (f, m, None),
                [f, m, t] => (f, m, Some(t)),
                _ => return Err("a fade setting that is not fade:FROM:MILLI or fade:FROM:MILLI:TO".into()),
            };
            let ell = holonics_engine::field::div_nearest(i128::from(milli.parse::<i64>()?) << holonics_engine::field::MATERIAL_BITS, 1000);
            let to = to.map_or(Ok(usize::MAX), str::parse)?;
            field.set_ruler_fade_between(from.parse()?, to, i32::try_from(ell).map_err(|_| "a fade past its chart")?).map_err(|e| e.to_string())?;
        }
        // [the lead, November 22, G-R4] `lane:j:h`: lane `j` of every site's state rounded after each tick to the power of two `h` places under
        // that site's own lane's root mean square; `lanept:j:k`: the same lane with `k` places dropped from the state's `2^(−16)`. The other
        // lanes are kept.
        for (prefix, relative) in [("lane:", true), ("lanept:", false)] {
            if let Some(jh) = name.strip_prefix(prefix) {
                let (j, h) = jh.split_once(':').ok_or("a lane setting that is not lane:j:h or lanept:j:k")?;
                field.ruler_lane_grain = Some((j.parse()?, h.parse()?, relative));
            }
        }
        // [measurement] The pairs a cut lets across, counted over the setting's forwards (every tick's row): its sites heard one by one
        // past the near field, and its hairs.
        holonics_engine::field::CUT_PAIRS_FAR.store(0, std::sync::atomic::Ordering::Relaxed);
        holonics_engine::field::CUT_PAIRS_HAIR.store(0, std::sync::atomic::Ordering::Relaxed);
        let c: Vec<Vec<i64>> = rows
            .par_iter()
            .map(|(_, classes)| {
                // A row too short for the cut, or for a passage of its own past `from`, is read by the law.
                let mut field = field.clone();
                field.ruler_cut = field.ruler_cut.filter(|&(c, _)| c >= 1 && c + 2 <= classes.len());
                let from = if from + 2 <= classes.len() { from } else { 0 };
                let codes = field.strand_codes(&classes[from..], true).map_err(|e| e.to_string())?;
                Ok::<_, String>(std::iter::repeat_n(0, from).chain(codes).collect())
            })
            .collect::<std::result::Result<_, _>>()?;
        let mut by: std::collections::BTreeMap<String, (i128, usize)> = std::collections::BTreeMap::new();
        for ((group, _), cs) in rows.iter().zip(&c) {
            for g in [group.split(':').next().unwrap_or("").to_string(), "all".to_string()] {
                let e = by.entry(g).or_insert((0, 0));
                e.0 += cs.iter().skip(1).map(|&v| i128::from(v)).sum::<i128>();
                e.1 += cs.len() - 1;
            }
        }
        for (g, (sum, n)) in &by {
            println!("REACH setting={name} group={g} places={n} nats_millionths={} ms={}", ((*sum * holonics_engine::field::ln2_face() * 1_000_000) >> (holonics_engine::field::READ_BITS + holonics_engine::field::LN2_BITS)) / (*n).max(1) as i128, started.elapsed().as_millis());
        }
        if field.ruler_cut.is_some() {
            println!("REACH_PAIRS setting={name} far={} hairs={}", holonics_engine::field::CUT_PAIRS_FAR.load(std::sync::atomic::Ordering::Relaxed), holonics_engine::field::CUT_PAIRS_HAIR.load(std::sync::atomic::Ordering::Relaxed));
        }
        codes.push(c);
    }
    std::fs::create_dir_all(out)?;
    let mut lines = String::new();
    for (r, (group, classes)) in rows.iter().enumerate() {
        for t in 0..classes.len() {
            lines.push_str(&format!("{r}\t{group}\t{t}"));
            for c in &codes {
                lines.push_str(&format!("\t{}", c[r][t]));
            }
            lines.push('\n');
        }
    }
    write_new(&out.join("codes.tsv"), lines.as_bytes())?;
    write_new(&out.join("settings.tsv"), settings.iter().map(|(n, _)| format!("{n}\n")).collect::<String>().as_bytes())?;
    println!("REACH_DONE rows={} settings={} ms={}", rows.len(), settings.len(), started.elapsed().as_millis());
    Ok(())
}

/// [measurement; the lead, November 18, the frontier record §5] `read-far UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA ROWS ROWS_SHA STATE
/// STATE_SHA`: **what a place at the frontier takes from the far field, by what it hears there**. Each row of `ROWS`
/// (`group:known:n<TAB>known text<TAB>next symbol`) is a region whose places are known but its last, the next symbol's, which alone is
/// open (the frontier's state, [`holonics_engine::passage::frontier_state_of`]). The rows are read three times on the host's realization:
/// with the law (an open receiver hears every definite site past its near field), with a definite receiver's far field in its place
/// (its probe's classes sharply and each octave's crowd), and with the near field alone; then with the law's hearing in one read and the
/// level unheard (`4`), and the same with every known place hearing only what stands before it (`3`)
/// ([`holonics_engine::field::Constitution::ruler_far`]). One line a setting and a group (the label up to its second colon): the rows and
/// the written symbol's code in millionths of a nat a place. A ruler's forward: the state is read, never written, and nothing is returned.
/// Why: a read that compares every place of a region at its own frontier needs a second, open place at every place; what that place must
/// hear far (every site before it, or a few crowds) sets the read's cost, and this reads it before the read is built.
pub fn read_far(args: &[String]) -> Result<()> {
    let only = args.len() == 12 && args[11] == "strand";
    let level = args.len() == 12 && args[11] == "level";
    if args.len() != 11 && !only && !level {
        return Err("read-far UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA ROWS ROWS_SHA STATE STATE_SHA [strand | level]".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("read-far")?;
    let units = units_of(&args[1], &args[2])?;
    let _keys = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?, units)?;
    let table = String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?;
    let mut learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[9], &args[10], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    let unescape = |t: &str| t.replace("\\n", "\n");
    let mut rows: Vec<(String, OwnedRegion)> = Vec::new();
    for line in table.lines() {
        let w: Vec<&str> = line.split('\t').collect();
        let [label, known, next] = w[..] else { return Err("a row that is not its label, its known text and its next symbol".into()) };
        let mut classes = codec.encode(unescape(known).as_bytes())?;
        let target = codec.encode(unescape(next).as_bytes())?;
        if classes.is_empty() || target.is_empty() {
            return Err("a row with no known place or no next symbol".into());
        }
        classes.push(target[0]);
        let mut open = vec![false; classes.len()];
        *open.last_mut().expect("a region of two places or more") = true;
        let group: String = label.splitn(3, ':').take(2).collect::<Vec<_>>().join(":");
        rows.push((group, OwnedRegion::plain(classes, open)));
    }
    if rows.is_empty() {
        return Err("no row".into());
    }
    let nats = |code: i128, n: usize| ((code * holonics_engine::field::ln2_face() * 1_000_000) >> 50) / n.max(1) as i128;
    // [the lead, November 18] A last pair of lines reads the law (printed as far=10) and the known stream (far=13) with the open place's
    // clock left bare at every tick (`Constitution::bare_stretch`): what its re-read from its own face is worth at the frontier.
    // [the lead, November 18] The lines far=7 and far=8 read the known stream with its carry circles at rest and with its plain strand
    // contacts unmet: what the strand's own contacts carry to the frontier. The line far=9 reads it with its odd contacts and its circles
    // from the right facing the past (`Region::past`). A last word `strand` reads these three and the known stream alone.
    // [the lead, November 18] A last word `level` reads by which path the level reaches the frontier ([`Constitution::ruler_level`]): the
    // law's hearing in one read without the level and with it (far=4, far=5); with no open place taking a prolonged row (far=21), every
    // place reading the epoch before its own (far=22), the open places alone doing so (far=23); the known stream (far=3), with the level
    // made one-sided as designed (far=24) and with the law's level over its ticks (far=25).
    for setting in if only { vec![3u8, 7, 8, 9] } else if level { vec![4u8, 5, 21, 22, 23, 3, 24, 25] } else { vec![0u8, 1, 2, 3, 4, 5, 6, 7, 8, 10, 13] } {
        let far = setting;
        (learner.field.ruler_far, learner.field.ruler_level, learner.field.bare_stretch) = match setting {
            21..=23 => (5, setting - 20, false),
            24 | 25 => (3, setting - 20, false),
            s => (s % 10, 0, s >= 10),
        };
        let mut groups: std::collections::BTreeMap<String, (i128, usize)> = std::collections::BTreeMap::new();
        // (a few hundred regions a call, so no call holds every region's forward at once)
        for chunk in rows.chunks(256) {
            let views: Vec<_> = chunk.iter().map(|(_, r)| view_of(r)).collect();
            let faces = holonics_engine::realization::Realization::read_faces(&mut holonics_engine::realization::Host, &learner.field, &views).map_err(|e| e.to_string())?;
            for ((group, region), face) in chunk.iter().zip(&faces) {
                let at = region.classes.len() - 1;
                let f = face[at].as_ref().ok_or("a frontier place that carries no face")?;
                let slot = groups.entry(group.clone()).or_insert((0, 0));
                slot.0 += i128::from(holonics_engine::field::ratio_code(f.masses[region.classes[at]], f.total));
                slot.1 += 1;
            }
        }
        for (group, &(code, n)) in &groups {
            println!("FAR far={far} group={group} rows={n} code={}", nats(code, n));
        }
        let (code, n) = groups.values().fold((0i128, 0usize), |(c, k), &(gc, gn)| (c + gc, k + gn));
        println!("FAR far={far} group=all rows={n} code={} ms={}", nats(code, n), started.elapsed().as_millis());
    }
    Ok(())
}

/// [measurement; the lead, November 18, the boundary chart] `read-chart UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA ROWS ROWS_SHA STATE
/// STATE_SHA [KNOWN]`: **a passage read at its boundary, every place at once** ([`holonics_engine::field::Constitution::chart_faces`]).
/// Each row of `ROWS` (`group:known:n<TAB>known text<TAB>next symbol`, [`read_far`]'s table) whose `known` is `KNOWN` (448 where none is
/// given) is one passage, its known text and its next symbol; the chart's forward reads the density at every place from what stands
/// before it. One line a group and an octave of places known (the written symbol's code in millionths of a nat a place, and the places),
/// and one a group for the passage's last place alone, the place [`read_far`] reads as a frontier's region. On the host's threads; the
/// state is read, never written. Why: before anything is compared under the chart, this is what a state compared two-sidedly and at
/// the frontier reads through it, the level a first pass under it starts from.
pub fn read_chart(args: &[String]) -> Result<()> {
    if args.len() != 11 && args.len() != 12 {
        return Err("read-chart UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA ROWS ROWS_SHA STATE STATE_SHA [KNOWN]".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("read-chart")?;
    let units = units_of(&args[1], &args[2])?;
    let _keys = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?, units)?;
    let table = String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?;
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[9], &args[10], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    let known = args.get(11).map_or("448", String::as_str);
    let unescape = |t: &str| t.replace("\\n", "\n");
    let mut rows: Vec<(String, Vec<usize>)> = Vec::new();
    for line in table.lines() {
        let w: Vec<&str> = line.split('\t').collect();
        let [label, text, next] = w[..] else { return Err("a row that is not its label, its known text and its next symbol".into()) };
        let parts: Vec<&str> = label.splitn(3, ':').collect();
        if parts.get(1).copied() != Some(known) {
            continue;
        }
        let mut classes = codec.encode(unescape(text).as_bytes())?;
        classes.push(*codec.encode(unescape(next).as_bytes())?.first().ok_or("a row with no next symbol")?);
        rows.push((parts[0].to_string(), classes));
    }
    if rows.is_empty() {
        return Err("no row of that count of known places".into());
    }
    use rayon::prelude::*;
    let field = &learner.field;
    // Each passage's codes by place, on the host's threads (a reading; each passage its own forward).
    let codes: Vec<std::result::Result<Vec<i64>, String>> = rows
        .par_iter()
        .map(|(_, classes)| {
            let faces = field.chart_faces(classes).map_err(|e| e.to_string())?;
            Ok(faces.iter().zip(classes).map(|(f, &c)| holonics_engine::field::ratio_code(f.masses[c], f.total)).collect())
        })
        .collect();
    let nats = |code: i128, n: usize| ((code * holonics_engine::field::ln2_face() * 1_000_000) >> 50) / n.max(1) as i128;
    let octave = |t: usize| if t == 0 { 0 } else { usize::BITS - t.leading_zeros() };
    let mut by: std::collections::BTreeMap<(String, u32), (i128, usize)> = std::collections::BTreeMap::new();
    let mut last: std::collections::BTreeMap<String, (i128, usize)> = std::collections::BTreeMap::new();
    for ((group, _), row) in rows.iter().zip(codes) {
        let row = row?;
        for (t, &c) in row.iter().enumerate() {
            for g in [group.as_str(), "all"] {
                let slot = by.entry((g.to_string(), octave(t))).or_insert((0, 0));
                (slot.0, slot.1) = (slot.0 + i128::from(c), slot.1 + 1);
            }
        }
        for g in [group.as_str(), "all"] {
            let slot = last.entry(g.to_string()).or_insert((0, 0));
            (slot.0, slot.1) = (slot.0 + i128::from(*row.last().expect("a passage of a place or more")), slot.1 + 1);
        }
    }
    for ((group, o), &(code, n)) in &by {
        let span = match *o {
            0 => "0".to_string(),
            1 => "1".to_string(),
            o => format!("{}-{}", 1usize << (o - 1), (1usize << o) - 1),
        };
        println!("CHART group={group} known={span} places={n} code={}", nats(code, n));
    }
    for (group, &(code, n)) in &last {
        println!("CHART_LAST group={group} known={known} rows={n} code={}", nats(code, n));
    }
    println!("CHART_DONE passages={} ms={}", rows.len(), started.elapsed().as_millis());
    Ok(())
}

/// [measurement; the lead, November 17, the record of the dwell §19] `read-level UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA FORMS
/// FORMS_SHA STATE STATE_SHA OUT [links]`: **a region's level, written out for a ruler**. Each row of `FORMS` (`label<TAB>prompt<TAB>run`) is
/// one region, its prompt known and its run open. `OUT/level.tsv` takes a line a region: its label, its sites, the epochs' anchors and
/// each place's news on the code's grain (`2^(−20)` bits); `OUT/coarse.i32` takes each epoch's read after the level's last tick, epoch
/// after epoch in the regions' order (`D₁` entries on `2^(−16)`); `OUT/dims.tsv` names `D₁`. On the host's threads; the state is read,
/// never written.
///
/// [measurement; the lead, November 17, the level's design record §6] With `links`, every link of the level's own equation is written
/// beside them ([`holonics_engine::field::Constitution::level_links`]), place after place and epoch after epoch in the regions' order:
/// `phase.i64` (`H` a place, on `2^(−30)`), `read.i32` (the place's read at the split, `D₀` on `2^(−16)`), `moment.i64` (`H D₀` an epoch),
/// `restricted.i64` (`D₁` an epoch, before the level's ticks), `prolonged.i64` (`D₀` a place) and `covector.i64` (`D₀` a place on
/// `2^(−24)`, what the region's reverse holds at the level's locus); `dims.tsv` then names `H` and `D₀` too.
pub fn read_level(args: &[String]) -> Result<()> {
    let usage = "read-level UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA FORMS FORMS_SHA STATE STATE_SHA OUT [links]";
    let links = match args.len() {
        12 => false,
        13 if args[12] == "links" => true,
        _ => return Err(usage.into()),
    };
    let started = std::time::Instant::now();
    refuse_variables("read-level")?;
    let units = units_of(&args[1], &args[2])?;
    let _keys = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?, units)?;
    let table = String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?;
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[9], &args[10], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let out = Path::new(&args[11]);
    let unescape = |t: &str| t.replace("\\n", "\n");
    let mut work: Vec<(String, OwnedRegion)> = Vec::new();
    for line in table.lines() {
        let w: Vec<&str> = line.split('\t').collect();
        if w.len() < 3 {
            return Err("a level row that is not label, prompt and run".into());
        }
        let (p, r) = (codec.encode(unescape(w[1]).as_bytes())?, codec.encode(unescape(w[2]).as_bytes())?);
        let mut classes = p.clone();
        classes.extend_from_slice(&r);
        let mut open = vec![false; classes.len()];
        open[p.len()..].fill(true);
        work.push((w[0].to_string(), OwnedRegion::plain(classes, open)));
    }
    std::fs::create_dir(out)?;
    let create = |name: &str| -> Result<std::io::BufWriter<std::fs::File>> { Ok(std::io::BufWriter::new(std::fs::OpenOptions::new().write(true).create_new(true).open(out.join(name))?)) };
    let (mut lines, mut coarse) = (create("level.tsv")?, create("coarse.i32")?);
    let mut link_files = if links { Some((create("phase.i64")?, create("read.i32")?, create("moment.i64")?, create("restricted.i64")?, create("prolonged.i64")?, create("covector.i64")?)) } else { None };
    let (mut width, mut harmonics, mut fine) = (0usize, 0usize, 0usize);
    // Regions in blocks, so that what is held before it is written stays bounded; rows in the table's order.
    for block in work.chunks(2048) {
        let traces: Vec<_> = block
            .par_iter()
            .map(|(_, region)| if links { learner.field.level_links(&view_of(region)) } else { learner.field.level_trace(&view_of(region)) }.map_err(|e| e.to_string()))
            .collect();
        for ((label, region), trace) in block.iter().zip(traces) {
            let t = trace?.ok_or("a field without a level")?;
            let (sites, epochs) = (region.classes.len(), t.anchors.len().max(1));
            width = t.coarse_read.len() / epochs;
            let list = |v: &mut dyn Iterator<Item = String>| v.collect::<Vec<_>>().join(",");
            writeln!(lines, "{label}\t{sites}\t{}\t{}", list(&mut t.anchors.iter().map(usize::to_string)), list(&mut t.news.iter().map(i64::to_string)))?;
            for v in &t.coarse_read {
                coarse.write_all(&v.to_le_bytes())?;
            }
            if let Some((phase, read, moment, restricted, prolonged, covector)) = link_files.as_mut() {
                harmonics = t.phase.len() / sites;
                fine = t.read.len() / sites;
                if t.covector.len() != sites * fine || t.prolonged.len() != sites * fine || t.moment.len() != epochs * harmonics * fine || t.restricted.len() != epochs * width {
                    return Err("a level's links of another shape than its region".into());
                }
                for v in &t.phase {
                    phase.write_all(&v.to_le_bytes())?;
                }
                for v in &t.read {
                    read.write_all(&v.to_le_bytes())?;
                }
                for v in &t.moment {
                    moment.write_all(&v.to_le_bytes())?;
                }
                for v in &t.restricted {
                    restricted.write_all(&v.to_le_bytes())?;
                }
                for v in &t.prolonged {
                    prolonged.write_all(&v.to_le_bytes())?;
                }
                for v in &t.covector {
                    covector.write_all(&v.to_le_bytes())?;
                }
            }
        }
    }
    lines.flush()?;
    coarse.flush()?;
    if let Some((mut a, mut b, mut c, mut d, mut e, mut f)) = link_files {
        a.flush()?;
        b.flush()?;
        c.flush()?;
        d.flush()?;
        e.flush()?;
        f.flush()?;
    }
    write_new(&out.join("dims.tsv"), if links { format!("coarse\t{width}\nharmonics\t{harmonics}\nfine\t{fine}\n") } else { format!("coarse\t{width}\n") }.as_bytes())?;
    println!("LEVEL_DONE regions={} links={links} threads={} ms={}", work.len(), rayon::current_num_threads(), started.elapsed().as_millis());
    Ok(())
}

/// [measurement; the lead, November 23, the level's receipt record §5] `read-strand-cut ... OUT moments`: each open place's retarded
/// cavity moment `[n][2M]` (`OUT/moments.i64`, rows in the table's order) and each mode's ring period (`OUT/periods.tsv`), with `OUT/dims.tsv`
/// naming `M` ([`holonics_engine::field::Constitution::strand_open_moments`]). The moments are the known stream's alone, so `past` does not
/// enter. On the host's threads; the state is read, never written. The directory is private.
fn read_strand_moments(args: &[String]) -> Result<()> {
    let started = std::time::Instant::now();
    refuse_variables("read-strand-cut")?;
    let units = units_of(&args[1], &args[2])?;
    let _keys = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?, units)?;
    let table = String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?;
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[9], &args[10], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let out = Path::new(&args[11]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let unescape = |t: &str| t.replace("\\n", "\n");
    let mut rows: Vec<Vec<usize>> = Vec::new();
    for line in table.lines() {
        let w: Vec<&str> = line.split('\t').collect();
        let [_, known, next] = w[..] else { return Err("a row that is not its label, its known text and its next symbol".into()) };
        let mut classes = codec.encode(unescape(known).as_bytes())?;
        classes.extend(codec.encode(unescape(next).as_bytes())?.into_iter().take(1));
        rows.push(classes);
    }
    let field = &learner.field;
    let read: Vec<(Vec<i64>, Vec<usize>)> = rows.par_iter().map(|classes| field.strand_open_moments(classes).map_err(|e| e.to_string())).collect::<std::result::Result<_, _>>()?;
    std::fs::create_dir_all(out)?;
    let bytes: Vec<u8> = read.iter().flat_map(|(m, _)| m.iter().flat_map(|v| v.to_le_bytes())).collect();
    write_new(&out.join("moments.i64"), &bytes)?;
    let periods = read.first().map(|(_, p)| p.clone()).unwrap_or_default();
    write_new(&out.join("periods.tsv"), periods.iter().map(|p| format!("{p}\n")).collect::<String>().as_bytes())?;
    write_new(&out.join("dims.tsv"), format!("modes\t{}\n", periods.len()).as_bytes())?;
    println!("STRAND_MOMENTS rows={} places={} modes={} ms={}", rows.len(), rows.iter().map(Vec::len).sum::<usize>(), periods.len(), started.elapsed().as_millis());
    Ok(())
}

/// [measurement; the lead, November 23, the level's receipt record §5] `read-strand-cut UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA ROWS
/// ROWS_SHA STATE STATE_SHA OUT [past] [links] [face]`: **which epoch each place of a strand reads, written out for a ruler**. Each row of `ROWS`
/// (`read-far`'s table, as [`read_strand_states`] reads it) is read whole as a passage by two streams; `OUT/cut.tsv` takes a line a row:
/// its index, its places, the known stream's anchors, and the epoch each open place reads (`-` where it reads none), comma-separated;
/// `OUT/powers.tsv` a line a site (`row`, `site` of the `2n`, the squared length of the row the level added there, of the state it was
/// added to; [`holonics_engine::field::Constitution::strand_cut_read`]). With `links`, the level link by link
/// ([`holonics_engine::field::Constitution::strand_level_links`]): `OUT/restricted.i64` and `OUT/coarse.i32` each epoch's restricted state
/// before the level's ticks and its read after them (`D₁` an epoch, epochs in the cut's order), `OUT/row.i32` and `OUT/joined.i32` each
/// open place's added row and the state it made (`D₀` a place, lane charts on `2^(−16)`), `OUT/lambda.i64` the covector the reverse
/// holds at that state (`D₀` a place on `2^(−24)`), and `OUT/dims.tsv` names `D₀` and `D₁`. On the host's threads; the state is read, never written. The directory
/// is private: its rows are the passage's places.
pub fn read_strand_cut(args: &[String]) -> Result<()> {
    let words: Vec<&str> = args.iter().skip(12).map(String::as_str).collect();
    // [the lead, November 26] `past face`: each open place's code at the level's own face beside the cut (`OUT/face.tsv`).
    let face = words.last() == Some(&"face");
    let words: Vec<&str> = if face { words[..words.len() - 1].to_vec() } else { words };
    let (past, links) = match words[..] {
        [] => (false, false),
        ["past"] => (true, false),
        ["links"] => (false, true),
        ["past", "links"] => (true, true),
        ["moments"] => {
            return read_strand_moments(args);
        }
        _ => return Err("read-strand-cut UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA ROWS ROWS_SHA STATE STATE_SHA OUT [past] [links]".into()),
    };
    if args.len() < 12 {
        return Err("read-strand-cut UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA ROWS ROWS_SHA STATE STATE_SHA OUT [past] [links]".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("read-strand-cut")?;
    let units = units_of(&args[1], &args[2])?;
    let _keys = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?, units)?;
    let table = String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?;
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[9], &args[10], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    let out = Path::new(&args[11]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let mut rows: Vec<Vec<usize>> = Vec::new();
    for line in table.lines() {
        let w: Vec<&str> = line.split('\t').collect();
        let [_, known, next] = w[..] else { return Err("a row that is not its label, its known text and its next symbol".into()) };
        let mut classes = codec.encode(&row_octets(known)?)?;
        classes.extend(codec.encode(&row_octets(next)?)?.into_iter().take(1));
        if classes.len() < 2 {
            return Err("a row of fewer than two places".into());
        }
        rows.push(classes);
    }
    let field = &learner.field;
    #[allow(clippy::type_complexity)]
    let cuts: Vec<(Vec<usize>, Vec<Option<usize>>, Vec<(u128, u128)>)> = rows
        .par_iter()
        .map(|classes| field.strand_cut_read(classes, past).map_err(|e| e.to_string()).and_then(|c| c.ok_or_else(|| "a field whose level does not hear a strand".to_string())))
        .collect::<std::result::Result<_, _>>()?;
    std::fs::create_dir_all(out)?;
    let list = |v: &mut dyn Iterator<Item = String>| v.collect::<Vec<_>>().join(",");
    let (mut lines, mut powers) = (String::new(), String::new());
    for (r, (classes, (anchors, source, p))) in rows.iter().zip(&cuts).enumerate() {
        let n = classes.len();
        lines.push_str(&format!("{r}\t{n}\t{}\t{}\n", list(&mut anchors.iter().map(usize::to_string)), list(&mut source[n..].iter().map(|s| s.map_or("-".to_string(), |j| j.to_string())))));
        for (site, (row, state)) in p.iter().enumerate() {
            powers.push_str(&format!("{r}\t{site}\t{row}\t{state}\n"));
        }
    }
    write_new(&out.join("cut.tsv"), lines.as_bytes())?;
    write_new(&out.join("powers.tsv"), powers.as_bytes())?;
    if face {
        // [the lead, November 26, the formal thread's record of nested cycles §9 item 3] The level read at its own face: each open place
        // that reads an epoch, its site of the `2n`, its symbol's code at the prolonged row alone and from the row at rest (on `2^(−20)`
        // bits), on a copy of the field with the receipt's read set; the state is the same.
        let mut faced = learner.field.clone();
        if let Some(sc) = faced.scale.as_deref_mut() {
            sc.receipt = true;
        }
        #[allow(clippy::type_complexity)]
        let read: Vec<Vec<(usize, i64, i64)>> = rows
            .par_iter()
            .map(|classes| faced.strand_level_face(classes, past).map_err(|e| e.to_string()).and_then(|c| c.map(|(_, _, f)| f).ok_or_else(|| "a field whose level does not hear a strand".to_string())))
            .collect::<std::result::Result<_, _>>()?;
        let mut text = String::new();
        for (r, f) in read.iter().enumerate() {
            for (site, code, rest) in f {
                text.push_str(&format!("{r}\t{site}\t{code}\t{rest}\n"));
            }
        }
        write_new(&out.join("face.tsv"), text.as_bytes())?;
    }
    if links {
        // [the lead, November 23] Each epoch's restricted state and its read after the level's ticks, and each open place's row and the
        // state it made, row after row in the table's order.
        #[allow(clippy::type_complexity)]
        let traced: Vec<(Vec<i64>, Vec<i32>, Vec<i32>, Vec<i32>, Vec<i64>)> = rows
            .par_iter()
            .map(|classes| field.strand_level_links(classes, past).map_err(|e| e.to_string()).and_then(|c| c.ok_or_else(|| "a field whose level does not hear a strand".to_string())))
            .collect::<std::result::Result<_, _>>()?;
        let mut files: Vec<Vec<u8>> = vec![Vec::new(); 5];
        for (restricted, coarse, row, joined, locus) in &traced {
            files[4].extend(locus.iter().flat_map(|v| v.to_le_bytes()));
            files[0].extend(restricted.iter().flat_map(|v| v.to_le_bytes()));
            files[1].extend(coarse.iter().flat_map(|v| v.to_le_bytes()));
            files[2].extend(row.iter().flat_map(|v| v.to_le_bytes()));
            files[3].extend(joined.iter().flat_map(|v| v.to_le_bytes()));
        }
        for (name, bytes) in ["restricted.i64", "coarse.i32", "row.i32", "joined.i32", "lambda.i64"].iter().zip(&files) {
            write_new(&out.join(name), bytes)?;
        }
        let coarse_width = field.scale.as_deref().map_or(0, |s| s.coarse.declaration.width);
        write_new(&out.join("dims.tsv"), format!("read\t{}\ncoarse\t{coarse_width}\n", field.declaration.width).as_bytes())?;
    }
    println!("STRAND_CUT rows={} places={} past={past} ms={}", rows.len(), rows.iter().map(Vec::len).sum::<usize>(), started.elapsed().as_millis());
    Ok(())
}
