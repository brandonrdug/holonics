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
        let reads: Vec<std::result::Result<holonics_engine::field::CrossingTension, String>> =
            regions.par_iter().map(|(_, region)| learner.field.crossing_tension(&view_of(region)).map_err(|e| e.to_string())).collect();
        for (r, ((slice, region), tension)) in regions.iter().zip(reads).enumerate() {
            let tension = tension?;
            for site in 0..region.classes.len() {
                let open = region.unresolved[site];
                if !open && site % every != 0 {
                    continue;
                }
                let code = if open { tension.codes[site].ok_or("an open place without a face")? } else { -1 };
                for k in 0..ticks {
                    writeln!(rows, "{}\t{done}\t{r}\t{site}\t{k}\t{}\t{}\t{code}", names[*slice], u8::from(open), region.classes[site])?;
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
                    writeln!(temper, "{}\t{done}\t{r}\t{i}\t{k}\t{h}\t{dl}", names[*slice])?;
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
            Some(_) => return Err("a forms row whose opening is not `suffix` or `first`".into()),
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
    if args.len() != 13 && args.len() != 14 {
        return Err("write-next UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA FORMS FORMS_SHA RUN OUT STATE STATE_SHA [WINDOW]".into());
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
    let unescape = |t: &str| t.replace("\\n", "\n");
    let escape = |b: &[u8]| String::from_utf8_lossy(b).replace('\n', "\\n").replace('\t', "\\t");
    let mut rows: Vec<(String, Vec<u8>, Vec<usize>, Vec<u8>)> = Vec::new();
    for line in table.lines() {
        let w: Vec<&str> = line.split('\t').collect();
        let [label, prompt, reference] = w[..] else { return Err("a forms row that is not three fields".into()) };
        let bytes = unescape(prompt).into_bytes();
        let classes = codec.encode(&bytes)?;
        if classes.is_empty() {
            return Err("a forms row with an empty prompt".into());
        }
        rows.push((label.to_string(), bytes, classes, unescape(reference).into_bytes()));
    }
    std::fs::create_dir(out)?;
    let void = codec.void();
    let mix = |counter: u64| -> u64 {
        let mut z = seed.wrapping_add(counter.wrapping_mul(0x9E37_79B9_7F4A_7C15));
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    };
    let known = learner.pass.as_ref().is_some_and(|p| p.before);
    let mut written: Vec<Vec<usize>> = vec![Vec::new(); rows.len()];
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
                OwnedRegion { before: known, ..OwnedRegion::plain(classes, open) }
            })
            .collect();
        let views: Vec<_> = regions.iter().map(view_of).collect();
        let faces = realization.read_faces(&learner.field, &views).map_err(|e| e.to_string())?;
        for (k, (face, w)) in faces.iter().zip(written.iter_mut()).enumerate() {
            let f = face.last().and_then(|f| f.as_ref()).ok_or("a written place that carries no face")?;
            let letters = f.total - f.masses[void];
            if letters == 0 {
                return Err("a face with no mass on a letter".into());
            }
            // A keyed uniform under the letters' mass: two draws make its 128 bits.
            let u = ((u128::from(mix(((k as u64) << 24) ^ step as u64)) << 64) | u128::from(mix(((k as u64) << 24) ^ step as u64 ^ (1 << 60)))) % letters;
            let mut acc = 0u128;
            let class = (0..f.masses.len()).filter(|&c| c != void).find(|&c| {
                acc += f.masses[c];
                acc > u
            });
            w.push(class.ok_or("a draw past the letters' mass")?);
        }
    }
    let mut text = String::new();
    for ((label, prompt, _, reference), w) in rows.iter().zip(&written) {
        text.push_str(&format!("{label}\t{}\t{}\t{}\n", escape(prompt), escape(&codec.decode(w)), escape(reference)));
    }
    write_new(&out.join("forms.written"), text.as_bytes())?;
    println!("NEXT_WRITE_DONE rows={} run={run} window={} ms={}", rows.len(), window.map_or("-".to_string(), |n| n.to_string()), started.elapsed().as_millis());
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
    if args.len() != 11 {
        return Err("read-far UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA ROWS ROWS_SHA STATE STATE_SHA".into());
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
    for far in 0..5u8 {
        learner.field.ruler_far = far;
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
