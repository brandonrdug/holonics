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
    let usage = "read-tension UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA FORMS FORMS_SHA STATE STATE_SHA OUT [all] [carry=MILLI]";
    if args.len() < 12 || args.len() > 14 {
        return Err(usage.into());
    }
    let (mut all, mut carry) = (false, None);
    for word in &args[12..] {
        match (word.as_str(), word.strip_prefix("carry=")) {
            ("all", _) => all = true,
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
            work.push((label.to_string(), j, p.len() + j, OwnedRegion::plain(classes.clone(), open)));
        }
    }
    if work.is_empty() {
        return Err("a tension table of no places".into());
    }
    let d = learner.field.declaration;
    let (dw, m2, j2, ticks) = (d.width, 2 * d.heads * d.modes, 2 * d.triads, d.ticks);
    std::fs::create_dir(out)?;
    write_new(&out.join("dims.tsv"), format!("lambda\t{dw}\nread\t{dw}\ncurrent\t{m2}\nproducts\t{j2}\nticks\t{ticks}\n").as_bytes())?;
    println!("TENSION_LAW places={} ticks={ticks} width={dw} current={m2} products={j2} carry={} threads={} ms={}", work.len(), carry.map_or("-".to_string(), |g| g.to_string()), rayon::current_num_threads(), started.elapsed().as_millis());
    // The locks' temperatures as the state holds them: `log₂ T` on the material's grain, one a head and receiver kind (a class receiver, a listener).
    let temper = learner.field.layout().temper;
    println!("TENSION_TEMPER log2_on_2^-24 {}", (0..2 * d.heads).map(|k| learner.field.theta[temper + k].to_string()).collect::<Vec<_>>().join(" "));
    let create = |name: &str| -> Result<std::io::BufWriter<std::fs::File>> { Ok(std::io::BufWriter::new(std::fs::OpenOptions::new().write(true).create_new(true).open(out.join(name))?)) };
    let (mut rows, mut lambda, mut read, mut current, mut products) = (create("rows.tsv")?, create("lambda.i64")?, create("read.i32")?, create("current.i64")?, create("products.i64")?);
    let (mut chart, mut shares) = if all { (Some(create("chart.i32")?), Some(create("shares.tsv")?)) } else { (None, None) };
    // With `all`, each site's value word beside its chart (`value.i64`, `2M` entries on `2^(−16)`): what the site offers a row that meets it.
    let mut value = if all { Some(create("value.i64")?) } else { None };
    // The open place's whole face, a record a place in the table's order (`faces.i64`, the code of each of the `A` classes on `2^(−20)` bits).
    let mut faces = create("faces.i64")?;
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
    for w in [&mut rows, &mut lambda, &mut read, &mut current, &mut products, &mut faces] {
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
