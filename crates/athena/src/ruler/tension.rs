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
use holonics_engine::codec::Codec;
use holonics_engine::field::Learner;
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
    if args.len() != 12 {
        return Err("read-tension UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA FORMS FORMS_SHA STATE STATE_SHA OUT".into());
    }
    let started = std::time::Instant::now();
    crate::store::refuse_variables("read-tension")?;
    let units = units_of(&args[1], &args[2])?;
    let _keys = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?, units)?;
    let table = String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?;
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[9], &args[10], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
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
    println!("TENSION_LAW places={} ticks={ticks} width={dw} current={m2} products={j2} threads={} ms={}", work.len(), rayon::current_num_threads(), started.elapsed().as_millis());
    let create = |name: &str| -> Result<std::io::BufWriter<std::fs::File>> { Ok(std::io::BufWriter::new(std::fs::OpenOptions::new().write(true).create_new(true).open(out.join(name))?)) };
    let (mut rows, mut lambda, mut read, mut current, mut products) = (create("rows.tsv")?, create("lambda.i64")?, create("read.i32")?, create("current.i64")?, create("products.i64")?);
    let mut written = 0usize;
    // Regions in blocks, so that what is held before it is written stays bounded; rows in the table's order.
    for block in work.chunks(1024) {
        let reads: Vec<std::result::Result<holonics_engine::field::CrossingTension, String>> =
            block.par_iter().map(|(_, _, _, region)| learner.field.crossing_tension(&view_of(region)).map_err(|e| e.to_string())).collect();
        for ((label, place, site, _), tension) in block.iter().zip(reads) {
            let tension = tension?;
            let code = tension.codes[*site].ok_or("an open place without a face")?;
            for k in 0..ticks {
                writeln!(rows, "{label}\t{place}\t{k}\t{code}")?;
                for &v in &tension.lambda[k][site * dw..(site + 1) * dw] {
                    lambda.write_all(&v.to_le_bytes())?;
                }
                for &v in &tension.read[k][site * dw..(site + 1) * dw] {
                    read.write_all(&v.to_le_bytes())?;
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
        println!("TENSION_BLOCK rows={written} ms={}", started.elapsed().as_millis());
    }
    for w in [&mut rows, &mut lambda, &mut read, &mut current, &mut products] {
        w.flush()?;
    }
    println!("TENSION_DONE rows={written} places={} ms={}", work.len(), started.elapsed().as_millis());
    Ok(())
}
