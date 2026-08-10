//! Grade [`holonic_engine::lean_development::read_development`] against mathlib, on six populations
//! at once, with an independent ground truth supplied from outside the crate.
//!
//! ```text
//! cargo run --release --example the_end_closes_the_frame_that_opened_it -- \
//!     <file-list> <ground-truth.tsv> <out-prefix>
//! ```
//!
//! The ground truth is a TSV `path line former name namespace` produced by a reader written from
//! the Lean grammar and **not** from this crate's constants — importing `DECLARATION_FORMERS` as
//! the oracle would grade the reader against itself, which is `CLAUDE.md` §8's tautology rule.
//!
//! Six measurements, each a number a repair either moves or does not:
//!
//! ```text
//! heads       positions the reader opened, against the positions the grammar declares
//! names       of the positions both agree on, how many carry the same name
//! namespace   of those, how many carry the same enclosing namespace
//! glyphs      how often the single-glyph type carriers reach `recruited` at all
//! statements  per former, how many statements run past the `where` that ends them
//! edges       cross-file recruitment landing inside the source's transitive import closure,
//!             against the analytic permutation null over the same target multiset
//! ```
//!
//! Every rate is reported in **basis points of an integer ratio**. No float decides anything here
//! and none is printed.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs;
use std::io::Write;
use std::time::Instant;

use holonic_engine::lean_development::{resolution_candidates, DeclarationGrain, read_development};

/// One declaration, reduced to what the six measurements need.
struct Record {
    file: u32,
    line: u32,
    former: String,
    name: String,
    namespace: String,
    anonymous: bool,
    statement: String,
    statement_runs_past_where: bool,
    recruited: Vec<u32>,
}

fn main() {
    let mut args = std::env::args().skip(1);
    let listing = args.next().expect("file list");
    let truth_path = args.next().expect("ground truth tsv");
    let prefix = args.next().expect("out prefix");

    let paths: Vec<String> = fs::read_to_string(&listing)
        .expect("listing")
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(str::to_owned)
        .collect();
    let file_index: HashMap<&str, u32> = paths
        .iter()
        .enumerate()
        .map(|(index, path)| (path.as_str(), index as u32))
        .collect();

    // ------------------------------------------------------------------ 1. read the corpus
    let mut texts: Vec<String> = Vec::with_capacity(paths.len());
    let mut bytes = 0usize;
    let mut source_lines = 0usize;
    let read_start = Instant::now();
    for path in &paths {
        let text = fs::read_to_string(path).unwrap_or_default();
        bytes += text.len();
        source_lines += text.lines().count();
        texts.push(text);
    }
    let read_nanos = read_start.elapsed().as_nanos();

    // Glyph occurrences in the source, so the recruited figure has a denominator.
    let mut source_glyphs: BTreeMap<char, u64> = BTreeMap::new();
    for text in &texts {
        for glyph in GLYPHS {
            source_glyphs
                .entry(glyph)
                .and_modify(|slot| *slot += text.matches(glyph).count() as u64)
                .or_insert(text.matches(glyph).count() as u64);
        }
    }

    // ------------------------------------------------------------------ 2. the reading
    let mut symbols: HashMap<String, u32> = HashMap::new();
    let mut symbol_text: Vec<String> = Vec::new();
    let mut symbol_occurrences: Vec<u64> = Vec::new();
    let mut records: Vec<Record> = Vec::new();
    let mut imports: Vec<Vec<String>> = Vec::with_capacity(paths.len());
    let mut preamble_kinds = 0usize;
    let mut preamble_occurrences = 0u64;
    let mut steps_total = 0usize;
    let mut bound_glyphs: BTreeMap<String, u64> = BTreeMap::new();

    let parse_start = Instant::now();
    for (file, text) in texts.iter().enumerate() {
        let reading = read_development(text, DeclarationGrain::EveryTopLevelDeclaration);
        preamble_kinds += reading.preamble.len();
        for count in reading.preamble.values() {
            preamble_occurrences += u64::from(*count);
        }
        // The import population is read off the source, not off the reader, so that a preamble
        // repair cannot flatter the edge measurement by changing its own denominator.
        imports.push(imports_of(text));
        for form in &reading.declarations {
            steps_total += form.steps.len();
            let mut recruited: Vec<u32> = Vec::with_capacity(form.recruited.len());
            for (symbol, count) in &form.recruited {
                let id = match symbols.get(symbol.as_str()) {
                    Some(id) => *id,
                    None => {
                        let id = symbol_text.len() as u32;
                        symbols.insert(symbol.clone(), id);
                        symbol_text.push(symbol.clone());
                        symbol_occurrences.push(0);
                        id
                    }
                };
                symbol_occurrences[id as usize] += u64::from(*count);
                recruited.push(id);
            }
            records.push(Record {
                file: file as u32,
                line: form.line as u32,
                former: form.former.clone(),
                name: form.name.clone(),
                namespace: form.namespace_path.join("."),
                anonymous: form.anonymous,
                statement: form.statement.clone(),
                statement_runs_past_where: has_token(&form.statement, "where"),
                recruited,
            });
            for (symbol, count) in &form.local_bindings {
                if symbol.chars().count() == 1 {
                    *bound_glyphs.entry(symbol.clone()).or_insert(0u64) += u64::from(*count);
                }
            }
        }
    }
    let parse_nanos = parse_start.elapsed().as_nanos();

    // ------------------------------------------------------------------ 3. the ground truth
    // path -> line -> (former, name, namespace, statement)
    let mut truth: Vec<BTreeMap<u32, (String, String, String, String)>> =
        vec![BTreeMap::new(); paths.len()];
    let truth_text = fs::read_to_string(&truth_path).expect("ground truth");
    let mut truth_total = 0usize;
    let mut truth_without_example = 0usize;
    let mut truth_anonymous = 0usize;
    for row in truth_text.lines() {
        let cells: Vec<&str> = row.split('\t').collect();
        if cells.len() < 4 {
            continue;
        }
        let Some(file) = file_index.get(cells[0]) else {
            continue;
        };
        let line: u32 = cells[1].parse().unwrap_or(0);
        let former = cells[2].to_owned();
        let name = cells[3].to_owned();
        let namespace = cells.get(4).copied().unwrap_or("").to_owned();
        let statement = cells.get(5).copied().unwrap_or("").to_owned();
        truth_total += 1;
        if former != "example" {
            truth_without_example += 1;
        }
        if name.is_empty() {
            truth_anonymous += 1;
        }
        truth[*file as usize].insert(line, (former, name, namespace, statement));
    }

    let mut head_hit = 0usize;
    let mut head_hit_without_example = 0usize;
    let mut phantom = 0usize;
    let mut name_agree = 0usize;
    let mut name_wrong = 0usize;
    let mut namespace_agree = 0usize;
    let mut namespace_shallow = 0usize;
    let mut namespace_deep = 0usize;
    let mut namespace_other = 0usize;
    let mut anonymous_returned = 0usize;
    let mut missed_by_former: BTreeMap<String, usize> = BTreeMap::new();
    let mut phantom_rows: Vec<String> = Vec::new();
    let mut wrong_name_rows: Vec<String> = Vec::new();
    let mut wrong_namespace_rows: Vec<String> = Vec::new();
    let mut statement_wrong_rows: Vec<String> = Vec::new();
    let mut statement_total: BTreeMap<String, usize> = BTreeMap::new();
    let mut statement_exact: BTreeMap<String, usize> = BTreeMap::new();
    let mut statement_past_where: BTreeMap<String, usize> = BTreeMap::new();

    let mut seen: Vec<BTreeSet<u32>> = vec![BTreeSet::new(); paths.len()];
    for record in &records {
        if record.anonymous {
            anonymous_returned += 1;
        }
        seen[record.file as usize].insert(record.line);
        let Some((former, name, namespace, statement)) = truth[record.file as usize].get(&record.line)
        else {
            phantom += 1;
            if phantom_rows.len() < 400 {
                phantom_rows.push(format!(
                    "{}\t{}\t{}\t{}",
                    paths[record.file as usize], record.line, record.former, record.name
                ));
            }
            continue;
        };
        head_hit += 1;
        if former != "example" {
            head_hit_without_example += 1;
        }
        *statement_total.entry(former.clone()).or_insert(0) += 1;
        if &record.statement == statement {
            *statement_exact.entry(former.clone()).or_insert(0) += 1;
        } else if statement_wrong_rows.len() < 400 {
            statement_wrong_rows.push(format!(
                "{}\t{}\t{}\t{}\t|\t{}",
                paths[record.file as usize], record.line, former, statement, record.statement
            ));
        }
        if record.statement_runs_past_where {
            *statement_past_where.entry(former.clone()).or_insert(0) += 1;
        }
        // An anonymous head agrees when the grammar also calls it anonymous.
        let reader_name = if record.anonymous { "" } else { record.name.as_str() };
        if reader_name == name {
            name_agree += 1;
        } else {
            name_wrong += 1;
            if wrong_name_rows.len() < 400 {
                wrong_name_rows.push(format!(
                    "{}\t{}\t{}\t{}\t{}",
                    paths[record.file as usize], record.line, record.former, name, reader_name
                ));
            }
        }
        if &record.namespace == namespace {
            namespace_agree += 1;
        } else {
            if namespace.starts_with(record.namespace.as_str()) {
                namespace_shallow += 1;
            } else if record.namespace.starts_with(namespace.as_str()) {
                namespace_deep += 1;
            } else {
                namespace_other += 1;
            }
            if wrong_namespace_rows.len() < 400 {
                wrong_namespace_rows.push(format!(
                    "{}\t{}\t{}\t{}\t{}",
                    paths[record.file as usize], record.line, record.name, namespace, record.namespace
                ));
            }
        }
    }
    let mut missed_rows: Vec<String> = Vec::new();
    let mut missed_by_cause: BTreeMap<&str, usize> = BTreeMap::new();
    for (file, rows) in truth.iter().enumerate() {
        for (line, (former, name, _, _)) in rows {
            if seen[file].contains(line) {
                continue;
            }
            *missed_by_former.entry(former.clone()).or_insert(0) += 1;
            let source = texts[file]
                .lines()
                .nth(*line as usize - 1)
                .unwrap_or_default();
            // Which of the six repairs owns this miss, read off the source line itself.
            let cause = if name.is_empty() && former == "instance" {
                "anonymous-instance"
            } else if former == "example" {
                "example-out-of-aperture"
            } else if source.contains('«') {
                "guillemet-name"
            } else if ["nonrec", "meta", "public", "scoped", "local"]
                .iter()
                .any(|word| source.starts_with(&format!("{word} ")))
            {
                "unlisted-modifier"
            } else {
                "other"
            };
            *missed_by_cause.entry(cause).or_insert(0) += 1;
            if missed_rows.len() < 4000 {
                missed_rows.push(format!(
                    "{}\t{line}\t{former}\t{name}\t{cause}\t{source}",
                    paths[file]
                ));
            }
        }
    }

    // ------------------------------------------------------------------ 5. the import closure
    let module_of: HashMap<String, u32> = paths
        .iter()
        .enumerate()
        .filter_map(|(index, path)| module_name(path).map(|name| (name, index as u32)))
        .collect();
    let direct: Vec<Vec<u32>> = imports
        .iter()
        .map(|list| {
            list.iter()
                .filter_map(|name| module_of.get(name).copied())
                .collect()
        })
        .collect();
    let words = paths.len().div_ceil(64);
    let mut closure: Vec<u64> = vec![0u64; words * paths.len()];
    let mut done = vec![false; paths.len()];
    let mut order: Vec<u32> = Vec::with_capacity(paths.len());
    // Iterative post-order over the import DAG.
    for root in 0..paths.len() as u32 {
        if done[root as usize] {
            continue;
        }
        let mut stack: Vec<(u32, usize)> = vec![(root, 0)];
        let mut on_stack: BTreeSet<u32> = BTreeSet::new();
        on_stack.insert(root);
        while let Some((node, cursor)) = stack.pop() {
            if cursor < direct[node as usize].len() {
                let next = direct[node as usize][cursor];
                stack.push((node, cursor + 1));
                if !done[next as usize] && !on_stack.contains(&next) {
                    on_stack.insert(next);
                    stack.push((next, 0));
                }
                continue;
            }
            if !done[node as usize] {
                done[node as usize] = true;
                on_stack.remove(&node);
                order.push(node);
            }
        }
    }
    for node in &order {
        let base = *node as usize * words;
        for next in &direct[*node as usize] {
            let other = *next as usize * words;
            closure[base + (*next as usize / 64)] |= 1u64 << (*next as usize % 64);
            for word in 0..words {
                closure[base + word] |= closure[other + word];
            }
        }
    }
    let inside = |source: u32, target: u32| -> bool {
        let base = source as usize * words;
        closure[base + (target as usize / 64)] & (1u64 << (target as usize % 64)) != 0
    };

    // ------------------------------------------------------------------ 6. cross-file edges
    // Short-name join: every file declaring the bare name is a candidate landing.
    let mut short_files: HashMap<&str, BTreeSet<u32>> = HashMap::new();
    let mut qualified_files: HashMap<String, BTreeSet<u32>> = HashMap::new();
    for record in &records {
        if record.anonymous {
            continue;
        }
        short_files
            .entry(record.name.as_str())
            .or_default()
            .insert(record.file);
        let qualified = if record.namespace.is_empty() {
            record.name.clone()
        } else {
            format!("{}.{}", record.namespace, record.name)
        };
        qualified_files.entry(qualified).or_default().insert(record.file);
    }

    let mut target_count: Vec<u64> = vec![0u64; paths.len()];
    let mut short_total = 0u64;
    let mut short_inside = 0u64;
    for record in &records {
        for id in &record.recruited {
            let symbol = symbol_text[*id as usize].as_str();
            let Some(landing) = short_files.get(symbol) else {
                continue;
            };
            for file in landing {
                if *file == record.file {
                    continue;
                }
                short_total += 1;
                target_count[*file as usize] += 1;
                if inside(record.file, *file) {
                    short_inside += 1;
                }
            }
        }
    }
    let short_null = analytic_null(&records, &short_files, &symbol_text, &target_count, words, &closure, paths.len());

    // Qualified join: Lean's own resolution, longest enclosing prefix first, and an OPEN return
    // where the resolved name is still declared in more than one file.
    let mut qualified_total = 0u64;
    let mut qualified_inside = 0u64;
    let mut qualified_open = 0u64;
    let mut qualified_unresolved = 0u64;
    let mut qualified_target_count: Vec<u64> = vec![0u64; paths.len()];
    let mut qualified_edges: Vec<(u32, u32)> = Vec::new();
    let namespace_parts_cache: HashMap<&str, Vec<String>> = HashMap::new();
    let _ = namespace_parts_cache;
    for record in &records {
        let path: Vec<String> = if record.namespace.is_empty() {
            Vec::new()
        } else {
            vec![record.namespace.clone()]
        };
        for id in &record.recruited {
            let symbol = symbol_text[*id as usize].as_str();
            let mut resolved: Option<&BTreeSet<u32>> = None;
            for candidate in resolution_candidates(&path, symbol) {
                if let Some(landing) = qualified_files.get(&candidate) {
                    resolved = Some(landing);
                    break;
                }
            }
            let Some(landing) = resolved else {
                qualified_unresolved += 1;
                continue;
            };
            let elsewhere: Vec<u32> = landing.iter().copied().filter(|f| *f != record.file).collect();
            if elsewhere.is_empty() {
                continue;
            }
            if elsewhere.len() > 1 {
                qualified_open += 1;
                continue;
            }
            qualified_total += 1;
            qualified_target_count[elsewhere[0] as usize] += 1;
            qualified_edges.push((record.file, elsewhere[0]));
            if inside(record.file, elsewhere[0]) {
                qualified_inside += 1;
            }
        }
    }
    let mut qualified_null_hits = 0u128;
    let mut qualified_null_denominator = 0u128;
    let total_targets: u64 = qualified_target_count.iter().sum();
    if total_targets > 0 {
        for (source, _) in &qualified_edges {
            let base = *source as usize * words;
            let mut reachable = 0u64;
            for word in 0..words {
                let mut bits = closure[base + word];
                while bits != 0 {
                    let bit = bits.trailing_zeros() as usize;
                    bits &= bits - 1;
                    reachable += qualified_target_count[word * 64 + bit];
                }
            }
            qualified_null_hits += u128::from(reachable);
            qualified_null_denominator += u128::from(total_targets);
        }
    }

    // ------------------------------------------------------------------ the report
    let mut out = String::new();
    let mut say = |key: &str, value: String| {
        println!("{key}\t{value}");
        out.push_str(&format!("{key}\t{value}\n"));
    };

    say("corpus.files", paths.len().to_string());
    say("corpus.lines", source_lines.to_string());
    say("corpus.bytes", bytes.to_string());
    say("cost.read_nanos", read_nanos.to_string());
    say("cost.parse_nanos", parse_nanos.to_string());

    say("truth.heads", truth_total.to_string());
    say("truth.heads_without_example", truth_without_example.to_string());
    say("truth.anonymous", truth_anonymous.to_string());
    say("reader.heads", records.len().to_string());
    say("reader.anonymous", anonymous_returned.to_string());
    say("reader.steps", steps_total.to_string());
    say("heads.hit", head_hit.to_string());
    say("heads.hit_without_example", head_hit_without_example.to_string());
    say("heads.phantom", phantom.to_string());
    say(
        "heads.recovered_bp",
        basis_points(head_hit_without_example as u64, truth_without_example as u64),
    );
    for (former, count) in &missed_by_former {
        say(&format!("heads.missed.{former}"), count.to_string());
    }
    for (cause, count) in &missed_by_cause {
        say(&format!("heads.cause.{cause}"), count.to_string());
    }

    say("names.agree", name_agree.to_string());
    say("names.wrong", name_wrong.to_string());
    say(
        "names.wrong_bp",
        basis_points(name_wrong as u64, head_hit as u64),
    );

    say("namespace.agree", namespace_agree.to_string());
    say("namespace.shallow", namespace_shallow.to_string());
    say("namespace.deep", namespace_deep.to_string());
    say("namespace.other", namespace_other.to_string());
    say(
        "namespace.wrong_bp",
        basis_points((head_hit - namespace_agree) as u64, head_hit as u64),
    );

    for glyph in GLYPHS {
        let key = glyph.to_string();
        let recruited = symbols
            .get(key.as_str())
            .map_or(0u64, |id| symbol_occurrences[*id as usize]);
        say(
            &format!("glyph.{key}"),
            format!(
                "recruited\t{recruited}\tbound\t{}\tsource\t{}",
                bound_glyphs.get(key.as_str()).copied().unwrap_or(0),
                source_glyphs.get(&glyph).copied().unwrap_or(0)
            ),
        );
    }
    let single_glyph_kinds = symbol_text
        .iter()
        .filter(|symbol| symbol.chars().count() == 1)
        .count();
    let single_glyph_occurrences: u64 = symbol_text
        .iter()
        .enumerate()
        .filter(|(_, symbol)| symbol.chars().count() == 1)
        .map(|(id, _)| symbol_occurrences[id])
        .sum();
    say("glyph.single_kinds", single_glyph_kinds.to_string());
    say("glyph.single_occurrences", single_glyph_occurrences.to_string());
    say("vocab.kinds", symbol_text.len().to_string());
    say("preamble.kinds", preamble_kinds.to_string());
    say("preamble.occurrences", preamble_occurrences.to_string());

    for (former, total) in &statement_total {
        let past = statement_past_where.get(former).copied().unwrap_or(0);
        let exact = statement_exact.get(former).copied().unwrap_or(0);
        say(
            &format!("statement.{former}"),
            format!(
                "exact\t{exact}\tof\t{total}\tbp\t{}\tpast_where\t{past}",
                basis_points(exact as u64, *total as u64)
            ),
        );
    }
    let statement_exact_all: usize = statement_exact.values().sum();
    let statement_all: usize = statement_total.values().sum();
    say(
        "statement.exact_bp",
        basis_points(statement_exact_all as u64, statement_all as u64),
    );

    say("edges.short.total", short_total.to_string());
    say("edges.short.inside", short_inside.to_string());
    say("edges.short.inside_bp", basis_points(short_inside, short_total));
    say("edges.short.null_bp", short_null);
    say("edges.qualified.total", qualified_total.to_string());
    say("edges.qualified.inside", qualified_inside.to_string());
    say(
        "edges.qualified.inside_bp",
        basis_points(qualified_inside, qualified_total),
    );
    say(
        "edges.qualified.null_bp",
        if qualified_null_denominator == 0 {
            "0".to_owned()
        } else {
            ((qualified_null_hits * 10_000) / qualified_null_denominator).to_string()
        },
    );
    say("edges.qualified.open", qualified_open.to_string());
    say("edges.qualified.unresolved", qualified_unresolved.to_string());

    fs::write(format!("{prefix}.summary.tsv"), out).unwrap();
    write_rows(&format!("{prefix}.phantom.tsv"), &phantom_rows);
    write_rows(&format!("{prefix}.wrongname.tsv"), &wrong_name_rows);
    write_rows(&format!("{prefix}.wrongns.tsv"), &wrong_namespace_rows);
    write_rows(&format!("{prefix}.wrongstmt.tsv"), &statement_wrong_rows);
    write_rows(&format!("{prefix}.missed.tsv"), &missed_rows);
}

/// The single-glyph carriers a length filter deletes. Each is a type, not a binder.
const GLYPHS: [char; 6] = ['ℝ', 'ℕ', 'ℂ', 'ℤ', '𝕜', 'α'];

fn write_rows(path: &str, rows: &[String]) {
    let mut file = fs::File::create(path).unwrap();
    for row in rows {
        writeln!(file, "{row}").unwrap();
    }
}

fn basis_points(part: u64, whole: u64) -> String {
    if whole == 0 {
        return "0".to_owned();
    }
    ((u128::from(part) * 10_000) / u128::from(whole)).to_string()
}

/// The analytic permutation null: the expected inside-rate when each edge's landing is redrawn
/// from the multiset of landings the observed population actually used.
#[allow(clippy::too_many_arguments)]
fn analytic_null(
    records: &[Record],
    short_files: &HashMap<&str, BTreeSet<u32>>,
    symbol_text: &[String],
    target_count: &[u64],
    words: usize,
    closure: &[u64],
    files: usize,
) -> String {
    let total: u64 = target_count.iter().sum();
    if total == 0 {
        return "0".to_owned();
    }
    // reachable[f] = how much of the target multiset sits inside f's import closure.
    let mut reachable = vec![0u64; files];
    for (file, slot) in reachable.iter_mut().enumerate() {
        let base = file * words;
        let mut sum = 0u64;
        for word in 0..words {
            let mut bits = closure[base + word];
            while bits != 0 {
                let bit = bits.trailing_zeros() as usize;
                bits &= bits - 1;
                sum += target_count[word * 64 + bit];
            }
        }
        *slot = sum;
    }
    let mut hits = 0u128;
    let mut draws = 0u128;
    for record in records {
        for id in &record.recruited {
            let Some(landing) = short_files.get(symbol_text[*id as usize].as_str()) else {
                continue;
            };
            let count = landing.iter().filter(|f| **f != record.file).count() as u128;
            hits += count * u128::from(reachable[record.file as usize]);
            draws += count * u128::from(total);
        }
    }
    if draws == 0 {
        return "0".to_owned();
    }
    ((hits * 10_000) / draws).to_string()
}

/// Every `import` a file declares, module-system prefixes included.
fn imports_of(text: &str) -> Vec<String> {
    let mut found = Vec::new();
    for line in text.lines() {
        let mut rest = line.trim();
        for visibility in ["public ", "private ", "meta "] {
            if let Some(after) = rest.strip_prefix(visibility) {
                rest = after.trim_start();
            }
        }
        let Some(after) = rest.strip_prefix("import ") else {
            continue;
        };
        if let Some(name) = after.split_whitespace().next() {
            found.push(name.to_owned());
        }
    }
    found
}

/// `…/mathlib/Mathlib/Algebra/Group/Basic.lean` is the module `Mathlib.Algebra.Group.Basic`.
fn module_name(path: &str) -> Option<String> {
    let stripped = path.strip_suffix(".lean")?;
    let at = stripped.rfind("/Mathlib/")?;
    Some(stripped[at + 1..].replace('/', "."))
}

/// Does `text` carry `token` as a whole identifier token?
fn has_token(text: &str, token: &str) -> bool {
    text.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '\''))
        .any(|word| word == token)
}
