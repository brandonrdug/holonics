use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::model::Inventory;
use crate::{Counts, MARKDOWN_MARKER, SCHEMA, TEXT_MARKER};

pub(crate) fn render(inventory: &Inventory, counts: &Counts) -> BTreeMap<String, String> {
    let mut files = BTreeMap::new();
    files.insert("INDEX.md".to_string(), overview(counts));
    files.insert("CANON_INDEX.md".to_string(), canon(inventory));
    files.insert("RESEARCH_INDEX.md".to_string(), research(inventory));
    files.insert("OBSERVATIONS_INDEX.md".to_string(), observations(inventory));
    files.insert("COMMUNE_INDEX.md".to_string(), commune(inventory));
    files.insert("LEDGER_INDEX.md".to_string(), ledger(inventory));
    files.insert("RUST_INDEX.md".to_string(), rust(inventory));
    files.insert("ABI_INDEX.md".to_string(), abi(inventory));
    files.insert("REGISTRY.tsv".to_string(), registry(inventory));
    files.insert("SOURCES.tsv".to_string(), sources(inventory));
    files
}

fn markdown_header(title: &str) -> String {
    format!(
        "{MARKDOWN_MARKER}\n\n# {title}\n\nSchema: `{SCHEMA}`. This file is a generated navigation map, never canon, evidence, correspondence, or a deposit. Source paths are laboratory-root-relative.\n\n"
    )
}

fn overview(counts: &Counts) -> String {
    let mut output = markdown_header("Laboratory record navigation index");
    output.push_str(
        "Canonical IDs come only from the append-only allocation table embedded with the tool. Formula handles and filesystem paths are aliases: they may be updated after an explicit move without changing the allocated ID. `discovery:` keys are provisional scanner coordinates and are not durable IDs. Lexical marks report words present in a heading or preamble; they do not infer authority or disposition.\n\n",
    );
    output.push_str("| Inventory | Count | Index |\n|---|---:|---|\n");
    writeln!(
        output,
        "| Formula claims | {} | [canon](CANON_INDEX.md) |",
        counts.formula_claims
    )
    .unwrap();
    writeln!(
        output,
        "| Research documents | {} | [research](RESEARCH_INDEX.md) |",
        counts.research_documents
    )
    .unwrap();
    writeln!(
        output,
        "| Recorded observations | {} campaigns / {} records | [observations](OBSERVATIONS_INDEX.md) |",
        counts.observations, counts.observation_records
    )
    .unwrap();
    writeln!(
        output,
        "| Commune letters | {} | [commune](COMMUNE_INDEX.md) |",
        counts.correspondence
    )
    .unwrap();
    writeln!(
        output,
        "| Ledger headings | {} | [ledger](LEDGER_INDEX.md) |",
        counts.ledger_entries
    )
    .unwrap();
    writeln!(
        output,
        "| Rust packages / lexical public declarations | {} / {} | [Rust](RUST_INDEX.md) |",
        counts.crates, counts.public_symbols
    )
    .unwrap();
    writeln!(
        output,
        "| Discoverable ABI/archive/kernel identifiers | {} | [ABI](ABI_INDEX.md) |",
        counts.abi_identifiers
    )
    .unwrap();
    output.push_str(
        "\nMachine-readable maps: [canonical registry](REGISTRY.tsv) and [source fingerprints](SOURCES.tsv). SHA-256 fingerprints describe source bytes; they are not identities.\n",
    );
    output
}

fn canon(inventory: &Inventory) -> String {
    let mut output = markdown_header("Formula section index");
    output.push_str(
        "`heading marks` are exact lexical marks from each Formula heading. `UNMARKED` means the heading itself did not state a recognized mark; no status is inferred from section prose. The Formula handle is a mutable alias to the durable allocated claim ID.\n\n",
    );
    output.push_str(
        "| Claim ID | Formula alias | Title | Heading marks | Source |\n|---|---|---|---|---|\n",
    );
    for entry in &inventory.formula {
        writeln!(
            output,
            "| `{}` | `formula:{}` | {} | {} | `{}` |",
            entry.id,
            md(&entry.handle),
            md(&entry.title),
            marks(&entry.marks),
            source_line(&entry.source, entry.line)
        )
        .unwrap();
    }
    output
}

fn research(inventory: &Inventory) -> String {
    let mut output = markdown_header("Research document index");
    output.push_str(
        "Research documents are inventoried as documents, not automatically promoted to canonical claims. Their `discovery:` keys are filename-derived scanner coordinates and may change when a file moves. `preamble marks` are lexical only.\n\n",
    );
    output.push_str("| Discovery key | Date | Title | Preamble marks | SHA-256 | Source |\n|---|---|---|---|---|---|\n");
    for entry in &inventory.research {
        writeln!(
            output,
            "| `{}` | {} | {} | {} | `{}` | `{}` |",
            md(&entry.id),
            md(&entry.date),
            md(&entry.title),
            marks(&entry.marks),
            entry.sha256,
            md(&entry.source)
        )
        .unwrap();
    }
    output
}

fn observations(inventory: &Inventory) -> String {
    let mut output = markdown_header("Observation evidence index");
    output.push_str(
        "Observation and evidence IDs are durable allocations. Campaign names and record paths are aliases. Only exact `RESULTS.md` and `PRODUCTION.md` records are included; artifact directories and campaigns without either record remain outside this declared index grain. `preamble marks` are lexical only.\n\n",
    );
    output.push_str("| Observation ID | Evidence ID | Campaign alias | Record | Title | Preamble marks | SHA-256 | Source |\n|---|---|---|---|---|---|---|---|\n");
    for entry in &inventory.observations {
        writeln!(
            output,
            "| `{}` | `{}` | `observation:{}` | {} | {} | {} | `{}` | `{}` |",
            entry.observation_id,
            entry.evidence_id,
            md(&entry.campaign),
            md(&entry.record_kind),
            md(&entry.title),
            marks(&entry.marks),
            entry.sha256,
            md(&entry.source)
        )
        .unwrap();
    }
    output
}

fn commune(inventory: &Inventory) -> String {
    let mut output = markdown_header("Commune correspondence index");
    output.push_str(
        "Correspondence IDs are durable allocations; letter paths are aliases. No answered/deposited/superseded disposition is inferred. `preamble marks` report lexical words only. `README.md` is protocol and is not allocated as a letter.\n\n",
    );
    output.push_str("| Correspondence ID | Date | From | To | Title | Preamble marks | SHA-256 | Source |\n|---|---|---|---|---|---|---|---|\n");
    for entry in &inventory.correspondence {
        writeln!(
            output,
            "| `{}` | {} | {} | {} | {} | {} | `{}` | `{}` |",
            entry.id,
            md(&entry.date),
            md(&entry.from),
            md(&entry.to),
            md(&entry.title),
            marks(&entry.marks),
            entry.sha256,
            md(&entry.source)
        )
        .unwrap();
    }
    output
}

fn ledger(inventory: &Inventory) -> String {
    let mut output = markdown_header("Ledger heading index");
    output.push_str(
        "This is a source-order pointer list over dated level-two and level-three headings. It assigns no new deposit IDs and copies no deposit prose. `heading marks` are lexical only.\n\n",
    );
    output.push_str("| Date | Heading | Heading marks | Source |\n|---|---|---|---|\n");
    for entry in &inventory.ledger {
        writeln!(
            output,
            "| {} | {} | {} | `{}` |",
            md(&entry.date),
            md(&entry.title),
            marks(&entry.marks),
            source_line(&entry.source, entry.line)
        )
        .unwrap();
    }
    output
}

fn rust(inventory: &Inventory) -> String {
    let mut output = markdown_header("Rust package and public-declaration index");
    output.push_str(
        "Package relationships are read from the nested Soma workspace and detached manifests. Public declarations are a conservative lexical scan of regular `.rs` files under package `src/` directories: macro expansion, visibility resolution, public fields, and re-export closure are intentionally not inferred. All `discovery:` keys in this file are provisional.\n\n",
    );
    output.push_str("## Packages\n\n| Discovery key | Package | Relationship | Manifest SHA-256 | Manifest |\n|---|---|---|---|---|\n");
    for entry in &inventory.crates {
        writeln!(
            output,
            "| `{}` | `{}` | {} | `{}` | `{}` |",
            md(&entry.id),
            md(&entry.name),
            md(&entry.relationship),
            entry.sha256,
            md(&entry.manifest)
        )
        .unwrap();
    }
    output.push_str("\n## Lexically public declarations\n\n| Package | Kind | Name/expression | Source |\n|---|---|---|---|\n");
    for entry in &inventory.public_symbols {
        writeln!(
            output,
            "| `{}` | {} | `{}` | `{}` |",
            md(&entry.crate_name),
            md(&entry.kind),
            md(&entry.name),
            source_line(&entry.source, entry.line)
        )
        .unwrap();
    }
    output
}

fn abi(inventory: &Inventory) -> String {
    let mut output = markdown_header("Discoverable ABI, archive, and kernel identifier index");
    output.push_str(
        "This scanner reports explicit kernel attributes and constant/static names with layout, archive, status, version, magic, schema, wire, or record vocabulary. It is a lexical duplication/navigation audit, not proof that a constant participates in a live ABI. `discovery:` keys are source coordinates, not durable allocated IDs. Declarations longer than 240 characters are visibly truncated with `…`.\n\n",
    );
    output.push_str("| Discovery key | Category | Package | Identifier | Declaration | Source |\n|---|---|---|---|---|---|\n");
    for entry in &inventory.abi {
        writeln!(
            output,
            "| `{}` | {} | `{}` | `{}` | `{}` | `{}` |",
            md(&entry.id),
            md(&entry.category),
            md(&entry.crate_name),
            md(&entry.name),
            md(&entry.declaration),
            source_line(&entry.source, entry.line)
        )
        .unwrap();
    }
    output
}

fn registry(inventory: &Inventory) -> String {
    let mut output = format!(
        "{TEXT_MARKER}\n# schema\t{SCHEMA}\n# Canonical IDs are append-only allocations; aliases may be updated explicitly after source movement.\n"
    );
    output.push_str("id\tkind\talias\ttitle\tsource\tline\tmarks\tsha256\n");
    for entry in inventory.registry.values() {
        writeln!(
            output,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            tsv(&entry.id),
            tsv(&entry.kind),
            tsv(&entry.alias),
            tsv(&entry.title),
            tsv(&entry.source),
            entry.line.map_or_else(String::new, |line| line.to_string()),
            tsv(&entry.marks.join(",")),
            entry.sha256.as_deref().map(tsv).unwrap_or_default()
        )
        .unwrap();
    }
    output
}

fn sources(inventory: &Inventory) -> String {
    let mut output = format!(
        "{TEXT_MARKER}\n# schema\t{SCHEMA}\n# SHA-256 fingerprints are byte snapshots, not record identities or authority.\npath\tsha256\n"
    );
    for (path, sha256) in &inventory.source_hashes {
        writeln!(output, "{}\t{}", tsv(path), sha256).unwrap();
    }
    output
}

fn marks(values: &[&str]) -> String {
    if values.is_empty() {
        "UNMARKED".to_string()
    } else {
        values.join(" · ")
    }
}

fn source_line(source: &str, line: usize) -> String {
    format!("{}:{line}", md(source))
}

fn md(value: &str) -> String {
    value
        .replace('\\', "\\\\")
        .replace('|', "\\|")
        .replace(['\n', '\r'], " ")
}

fn tsv(value: &str) -> String {
    value
        .replace('\\', "\\\\")
        .replace('\t', "\\t")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
}

#[cfg(test)]
mod tests {
    use super::{md, tsv};

    #[test]
    fn table_escaping_is_deterministic() {
        assert_eq!(md("a|b\nc"), "a\\|b c");
        assert_eq!(tsv("a\tb\\c"), "a\\tb\\\\c");
    }
}
