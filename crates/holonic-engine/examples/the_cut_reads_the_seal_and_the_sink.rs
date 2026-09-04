//! **The cut classifier joined to two materials: the machine's own sealed receipts, and the
//! published attention-sink diagnostics.**
//!
//! ```text
//! cargo run --release --example the_cut_reads_the_seal_and_the_sink -- \
//!     .local/artifacts/the_conditioning_return_crosses_the_seal
//! ```
//!
//! `CONSTRUCTION_STATE.md`'s open line records [`holonic_engine::spine_cut`] as *joined to nothing*.
//! It gained a mouth onto the body's own chain carrier on 2026-08-10 and a driver over the
//! derivation circuit; what it had never read is **material that states its own populations**. This
//! driver supplies two such materials, one interior and one exterior, and the exterior one is a
//! control the field already published the answer to.
//!
//! # Interior — the conditioning return, read off its own seal
//!
//! The receipts deposited by the plan-2 conditioning run are content-addressed `.form` files. The
//! ones this driver reads are JSON and state their own counted populations: how many occurrences the
//! corpus carries and from which sources, how many passages the first production founded, how many
//! routes returned, how many cells the typed contact founded, what the ablation removed and what
//! stood afterwards.
//!
//! **The split that makes this a measurement.** The *stations and the edges between them* are this
//! driver's declared reading — a part-and-whole cell per row, the parts flowing into the whole and
//! the whole returning. The *populations* are the receipt's. A reading that both declared the
//! structure and supplied the numbers would have measured nothing, and
//! [`holonic_engine::spine_cut::read_counted_transfers`] refuses a field the receipt does not carry
//! rather than reading it as a zero, because an absent count and a count of nothing are different
//! claims and only one of them says the loop closed.
//!
//! The addresses in the file names are content hashes and **move whenever the material is re-sealed**,
//! so files are found by their station prefix and the directory is `argv[1]`.
//!
//! # Exterior — the attention sink, where the field has the diagnostics and no cut vocabulary
//!
//! `docs/canon/THE_CORRESPONDENCE_ATLAS.md` §4, *"the sink as a named cut"*: two species with published
//! structural diagnostics. A **nop** sink (`arXiv:2605.08453`, proved: a sink is a hard attention
//! switch and the output is identically zero) has negligible value norms; a **broadcast** sink
//! (`arXiv:2606.08105`) aggregates from the context and redistributes, which induces low-rank
//! outputs. The atlas's falsifier: *the classification must separate the two species from
//! value-norm and output-rank readings alone.*
//!
//! Four declared fixtures and three refusals are printed below. The fixtures are exact rationals;
//! the diagnostics never see the chain and the chain never sees the diagnostics, so their agreement
//! is evidence — and the fifth fixture is the head where they **disagree**, which is what says so.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use num_bigint::BigInt;
use num_traits::Zero;
use relational_geometry::Rat;

use holonic_engine::VertexId;
use holonic_engine::spine_cut::{
    AttentionHead, CountedTransfer, EdgeId, SinkReading, SinkSpecies, SpineCut, SpineCutError,
    classify_sink, name_the_cut, read_counted_transfers,
};

// -------------------------------------------------------------------------------------------------
// a boundary codec: the receipts are JSON and this crate carries no JSON reader
// -------------------------------------------------------------------------------------------------

/// The smallest reader that can address a field by path. A **boundary codec in a driver**, which is
/// where every codec in this tree lives; nothing below it enters a library.
// Every variant is parsed so the reader stays total over the receipt; only `Number` and `Object`
// are ever read out, and dropping the others would make the reader stop at the first string.
#[allow(dead_code)]
#[derive(Clone, Debug)]
enum Json {
    Null,
    Bool(bool),
    Number(String),
    Text(String),
    Array(Vec<Json>),
    Object(BTreeMap<String, Json>),
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }

    fn skip(&mut self) {
        while self.at < self.bytes.len() && self.bytes[self.at].is_ascii_whitespace() {
            self.at += 1;
        }
    }

    fn peek(&mut self) -> Option<u8> {
        self.skip();
        self.bytes.get(self.at).copied()
    }

    fn expect(&mut self, byte: u8) -> Option<()> {
        if self.peek()? == byte {
            self.at += 1;
            Some(())
        } else {
            None
        }
    }

    fn text(&mut self) -> Option<String> {
        self.expect(b'"')?;
        let mut out = String::new();
        loop {
            let byte = *self.bytes.get(self.at)?;
            self.at += 1;
            match byte {
                b'"' => return Some(out),
                b'\\' => {
                    let escaped = *self.bytes.get(self.at)?;
                    self.at += 1;
                    match escaped {
                        b'n' => out.push('\n'),
                        b't' => out.push('\t'),
                        b'r' => out.push('\r'),
                        b'b' => out.push('\u{8}'),
                        b'f' => out.push('\u{c}'),
                        b'u' => {
                            let hex =
                                std::str::from_utf8(self.bytes.get(self.at..self.at + 4)?).ok()?;
                            self.at += 4;
                            out.push(char::from_u32(u32::from_str_radix(hex, 16).ok()?)?);
                        }
                        other => out.push(other as char),
                    }
                }
                other => out.push(other as char),
            }
        }
    }

    fn value(&mut self) -> Option<Json> {
        match self.peek()? {
            b'{' => {
                self.at += 1;
                let mut carried = BTreeMap::new();
                if self.peek()? == b'}' {
                    self.at += 1;
                    return Some(Json::Object(carried));
                }
                loop {
                    let key = self.text()?;
                    self.expect(b':')?;
                    carried.insert(key, self.value()?);
                    match self.peek()? {
                        b',' => self.at += 1,
                        b'}' => {
                            self.at += 1;
                            return Some(Json::Object(carried));
                        }
                        _ => return None,
                    }
                }
            }
            b'[' => {
                self.at += 1;
                let mut carried = Vec::new();
                if self.peek()? == b']' {
                    self.at += 1;
                    return Some(Json::Array(carried));
                }
                loop {
                    carried.push(self.value()?);
                    match self.peek()? {
                        b',' => self.at += 1,
                        b']' => {
                            self.at += 1;
                            return Some(Json::Array(carried));
                        }
                        _ => return None,
                    }
                }
            }
            b'"' => Some(Json::Text(self.text()?)),
            b't' => {
                self.at += 4;
                Some(Json::Bool(true))
            }
            b'f' => {
                self.at += 5;
                Some(Json::Bool(false))
            }
            b'n' => {
                self.at += 4;
                Some(Json::Null)
            }
            _ => {
                let start = self.at;
                while self
                    .bytes
                    .get(self.at)
                    .is_some_and(|byte| !b",]} \n\t\r".contains(byte))
                {
                    self.at += 1;
                }
                Some(Json::Number(
                    std::str::from_utf8(&self.bytes[start..self.at])
                        .ok()?
                        .to_string(),
                ))
            }
        }
    }
}

impl Json {
    fn parse(bytes: &[u8]) -> Option<Self> {
        Reader::new(bytes).value()
    }

    fn at(&self, path: &[&str]) -> Option<&Self> {
        let mut standing = self;
        for step in path {
            let Self::Object(carried) = standing else {
                return None;
            };
            standing = carried.get(*step)?;
        }
        Some(standing)
    }

    /// The integer at a path, exactly. `None` when the path is absent or the value is not an
    /// integer — which is the whole point: it becomes a refusal, never a zero.
    fn integer(&self, path: &[&str]) -> Option<Rat> {
        let Self::Number(lexeme) = self.at(path)? else {
            return None;
        };
        lexeme.parse::<BigInt>().ok().map(Rat::from_integer)
    }
}

// -------------------------------------------------------------------------------------------------
// the declared reading of the seal
// -------------------------------------------------------------------------------------------------

/// Where the declared load sits for one row.
enum Load {
    /// The whole's own return edge: the reading exists to deliver the total.
    Return,
    /// A named part edge, by its position in `parts`. Used to point the load at a channel the
    /// material does not carry current through — the short-circuit reading.
    Part(usize),
}

struct Row {
    title: &'static str,
    parts: Vec<(&'static str, Vec<&'static str>)>,
    whole: (&'static str, Vec<&'static str>),
    load: Load,
    /// The field, if any, this row reads as `q_n − q_m`: a population the body holds rather than
    /// transports.
    stored: Option<(&'static str, Vec<&'static str>)>,
    why: &'static str,
}

fn rows() -> Vec<Row> {
    let corpus = |field: &'static str| vec!["grade", "corpus", "receipt", field];
    let successor = |field: &'static str| vec!["attribution", "successor", field];
    let conduct = |field: &'static str| vec!["attribution", "conduct", field];
    vec![
        Row {
            title: "the occurrence census",
            parts: vec![
                ("human", corpus("human_occurrences")),
                ("assistant", corpus("assistant_occurrences")),
                ("document", corpus("document_occurrences")),
            ],
            whole: ("unique occurrences", corpus("unique_occurrences")),
            load: Load::Return,
            stored: None,
            why: "the three declared sources against the corpus the mouth sealed",
        },
        Row {
            title: "the witness census",
            parts: vec![
                ("claude history", corpus("claude_history_witnesses")),
                ("codex history", corpus("codex_history_witnesses")),
                ("claude rollouts", corpus("claude_witnesses")),
                ("codex rollouts", corpus("codex_witnesses")),
                ("documents", corpus("document_witnesses")),
            ],
            whole: ("witnessed occurrences", corpus("witnessed_occurrences")),
            load: Load::Return,
            stored: None,
            why: "five witness containers against the witnessed total",
        },
        Row {
            title: "the duplicate remainder",
            parts: vec![
                ("unique", corpus("unique_occurrences")),
                ("exact duplicates", corpus("exact_duplicate_witnesses")),
            ],
            whole: ("witnessed occurrences", corpus("witnessed_occurrences")),
            load: Load::Return,
            stored: None,
            why: "the duplicate population is exactly what witnessed exceeds unique by",
        },
        Row {
            title: "the corpus with its held-out control",
            parts: vec![
                ("human", corpus("human_occurrences")),
                ("assistant", corpus("assistant_occurrences")),
                ("document", corpus("document_occurrences")),
            ],
            whole: ("unique occurrences", corpus("unique_occurrences")),
            load: Load::Return,
            stored: Some(("excluded control", corpus("excluded_control_occurrences"))),
            why: "the same census, with the declared control read as STORED rather than transported",
        },
        Row {
            title: "the self-emanated channel",
            parts: vec![
                ("human", corpus("human_occurrences")),
                ("assistant", corpus("assistant_occurrences")),
                ("document", corpus("document_occurrences")),
                ("self-emanated", corpus("self_emanated_witnesses")),
            ],
            whole: ("unique occurrences", corpus("unique_occurrences")),
            load: Load::Part(3),
            stored: None,
            why: "the census closes without ever crossing the self-emanation channel",
        },
        Row {
            title: "the second production",
            parts: vec![
                ("base passages", successor("base_passages")),
                ("returned routes", successor("returned_routes")),
            ],
            whole: (
                "second production passages",
                vec!["attribution", "successor", "second", "passages"],
            ),
            load: Load::Return,
            stored: None,
            why: "the return through the seal is what the second production is longer by",
        },
        Row {
            title: "the returned routes and the rest",
            parts: vec![
                ("returned routes", successor("returned_routes")),
                ("withdrawn cells", successor("withdrawn_cells")),
            ],
            whole: (
                "rest records",
                vec!["attribution", "conduct", "rest", "records"],
            ),
            load: Load::Return,
            stored: None,
            why: "what returned is what the source-free rest carries",
        },
        Row {
            title: "the typed contact",
            parts: vec![(
                "contact relations",
                vec!["grade", "typed_contact", "relations"],
            )],
            whole: ("founded cells", successor("founded_cells")),
            load: Load::Return,
            stored: None,
            why: "every relation the contact typed founded a cell",
        },
        Row {
            title: "the earlier return against the founding",
            parts: vec![(
                "returned artifacts",
                vec!["grade", "earlier_return", "returned_artifacts"],
            )],
            whole: ("founded cells", successor("founded_cells")),
            load: Load::Return,
            stored: None,
            why: "the reading returned fewer artifacts than the contact founded cells",
        },
        Row {
            title: "the ablation",
            parts: vec![(
                "routes after ablation",
                vec![
                    "attribution",
                    "conduct",
                    "all_ablation",
                    "returned_routes_after",
                ],
            )],
            whole: ("returned routes", successor("returned_routes")),
            load: Load::Return,
            stored: None,
            why: "removing the deposits removed the later conduct",
        },
        Row {
            title: "after the ablation",
            parts: vec![(
                "routes after ablation",
                vec![
                    "attribution",
                    "conduct",
                    "all_ablation",
                    "returned_routes_after",
                ],
            )],
            whole: ("withdrawn cells", successor("withdrawn_cells")),
            load: Load::Return,
            stored: None,
            why: "nothing returned and nothing was withdrawn",
        },
        Row {
            title: "a field the receipt does not carry",
            parts: vec![
                ("returned routes", successor("returned_routes")),
                ("a population nobody sealed", conduct("no_such_population")),
            ],
            whole: (
                "rest records",
                vec!["attribution", "conduct", "rest", "records"],
            ),
            load: Load::Return,
            stored: None,
            why: "THE NEGATIVE CONTROL: an absent count must refuse, never arrive as a zero",
        },
    ]
}

fn read_row(row: &Row, material: &Json) -> Result<(SpineCut, Rat, Rat), SpineCutError> {
    let parts_vertex = VertexId(1);
    let whole_vertex = VertexId(2);
    let mut transfers = Vec::new();
    let mut carried = Rat::zero();
    for (ordinal, (label, path)) in row.parts.iter().enumerate() {
        let population = material.integer(path);
        if let Some(value) = &population {
            carried += value;
        }
        transfers.push(CountedTransfer {
            id: EdgeId(ordinal as u64 + 1),
            tail: parts_vertex,
            head: whole_vertex,
            name: (*label).to_string(),
            population,
        });
    }
    let whole = material.integer(&row.whole.1);
    let total = whole.clone().unwrap_or_else(Rat::zero);
    transfers.push(CountedTransfer {
        id: EdgeId(0),
        tail: whole_vertex,
        head: parts_vertex,
        name: row.whole.0.to_string(),
        population: whole,
    });
    let stored = row
        .stored
        .as_ref()
        .and_then(|(_, path)| material.integer(path))
        .unwrap_or_else(Rat::zero);
    let reading = read_counted_transfers(transfers, stored)?;
    let load = BTreeSet::from([match row.load {
        Load::Return => EdgeId(0),
        Load::Part(ordinal) => EdgeId(ordinal as u64 + 1),
    }]);
    Ok((name_the_cut(&reading, &load)?, carried, total))
}

// -------------------------------------------------------------------------------------------------
// the material
// -------------------------------------------------------------------------------------------------

fn receipt(root: &Path, prefix: &str) -> Option<Json> {
    let mut found: Vec<PathBuf> = std::fs::read_dir(root)
        .ok()?
        .flatten()
        .map(|entry| entry.path())
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with(prefix))
        })
        .collect();
    found.sort();
    for path in found {
        let bytes = std::fs::read(&path).ok()?;
        if bytes.first() == Some(&b'{') {
            if let Some(parsed) = Json::parse(&bytes) {
                return Some(parsed);
            }
        }
    }
    None
}

// -------------------------------------------------------------------------------------------------
// the exterior fixtures
// -------------------------------------------------------------------------------------------------

fn ratio(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn row_of(entries: &[(i64, i64)]) -> Vec<Rat> {
    entries
        .iter()
        .map(|(numerator, denominator)| ratio(*numerator, *denominator))
        .collect()
}

/// The nop: every query routes its whole attention to a null position whose value carries nothing.
fn nop_head() -> AttentionHead {
    let to_sink = row_of(&[(0, 1), (0, 1), (0, 1), (1, 1)]);
    AttentionHead::declare(
        vec![to_sink.clone(), to_sink.clone(), to_sink.clone(), to_sink],
        vec![
            row_of(&[(1, 1), (0, 1), (0, 1)]),
            row_of(&[(0, 1), (1, 1), (0, 1)]),
            row_of(&[(0, 1), (0, 1), (1, 1)]),
            row_of(&[(0, 1), (0, 1), (0, 1)]),
        ],
        3,
        [0, 1, 2],
    )
    .expect("the fixture is stochastic and meets")
}

/// The broadcast: the sink aggregates uniformly and its value **is** the aggregate.
fn broadcast_head() -> AttentionHead {
    let to_sink = row_of(&[(0, 1), (0, 1), (0, 1), (1, 1)]);
    let aggregate = row_of(&[(1, 3), (1, 3), (1, 3), (0, 1)]);
    AttentionHead::declare(
        vec![to_sink.clone(), to_sink.clone(), to_sink, aggregate],
        vec![
            row_of(&[(1, 1), (0, 1), (0, 1)]),
            row_of(&[(0, 1), (1, 1), (0, 1)]),
            row_of(&[(0, 1), (0, 1), (1, 1)]),
            row_of(&[(1, 3), (1, 3), (1, 3)]),
        ],
        3,
        [0, 1, 2],
    )
    .expect("the fixture is stochastic and meets")
}

/// The same broadcast, redistributing to positions the caller does not read.
fn bypassing_head() -> AttentionHead {
    let to_sink = row_of(&[(0, 1), (0, 1), (0, 1), (0, 1), (1, 1)]);
    let apart = row_of(&[(0, 1), (0, 1), (0, 1), (1, 1), (0, 1)]);
    let aggregate = row_of(&[(1, 3), (1, 3), (1, 3), (0, 1), (0, 1)]);
    AttentionHead::declare(
        vec![to_sink.clone(), to_sink.clone(), to_sink, apart, aggregate],
        vec![
            row_of(&[(1, 1), (0, 1), (0, 1)]),
            row_of(&[(0, 1), (1, 1), (0, 1)]),
            row_of(&[(0, 1), (0, 1), (1, 1)]),
            row_of(&[(1, 1), (0, 1), (0, 1)]),
            row_of(&[(1, 3), (1, 3), (1, 3)]),
        ],
        4,
        [3],
    )
    .expect("the fixture is stochastic and meets")
}

/// A hub whose value carries three times the mass it aggregated: both published diagnostics still
/// read **broadcast**, and the chain reads **leak**.
fn imbalanced_head() -> AttentionHead {
    let to_sink = row_of(&[(0, 1), (0, 1), (0, 1), (1, 1)]);
    let aggregate = row_of(&[(1, 3), (1, 3), (1, 3), (0, 1)]);
    AttentionHead::declare(
        vec![to_sink.clone(), to_sink.clone(), to_sink, aggregate],
        vec![
            row_of(&[(1, 1), (0, 1), (0, 1)]),
            row_of(&[(0, 1), (1, 1), (0, 1)]),
            row_of(&[(0, 1), (0, 1), (1, 1)]),
            row_of(&[(1, 1), (1, 1), (1, 1)]),
        ],
        3,
        [0, 1, 2],
    )
    .expect("the fixture is stochastic and meets")
}

/// A head that routes content directly between positions: neither species.
fn routing_head() -> AttentionHead {
    AttentionHead::declare(
        vec![
            row_of(&[(1, 2), (1, 2), (0, 1)]),
            row_of(&[(0, 1), (1, 2), (1, 2)]),
            row_of(&[(1, 2), (0, 1), (1, 2)]),
        ],
        vec![
            row_of(&[(1, 1), (0, 1), (0, 1)]),
            row_of(&[(0, 1), (1, 1), (0, 1)]),
            row_of(&[(0, 1), (0, 1), (1, 1)]),
        ],
        0,
        [0, 1, 2],
    )
    .expect("the fixture is stochastic and meets")
}

fn print_head(label: &str, head: &AttentionHead, declared: SinkSpecies) -> Option<bool> {
    let diagnostics = head.diagnose().expect("the head reads");
    println!(
        "  {label:<26} value mass at sink {:<6} output rank {} of {:<3} attention on sink {}",
        diagnostics.sink_value_mass,
        diagnostics.output_rank,
        diagnostics.full_rank_bound,
        diagnostics.attention_on_sink
    );
    match classify_sink(head, declared) {
        Ok(verdict) => {
            println!(
                "  {:<26} species {:<28} cut {:<22} agree {}",
                "",
                match &verdict.read {
                    SinkReading::Species(species) => format!("{species:?}"),
                    SinkReading::Neither { why } => format!("neither ({why})"),
                },
                verdict.cut.name(),
                verdict.agrees()
            );
            Some(verdict.agrees())
        }
        Err(SpineCutError::SinkSpeciesRefuted { declared, read }) => {
            println!(
                "  {:<26} REFUSED: declared {declared:?}, diagnostics read {read:?}",
                ""
            );
            None
        }
        Err(other) => {
            println!("  {:<26} REFUSED: {other}", "");
            None
        }
    }
}

// -------------------------------------------------------------------------------------------------

fn main() {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| ".local/artifacts/the_conditioning_return_crosses_the_seal".to_string());
    let root = PathBuf::from(root);

    println!("== the cut classifier, joined to two materials ==");
    println!("interior: {}", root.display());

    let grade = receipt(&root, "conditioning-return-grade-");
    let attribution = receipt(&root, "source-free-causal-attribution-");

    println!();
    println!("-- interior: the conditioning return, read off its own seal --");
    match (grade, attribution) {
        (Some(grade), Some(attribution)) => {
            let material = Json::Object(BTreeMap::from([
                ("grade".to_string(), grade),
                ("attribution".to_string(), attribution),
            ]));
            let mut named: BTreeMap<&str, usize> = BTreeMap::new();
            let mut refused = 0usize;
            for row in rows() {
                match read_row(&row, &material) {
                    Ok((cut, parts, whole)) => {
                        *named.entry(cut.name()).or_default() += 1;
                        println!(
                            "  {:<38} parts {:>8}  whole {:>8}  ->  {}",
                            row.title,
                            parts.to_string(),
                            whole.to_string(),
                            cut.name()
                        );
                        if let SpineCut::Leak { at } = &cut {
                            let named: Vec<String> = at
                                .iter()
                                .map(|(vertex, value)| format!("{vertex:?}={value}"))
                                .collect();
                            println!("  {:<38} the residual is named at {}", "", named.join(", "));
                        }
                        if let SpineCut::Accumulation { stored } = &cut {
                            println!(
                                "  {:<38} stored {stored} -- {}",
                                "",
                                row.stored.as_ref().map_or("", |(label, _)| label)
                            );
                        }
                        if let SpineCut::ShortCircuit {
                            bypass,
                            declared_load,
                        } = &cut
                        {
                            println!(
                                "  {:<38} {} edges carry, none of them the declared load {:?}",
                                "",
                                bypass.len(),
                                declared_load
                            );
                        }
                        println!("  {:<38} {}", "", row.why);
                    }
                    Err(SpineCutError::PopulationNotCarried { name, .. }) => {
                        refused += 1;
                        println!(
                            "  {:<38} REFUSED: the receipt carries no \"{name}\", and an absent \
                             count is not a zero",
                            row.title
                        );
                        println!("  {:<38} {}", "", row.why);
                    }
                    Err(other) => {
                        refused += 1;
                        println!("  {:<38} REFUSED: {other}", row.title);
                    }
                }
            }
            println!();
            println!("  cuts named on the seal: {named:?}");
            println!("  readings refused for want of a carried population: {refused}");
            println!(
                "  distinct cuts reached on this material: {} of 5",
                named.len()
            );
        }
        (grade, attribution) => {
            println!(
                "  no readable receipt pair under {} (grade {}, attribution {})",
                root.display(),
                if grade.is_some() { "found" } else { "absent" },
                if attribution.is_some() {
                    "found"
                } else {
                    "absent"
                }
            );
            println!(
                "  the addresses are content hashes and move on every re-seal; pass the directory \
                 as argv[1]"
            );
        }
    }

    println!();
    println!("-- exterior: the attention sink, against the published diagnostics --");
    println!("  the species is read from value mass and output rank ALONE; the cut is read from");
    println!("  the chain; neither reading sees the other.");
    println!();
    let mut agreed = 0usize;
    let mut disagreed = 0usize;
    for (label, head, declared) in [
        ("nop sink", nop_head(), SinkSpecies::Nop),
        ("broadcast sink", broadcast_head(), SinkSpecies::Broadcast),
        (
            "broadcast off the load",
            bypassing_head(),
            SinkSpecies::Broadcast,
        ),
        (
            "hub emitting excess",
            imbalanced_head(),
            SinkSpecies::Broadcast,
        ),
    ] {
        match print_head(label, &head, declared) {
            Some(true) => agreed += 1,
            Some(false) => disagreed += 1,
            None => {}
        }
    }
    println!();
    println!("  -- the refusals, which are what make the four above evidence --");
    print_head(
        "broadcast declared nop",
        &broadcast_head(),
        SinkSpecies::Nop,
    );
    print_head(
        "nop declared broadcast",
        &nop_head(),
        SinkSpecies::Broadcast,
    );
    print_head("direct routing", &routing_head(), SinkSpecies::Broadcast);

    println!();
    println!(
        "  fixtures whose two readings agreed: {agreed}; disagreed: {disagreed} \
         (the imbalanced hub, by construction)"
    );

    // The nop's chain, exhibited rather than described: every current is zero, so the cut is rest
    // and not a leak that happened to balance.
    let nop = nop_head();
    let reading = nop.read_the_head().expect("the head reads");
    println!(
        "  the nop chain carries {} edges and {} of them carry current",
        reading.edges.len(),
        reading.carrying().len()
    );
    let broadcast = broadcast_head();
    let reading = broadcast.read_the_head().expect("the head reads");
    println!(
        "  the broadcast chain carries {} edges, {} of them carry, and the residual vanishes at \
         every position: {}",
        reading.edges.len(),
        reading.carrying().len(),
        reading.residual.values().all(Zero::is_zero)
    );
}
