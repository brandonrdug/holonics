use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use super::{check_generated, generate, write_generated, IndexError};

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

struct Fixture {
    root: PathBuf,
}

impl Fixture {
    fn new() -> Self {
        let serial = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "soma-record-index-test-{}-{serial}",
            std::process::id()
        ));
        if root.exists() {
            fs::remove_dir_all(&root).unwrap();
        }
        let fixture = Self { root };
        fixture.seed();
        fixture
    }

    fn seed(&self) {
        self.write(
            "src/soma/FORMULA.md",
            "# Formula\n\n## I · FIRST LAW (RATIFIED)\n\nThe body says OPEN, but the heading does not.\n",
        );
        self.write(
            "src/soma/RESEARCH/2026-07-15_NOTE.md",
            "# A research note\n\n**DRAFT**\n\n## Body\n",
        );
        self.write(
            "src/soma/observations/demo/RESULTS.md",
            "# Demo results\n\n**BUILT / MEASURED**\n\n## Evidence\n",
        );
        self.write(
            "src/soma/observations/demo/PRODUCTION.md",
            "# Demo production\n\n**MEASURED**\n\n## Read\n",
        );
        self.write(
            ".agents/COMMUNE/2026-07-15_sol-to-fable_fixture.md",
            "# SOL → FABLE — fixture\n\n**OPEN**\n",
        );
        self.write(
            "src/soma/LEDGER.md",
            "# Ledger\n\n## 2026-07-15 — THE FIXTURE [BUILT]\n",
        );
        self.write(
            "src/soma/Cargo.toml",
            "[workspace]\nresolver = \"2\"\nmembers = [\"body\", \"tools/record-index\"]\n",
        );
        self.write(
            "src/soma/body/Cargo.toml",
            "[package]\nname = \"body\"\nversion = \"0.0.0\"\nedition = \"2021\"\n",
        );
        self.write(
            "src/soma/body/src/lib.rs",
            "pub const ROW_WORDS: usize = 3;\nconst PRIVATE: usize = 1;\npub struct Body;\n#[no_mangle]\npub extern \"C\" fn body_entry() {}\n",
        );
        self.write(
            "src/soma/tools/record-index/Cargo.toml",
            "[package]\nname = \"soma-record-index\"\nversion = \"0.0.0\"\nedition = \"2021\"\n",
        );
        self.write(
            "src/soma/tools/record-index/src/main.rs",
            "pub fn fixture_main() {}\n",
        );
        self.write(
            "src/soma/tools/record-index/allocations.tsv",
            "# allocations\nclaim\tCLM-20260715-0001\tformula:I\nobservation\tOBS-20260715-0001\tobservation:demo\nevidence\tEVD-20260715-0001\tevidence:src/soma/observations/demo/PRODUCTION.md\nevidence\tEVD-20260715-0002\tevidence:src/soma/observations/demo/RESULTS.md\ncorrespondence\tCOR-20260715-0001\tcorrespondence:.agents/COMMUNE/2026-07-15_sol-to-fable_fixture.md\n",
        );
    }

    fn write(&self, relative: &str, contents: &str) {
        let path = self.root.join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

#[test]
fn full_render_is_byte_deterministic_and_typed() {
    let fixture = Fixture::new();
    let first = generate(&fixture.root).unwrap();
    let second = generate(&fixture.root).unwrap();
    assert_eq!(first, second);
    assert_eq!(first.counts().formula_claims, 1);
    assert_eq!(first.counts().observation_records, 2);
    assert_eq!(first.counts().observations, 1);
    assert_eq!(first.counts().correspondence, 1);
    assert_eq!(first.counts().crates, 2);
    assert_eq!(first.counts().public_symbols, 4);

    let canon = &first.files()["CANON_INDEX.md"];
    assert!(canon.contains("`CLM-20260715-0001`"));
    assert!(canon.contains("RATIFIED"));
    assert!(!canon.contains("RATIFIED · OPEN"));
    let registry = &first.files()["REGISTRY.tsv"];
    assert!(registry.contains("CLM-20260715-0001\tclaim\tformula:I"));
    assert!(registry
        .contains("EVD-20260715-0002\tevidence\tevidence:src/soma/observations/demo/RESULTS.md"));
}

#[test]
fn allocated_id_survives_an_explicit_alias_move() {
    let fixture = Fixture::new();
    let before = generate(&fixture.root).unwrap();
    let old = fixture.root.join("src/soma/observations/demo/RESULTS.md");
    let new = fixture
        .root
        .join("src/soma/observations/demo/archive/RESULTS.md");
    fs::create_dir_all(new.parent().unwrap()).unwrap();
    fs::rename(old, new).unwrap();
    let allocation_path = fixture
        .root
        .join("src/soma/tools/record-index/allocations.tsv");
    let allocations = fs::read_to_string(&allocation_path).unwrap().replace(
        "evidence:src/soma/observations/demo/RESULTS.md",
        "evidence:src/soma/observations/demo/archive/RESULTS.md",
    );
    fs::write(allocation_path, allocations).unwrap();
    let after = generate(&fixture.root).unwrap();
    assert!(before.files()["REGISTRY.tsv"].contains("EVD-20260715-0002"));
    assert!(after.files()["REGISTRY.tsv"].contains(
        "EVD-20260715-0002\tevidence\tevidence:src/soma/observations/demo/archive/RESULTS.md"
    ));
}

#[test]
fn writer_owns_only_marked_outputs_and_check_detects_drift() {
    let fixture = Fixture::new();
    let generated = generate(&fixture.root).unwrap();
    let output = fixture.root.join("generated/record-index");
    write_generated(&fixture.root, &output, &generated).unwrap();
    check_generated(&fixture.root, &output, &generated).unwrap();

    fs::write(output.join("INDEX.md"), "changed\n").unwrap();
    assert!(matches!(
        check_generated(&fixture.root, &output, &generated),
        Err(IndexError::Drift { .. })
    ));
    assert!(matches!(
        write_generated(&fixture.root, &output, &generated),
        Err(IndexError::ForeignOutput { .. })
    ));
}

#[test]
fn writer_refuses_authoritative_directories() {
    let fixture = Fixture::new();
    let generated = generate(&fixture.root).unwrap();
    let output = fixture.root.join("src/soma/RESEARCH/generated");
    assert!(matches!(
        write_generated(&fixture.root, &output, &generated),
        Err(IndexError::UnsafeOutput { .. })
    ));
    assert!(!output.exists());
}

#[test]
fn missing_allocation_is_a_typed_stop() {
    let fixture = Fixture::new();
    fixture.write(
        ".agents/COMMUNE/2026-07-15_fable-to-sol_unallocated.md",
        "# FABLE → SOL — unallocated\n",
    );
    assert!(matches!(
        generate(&fixture.root),
        Err(IndexError::MissingAllocation {
            kind,
            alias
        }) if kind == "correspondence" && alias.contains("unallocated")
    ));
}

#[test]
fn root_discovery_walks_up() {
    let fixture = Fixture::new();
    let nested = fixture.root.join("src/soma/body/src");
    assert_eq!(
        super::discover_laboratory_root(&nested).unwrap(),
        fixture.root
    );
}
