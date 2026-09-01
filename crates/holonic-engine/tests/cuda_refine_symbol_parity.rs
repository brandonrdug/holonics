use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

const CUDA_SOURCE: &str = include_str!("../kernels/refine_shell.cu");
const RUST_SOURCE: &str = include_str!("../src/cuda_refine.rs");

fn cuda_entries(source: &str) -> BTreeSet<String> {
    source
        .split("extern \"C\" __global__ void")
        .skip(1)
        .filter_map(|tail| {
            tail.trim_start()
                .split(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
                .next()
        })
        .filter(|name| !name.is_empty())
        .map(str::to_owned)
        .collect()
}

fn quoted_include(line: &str) -> Option<&str> {
    let include = line.trim_start().strip_prefix("#include \"")?;
    include.strip_suffix('"')
}

fn cuda_entries_from_include_closure(root: &Path) -> BTreeSet<String> {
    let mut pending = vec![root.to_path_buf()];
    let mut visited = BTreeSet::<PathBuf>::new();
    let mut entries = BTreeSet::new();
    while let Some(path) = pending.pop() {
        if !visited.insert(path.clone()) {
            continue;
        }
        let source = fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("cannot read CUDA include {path:?}: {error}"));
        entries.extend(cuda_entries(&source));
        let parent = path
            .parent()
            .unwrap_or_else(|| panic!("CUDA include has no parent: {path:?}"));
        for include in source.lines().filter_map(quoted_include) {
            let child = parent.join(include);
            if !child.is_file() {
                panic!("CUDA quoted include is missing: {child:?}");
            }
            pending.push(child);
        }
    }
    entries
}

fn rust_loaded_symbols(source: &str) -> BTreeSet<String> {
    source
        .split("c\"")
        .skip(1)
        .filter_map(|tail| tail.split('"').next())
        .filter(|name| {
            !name.is_empty()
                && name
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        })
        .map(str::to_owned)
        .collect()
}

fn rust_loaded_symbols_from_owner(root: &Path) -> BTreeSet<String> {
    let mut pending = vec![root.to_path_buf(), root.with_extension("")];
    let mut symbols = BTreeSet::new();
    while let Some(path) = pending.pop() {
        if path.is_dir() {
            let entries = fs::read_dir(&path).unwrap_or_else(|error| {
                panic!("cannot read Rust owner directory {path:?}: {error}")
            });
            pending.extend(entries.map(|entry| {
                entry
                    .unwrap_or_else(|error| {
                        panic!("cannot read entry in Rust owner directory {path:?}: {error}")
                    })
                    .path()
            }));
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            let source = fs::read_to_string(&path)
                .unwrap_or_else(|error| panic!("cannot read Rust owner {path:?}: {error}"));
            symbols.extend(rust_loaded_symbols(&source));
        }
    }
    symbols
}

#[test]
fn every_cuda_entry_is_loaded_or_explicitly_quarantined() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("kernels/refine_shell.cu");
    let rust_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/cuda_refine.rs");
    assert_eq!(
        fs::read_to_string(&root).expect("refine shell source"),
        CUDA_SOURCE
    );
    let cuda = cuda_entries_from_include_closure(&root);
    assert_eq!(
        fs::read_to_string(&rust_root).expect("refine Rust owner"),
        RUST_SOURCE
    );
    let rust = rust_loaded_symbols_from_owner(&rust_root);

    let missing_from_cuda = rust.difference(&cuda).cloned().collect::<Vec<_>>();
    assert!(
        missing_from_cuda.is_empty(),
        "Rust loads CUDA symbols which refine_shell.cu does not define: {missing_from_cuda:?}"
    );

    // These two target-state-local receiver variants are retained for a separate conduct audit.
    // Current production deliberately loads the complete-receiver variants instead. Keeping this
    // finite list here makes that standing explicit while refusing every new unowned entry.
    let quarantined = BTreeSet::from([
        "select_membrane_boundary_phase_front_target_state_direct".to_owned(),
        "select_membrane_situated_output_pairing_front_target_state_direct".to_owned(),
    ]);
    let unowned = cuda.difference(&rust).cloned().collect::<BTreeSet<_>>();
    assert_eq!(unowned, quarantined);
}
