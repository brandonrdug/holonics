use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use crate::model::{
    AbiIdentifier, CorrespondenceEntry, CrateEntry, FormulaEntry, Inventory, LedgerEntry,
    ObservationEntry, PublicSymbol, RegistryRecord, ResearchEntry,
};
use crate::sha256;
use crate::IndexError;

const MARKS: [&str; 12] = [
    "EXACT",
    "DERIVED",
    "CHOSEN",
    "RATIFIED",
    "BUILT",
    "CUDA-MEASURED",
    "MEASURED",
    "OPEN",
    "FAILED",
    "SUPERSEDED",
    "PRESENTED",
    "DRAFT",
];

const ALLOCATION_FILE: &str = "src/soma/tools/record-index/allocations.tsv";

pub(crate) fn inventory(root: &Path) -> Result<Inventory, IndexError> {
    let mut collector = Collector::new(root);
    let allocation_text = collector.read_text(&root.join(ALLOCATION_FILE))?;
    let mut allocations = Allocations::parse(&root.join(ALLOCATION_FILE), &allocation_text)?;
    let mut inventory = Inventory::default();

    scan_formula(&mut collector, &mut allocations, &mut inventory)?;
    scan_research(&mut collector, &mut inventory)?;
    scan_observations(&mut collector, &mut allocations, &mut inventory)?;
    scan_correspondence(&mut collector, &mut allocations, &mut inventory)?;
    scan_ledger(&mut collector, &mut inventory)?;
    scan_rust(&mut collector, &mut inventory)?;
    allocations.require_all_used()?;

    inventory.source_hashes = collector.hashes;
    inventory.formula.sort_by_key(|entry| entry.line);
    inventory
        .research
        .sort_by(|left, right| left.source.cmp(&right.source));
    inventory
        .observations
        .sort_by(|left, right| left.source.cmp(&right.source));
    inventory
        .correspondence
        .sort_by(|left, right| left.source.cmp(&right.source));
    inventory.ledger.sort_by_key(|entry| entry.line);
    inventory
        .crates
        .sort_by(|left, right| left.manifest.cmp(&right.manifest));
    inventory.public_symbols.sort_by(|left, right| {
        (&left.source, left.line, &left.kind, &left.name).cmp(&(
            &right.source,
            right.line,
            &right.kind,
            &right.name,
        ))
    });
    inventory.abi.sort_by(|left, right| {
        (&left.source, left.line, &left.category, &left.name).cmp(&(
            &right.source,
            right.line,
            &right.category,
            &right.name,
        ))
    });
    Ok(inventory)
}

struct Collector<'a> {
    root: &'a Path,
    hashes: BTreeMap<String, String>,
}

impl<'a> Collector<'a> {
    fn new(root: &'a Path) -> Self {
        Self {
            root,
            hashes: BTreeMap::new(),
        }
    }

    fn read_text(&mut self, path: &Path) -> Result<String, IndexError> {
        if !path.is_file() {
            return Err(IndexError::MissingSource {
                path: path.to_path_buf(),
            });
        }
        let bytes = fs::read(path)
            .map_err(|source| IndexError::io("read source", path.to_path_buf(), source))?;
        let text = String::from_utf8(bytes.clone()).map_err(|source| {
            IndexError::invalid(path, None, format!("source is not valid UTF-8: {source}"))
        })?;
        let relative = relative_path(self.root, path)?;
        self.hashes.insert(relative, sha256::digest_hex(&bytes));
        Ok(text)
    }

    fn relative(&self, path: &Path) -> Result<String, IndexError> {
        relative_path(self.root, path)
    }

    fn hash_for(&self, relative: &str) -> Result<String, IndexError> {
        self.hashes.get(relative).cloned().ok_or_else(|| {
            IndexError::invalid(
                self.root.join(relative),
                None,
                "internal error: source was not fingerprinted",
            )
        })
    }
}

#[derive(Debug)]
struct Allocation {
    id: String,
    kind: String,
    alias: String,
    line: usize,
}

struct Allocations {
    path: PathBuf,
    by_alias: BTreeMap<(String, String), Allocation>,
    by_id: BTreeMap<String, (String, String)>,
    used: BTreeSet<(String, String)>,
}

impl Allocations {
    fn parse(path: &Path, text: &str) -> Result<Self, IndexError> {
        let mut by_alias = BTreeMap::new();
        let mut by_id = BTreeMap::new();
        for (index, raw) in text.lines().enumerate() {
            let line = index + 1;
            let raw = raw.trim_end();
            if raw.is_empty() || raw.starts_with('#') {
                continue;
            }
            let fields: Vec<_> = raw.split('\t').collect();
            if fields.len() != 3 {
                return Err(IndexError::invalid(
                    path,
                    Some(line),
                    "allocation row must be KIND<TAB>ID<TAB>ALIAS",
                ));
            }
            let kind = fields[0].to_string();
            let id = fields[1].to_string();
            let alias = fields[2].to_string();
            validate_allocation_id(path, line, &kind, &id)?;
            let key = (kind.clone(), alias.clone());
            if let Some(previous) = by_alias.insert(
                key.clone(),
                Allocation {
                    id: id.clone(),
                    kind: kind.clone(),
                    alias: alias.clone(),
                    line,
                },
            ) {
                return Err(IndexError::invalid(
                    path,
                    Some(line),
                    format!(
                        "alias {kind}:{alias} was already allocated at line {}",
                        previous.line
                    ),
                ));
            }
            if let Some((first_kind, first_alias)) =
                by_id.insert(id.clone(), (kind.clone(), alias.clone()))
            {
                return Err(IndexError::DuplicateId {
                    id,
                    first: format!("{first_kind}:{first_alias}"),
                    second: format!("{kind}:{alias}"),
                });
            }
        }
        Ok(Self {
            path: path.to_path_buf(),
            by_alias,
            by_id,
            used: BTreeSet::new(),
        })
    }

    fn resolve(&mut self, kind: &str, alias: &str) -> Result<String, IndexError> {
        let key = (kind.to_string(), alias.to_string());
        let allocation = self
            .by_alias
            .get(&key)
            .ok_or_else(|| IndexError::MissingAllocation {
                kind: kind.to_string(),
                alias: alias.to_string(),
            })?;
        debug_assert_eq!(allocation.kind, kind);
        debug_assert_eq!(allocation.alias, alias);
        self.used.insert(key);
        Ok(allocation.id.clone())
    }

    fn require_all_used(&self) -> Result<(), IndexError> {
        for (key, allocation) in &self.by_alias {
            if !self.used.contains(key) {
                return Err(IndexError::UnusedAllocation {
                    id: allocation.id.clone(),
                    alias: allocation.alias.clone(),
                });
            }
        }
        debug_assert_eq!(self.by_alias.len(), self.by_id.len());
        debug_assert!(self.path.is_file());
        Ok(())
    }
}

fn validate_allocation_id(
    path: &Path,
    line: usize,
    kind: &str,
    id: &str,
) -> Result<(), IndexError> {
    let prefix = match kind {
        "claim" => "CLM",
        "evidence" => "EVD",
        "observation" => "OBS",
        "correspondence" => "COR",
        _ => {
            return Err(IndexError::invalid(
                path,
                Some(line),
                format!("unknown allocation kind {kind:?}"),
            ));
        }
    };
    let parts: Vec<_> = id.split('-').collect();
    let valid = parts.len() == 3
        && parts[0] == prefix
        && parts[1].len() == 8
        && parts[1].bytes().all(|byte| byte.is_ascii_digit())
        && parts[2].len() == 4
        && parts[2].bytes().all(|byte| byte.is_ascii_digit());
    if !valid {
        return Err(IndexError::invalid(
            path,
            Some(line),
            format!("{kind} ID must have the form {prefix}-YYYYMMDD-NNNN"),
        ));
    }
    Ok(())
}

fn scan_formula(
    collector: &mut Collector<'_>,
    allocations: &mut Allocations,
    inventory: &mut Inventory,
) -> Result<(), IndexError> {
    let path = collector.root.join("src/soma/FORMULA.md");
    let source = collector.relative(&path)?;
    let text = collector.read_text(&path)?;
    let sha256 = collector.hash_for(&source)?;
    for (index, line) in text.lines().enumerate() {
        let Some((handle, title)) = formula_heading(line) else {
            continue;
        };
        let alias = format!("formula:{handle}");
        let id = allocations.resolve("claim", &alias)?;
        let entry = FormulaEntry {
            id: id.clone(),
            handle,
            title,
            marks: formula_heading_marks(line),
            source: source.clone(),
            line: index + 1,
            sha256: sha256.clone(),
        };
        insert_registry(
            inventory,
            RegistryRecord {
                id,
                kind: "claim".to_string(),
                alias,
                title: entry.title.clone(),
                source: entry.source.clone(),
                line: Some(entry.line),
                marks: entry.marks.clone(),
                sha256: Some(entry.sha256.clone()),
            },
        )?;
        inventory.formula.push(entry);
    }
    if inventory.formula.is_empty() {
        return Err(IndexError::invalid(
            path,
            None,
            "no Formula section headings were discovered",
        ));
    }
    Ok(())
}

fn formula_heading(line: &str) -> Option<(String, String)> {
    let content = if let Some(content) = line.strip_prefix("## ") {
        content
    } else {
        line.strip_prefix("### ")?
    };
    let content = content.trim_start_matches('§').trim();
    let (handle, title) = content.split_once('·')?;
    let handle = handle.trim();
    if !valid_formula_handle(handle) {
        return None;
    }
    Some((handle.to_string(), title.trim().to_string()))
}

fn valid_formula_handle(handle: &str) -> bool {
    let mut parts = handle.split('-');
    let Some(roman) = parts.next() else {
        return false;
    };
    if roman.is_empty() || !roman.bytes().all(|byte| b"IVXLCDM".contains(&byte)) {
        return false;
    }
    match (parts.next(), parts.next()) {
        (None, None) => true,
        (Some(suffix), None) => {
            !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_alphabetic())
        }
        _ => false,
    }
}

fn scan_research(
    collector: &mut Collector<'_>,
    inventory: &mut Inventory,
) -> Result<(), IndexError> {
    let directory = collector.root.join("src/soma/RESEARCH");
    for path in direct_files(&directory)? {
        if path.extension().and_then(|value| value.to_str()) != Some("md") {
            continue;
        }
        let source = collector.relative(&path)?;
        let text = collector.read_text(&path)?;
        let title = first_h1(&text).unwrap_or_else(|| file_stem(&path).unwrap_or_default());
        let stem = file_stem(&path)?;
        inventory.research.push(ResearchEntry {
            id: format!("discovery:research:{stem}"),
            date: filename_date(&stem).unwrap_or_else(|| "UNDECLARED".to_string()),
            title,
            marks: preamble_marks(&text),
            sha256: collector.hash_for(&source)?,
            source,
        });
    }
    Ok(())
}

fn scan_observations(
    collector: &mut Collector<'_>,
    allocations: &mut Allocations,
    inventory: &mut Inventory,
) -> Result<(), IndexError> {
    let directory = collector.root.join("src/soma/observations");
    let mut paths = walk_files(&directory, WalkKind::Documents)?;
    paths.retain(|path| {
        matches!(
            path.file_name().and_then(|value| value.to_str()),
            Some("RESULTS.md" | "PRODUCTION.md")
        )
    });
    for path in paths {
        let relative_observation = path.strip_prefix(&directory).map_err(|_| {
            IndexError::invalid(&path, None, "observation escaped its source directory")
        })?;
        let campaign = relative_observation
            .components()
            .next()
            .and_then(|component| component.as_os_str().to_str())
            .ok_or_else(|| IndexError::NonUtf8Path { path: path.clone() })?
            .to_string();
        let record_kind = path
            .file_stem()
            .and_then(|value| value.to_str())
            .ok_or_else(|| IndexError::NonUtf8Path { path: path.clone() })?
            .to_string();
        let source = collector.relative(&path)?;
        let observation_alias = format!("observation:{campaign}");
        let evidence_alias = format!("evidence:{source}");
        let observation_id = allocations.resolve("observation", &observation_alias)?;
        let evidence_id = allocations.resolve("evidence", &evidence_alias)?;
        let text = collector.read_text(&path)?;
        let title = first_h1(&text).unwrap_or_else(|| format!("{campaign} {record_kind}"));
        let sha256 = collector.hash_for(&source)?;
        let entry = ObservationEntry {
            observation_id: observation_id.clone(),
            evidence_id: evidence_id.clone(),
            campaign: campaign.clone(),
            record_kind,
            title: title.clone(),
            marks: preamble_marks(&text),
            source: source.clone(),
            sha256: sha256.clone(),
        };
        if !inventory.registry.contains_key(&observation_id) {
            insert_registry(
                inventory,
                RegistryRecord {
                    id: observation_id,
                    kind: "observation".to_string(),
                    alias: observation_alias,
                    title: campaign,
                    source: format!("src/soma/observations/{}", entry.campaign),
                    line: None,
                    marks: Vec::new(),
                    sha256: None,
                },
            )?;
        }
        insert_registry(
            inventory,
            RegistryRecord {
                id: evidence_id,
                kind: "evidence".to_string(),
                alias: evidence_alias,
                title,
                source,
                line: Some(1),
                marks: entry.marks.clone(),
                sha256: Some(sha256),
            },
        )?;
        inventory.observations.push(entry);
    }
    Ok(())
}

fn scan_correspondence(
    collector: &mut Collector<'_>,
    allocations: &mut Allocations,
    inventory: &mut Inventory,
) -> Result<(), IndexError> {
    let directory = collector.root.join(".agents/COMMUNE");
    for path in direct_files(&directory)? {
        if path.file_name().and_then(|value| value.to_str()) == Some("README.md")
            || path.extension().and_then(|value| value.to_str()) != Some("md")
        {
            continue;
        }
        let source = collector.relative(&path)?;
        let stem = file_stem(&path)?;
        let (date, from, to) = correspondence_route(&path, &stem)?;
        let alias = format!("correspondence:{source}");
        let id = allocations.resolve("correspondence", &alias)?;
        let text = collector.read_text(&path)?;
        let title = first_h1(&text).unwrap_or_else(|| stem.clone());
        let sha256 = collector.hash_for(&source)?;
        let entry = CorrespondenceEntry {
            id: id.clone(),
            date,
            from,
            to,
            title: title.clone(),
            marks: preamble_marks(&text),
            source: source.clone(),
            sha256: sha256.clone(),
        };
        insert_registry(
            inventory,
            RegistryRecord {
                id,
                kind: "correspondence".to_string(),
                alias,
                title,
                source,
                line: Some(1),
                marks: entry.marks.clone(),
                sha256: Some(sha256),
            },
        )?;
        inventory.correspondence.push(entry);
    }
    Ok(())
}

fn correspondence_route(path: &Path, stem: &str) -> Result<(String, String, String), IndexError> {
    let date = filename_date(stem).ok_or_else(|| {
        IndexError::invalid(
            path,
            None,
            "commune filename lacks a leading YYYY-MM-DD date",
        )
    })?;
    let route = stem
        .get(11..)
        .and_then(|rest| rest.split_once('_').map(|pair| pair.0))
        .ok_or_else(|| {
            IndexError::invalid(path, None, "commune filename lacks a route and slug")
        })?;
    let (from, to) = route.split_once("-to-").ok_or_else(|| {
        IndexError::invalid(path, None, "commune route must have the form FROM-to-TO")
    })?;
    if from.is_empty() || to.is_empty() {
        return Err(IndexError::invalid(
            path,
            None,
            "commune route has an empty endpoint",
        ));
    }
    Ok((date, from.to_string(), to.to_string()))
}

fn scan_ledger(collector: &mut Collector<'_>, inventory: &mut Inventory) -> Result<(), IndexError> {
    let path = collector.root.join("src/soma/LEDGER.md");
    let source = collector.relative(&path)?;
    let text = collector.read_text(&path)?;
    for (index, line) in text.lines().enumerate() {
        let content = line
            .strip_prefix("## ")
            .or_else(|| line.strip_prefix("### "));
        let Some(content) = content else {
            continue;
        };
        let Some(date) = date_in_heading(content) else {
            continue;
        };
        inventory.ledger.push(LedgerEntry {
            date,
            title: content.trim().to_string(),
            marks: lexical_marks(content),
            source: source.clone(),
            line: index + 1,
        });
    }
    Ok(())
}

fn scan_rust(collector: &mut Collector<'_>, inventory: &mut Inventory) -> Result<(), IndexError> {
    let soma = collector.root.join("src/soma");
    let workspace_manifest = soma.join("Cargo.toml");
    let workspace_text = collector.read_text(&workspace_manifest)?;
    let members = parse_workspace_members(&workspace_manifest, &workspace_text)?;
    let mut manifests = walk_files(&soma, WalkKind::RustSources)?;
    manifests
        .retain(|path| path.file_name().and_then(|value| value.to_str()) == Some("Cargo.toml"));

    for manifest in manifests {
        let manifest_source = collector.relative(&manifest)?;
        let text = if manifest == workspace_manifest {
            workspace_text.clone()
        } else {
            collector.read_text(&manifest)?
        };
        let Some(name) = parse_package_name(&manifest, &text)? else {
            continue;
        };
        let crate_dir = manifest.parent().expect("a manifest always has a parent");
        let crate_relative = relative_path(&soma, crate_dir)?;
        let relationship = if members.contains(&crate_relative) {
            "workspace-member"
        } else if has_empty_workspace_table(&text) {
            "detached-workspace"
        } else {
            "discovered-package"
        };
        inventory.crates.push(CrateEntry {
            id: format!("discovery:crate:{crate_relative}"),
            name: name.clone(),
            relationship: relationship.to_string(),
            manifest: manifest_source.clone(),
            sha256: collector.hash_for(&manifest_source)?,
        });

        let source_dir = crate_dir.join("src");
        if !source_dir.is_dir() {
            continue;
        }
        let mut rust_sources = walk_files(&source_dir, WalkKind::RustSources)?;
        rust_sources.retain(|path| path.extension().and_then(|value| value.to_str()) == Some("rs"));
        for rust_path in rust_sources {
            let source = collector.relative(&rust_path)?;
            let rust = collector.read_text(&rust_path)?;
            scan_rust_source(&name, &source, &rust, inventory)?;
        }
    }
    Ok(())
}

fn parse_workspace_members(path: &Path, text: &str) -> Result<BTreeSet<String>, IndexError> {
    let mut in_workspace = false;
    let mut collecting = false;
    let mut buffer = String::new();
    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with('[') {
            in_workspace = trimmed == "[workspace]";
        }
        if in_workspace && !collecting && trimmed.starts_with("members") {
            let (_, rest) = trimmed.split_once('=').ok_or_else(|| {
                IndexError::invalid(path, None, "workspace members assignment lacks '='")
            })?;
            collecting = true;
            buffer.push_str(rest);
            buffer.push('\n');
            if rest.contains(']') {
                break;
            }
        } else if collecting {
            buffer.push_str(trimmed);
            buffer.push('\n');
            if trimmed.contains(']') {
                break;
            }
        }
    }
    if !collecting {
        return Err(IndexError::invalid(
            path,
            None,
            "workspace has no members assignment",
        ));
    }
    let values = quoted_strings(&buffer);
    if values.is_empty() {
        return Err(IndexError::invalid(
            path,
            None,
            "workspace members assignment is empty or unsupported",
        ));
    }
    Ok(values.into_iter().collect())
}

fn quoted_strings(text: &str) -> Vec<String> {
    let mut values = Vec::new();
    let mut current = String::new();
    let mut quoted = false;
    let mut escaped = false;
    for character in text.chars() {
        if !quoted {
            if character == '"' {
                quoted = true;
                current.clear();
            }
            continue;
        }
        if escaped {
            current.push(character);
            escaped = false;
        } else if character == '\\' {
            escaped = true;
        } else if character == '"' {
            quoted = false;
            values.push(current.clone());
        } else {
            current.push(character);
        }
    }
    values
}

fn parse_package_name(path: &Path, text: &str) -> Result<Option<String>, IndexError> {
    let mut in_package = false;
    let mut saw_package = false;
    for (index, line) in text.lines().enumerate() {
        let trimmed = strip_comment(line).trim();
        if trimmed.starts_with('[') {
            in_package = trimmed == "[package]";
            saw_package |= in_package;
            continue;
        }
        if in_package && trimmed.starts_with("name") {
            let (_, value) = trimmed.split_once('=').ok_or_else(|| {
                IndexError::invalid(path, Some(index + 1), "package name lacks '='")
            })?;
            let value = value.trim();
            if value.len() < 2 || !value.starts_with('"') || !value.ends_with('"') {
                return Err(IndexError::invalid(
                    path,
                    Some(index + 1),
                    "package name must be one quoted string",
                ));
            }
            return Ok(Some(value[1..value.len() - 1].to_string()));
        }
    }
    if saw_package {
        Err(IndexError::invalid(path, None, "[package] has no name"))
    } else {
        Ok(None)
    }
}

fn has_empty_workspace_table(text: &str) -> bool {
    text.lines().any(|line| line.trim() == "[workspace]")
}

fn scan_rust_source(
    crate_name: &str,
    source: &str,
    text: &str,
    inventory: &mut Inventory,
) -> Result<(), IndexError> {
    let lines: Vec<_> = text.lines().collect();
    let mut pending_kernel = None;
    for (index, line) in lines.iter().enumerate() {
        let number = index + 1;
        let trimmed = strip_comment(line).trim();
        if trimmed.starts_with("#[") && trimmed.contains("no_mangle") {
            pending_kernel = Some("kernel-entry");
        } else if trimmed.starts_with("#[") && trimmed.contains("spirv(compute") {
            pending_kernel = Some("spirv-entry");
        }

        if let Some((kind, name)) = public_declaration(trimmed) {
            inventory.public_symbols.push(PublicSymbol {
                crate_name: crate_name.to_string(),
                kind,
                name,
                source: source.to_string(),
                line: number,
            });
        }

        if let Some(category) = pending_kernel {
            if let Some(name) = function_name(trimmed) {
                inventory.abi.push(AbiIdentifier {
                    id: discovery_abi_id(crate_name, source, &name),
                    category: category.to_string(),
                    crate_name: crate_name.to_string(),
                    name,
                    declaration: normalize_declaration(trimmed, 240),
                    source: source.to_string(),
                    line: number,
                });
                pending_kernel = None;
            } else if !trimmed.is_empty()
                && !trimmed.starts_with("#[")
                && !trimmed.starts_with("///")
            {
                pending_kernel = None;
            }
        }

        if let Some(name) = const_name(trimmed) {
            if abi_constant_name(&name) {
                let declaration = declaration_from(&lines, index);
                let category = abi_category(source, &name);
                inventory.abi.push(AbiIdentifier {
                    id: discovery_abi_id(crate_name, source, &name),
                    category: category.to_string(),
                    crate_name: crate_name.to_string(),
                    name,
                    declaration,
                    source: source.to_string(),
                    line: number,
                });
            }
        }
    }

    let mut seen = BTreeSet::new();
    inventory
        .abi
        .retain(|entry| seen.insert((entry.source.clone(), entry.line, entry.name.clone())));
    Ok(())
}

fn public_declaration(line: &str) -> Option<(String, String)> {
    if !line.starts_with("pub ") {
        return None;
    }
    let tokens = identifiers(line);
    if tokens.first().map(String::as_str) != Some("pub") {
        return None;
    }
    if let Some(index) = tokens.iter().position(|token| token == "fn") {
        return Some(("fn".to_string(), tokens.get(index + 1)?.clone()));
    }
    for kind in [
        "struct", "enum", "trait", "union", "type", "static", "const", "mod", "macro",
    ] {
        if let Some(index) = tokens.iter().position(|token| token == kind) {
            return Some((kind.to_string(), tokens.get(index + 1)?.clone()));
        }
    }
    if line.starts_with("pub use ") {
        return Some((
            "use".to_string(),
            normalize_declaration(line.trim_start_matches("pub use "), 160),
        ));
    }
    None
}

fn function_name(line: &str) -> Option<String> {
    let tokens = identifiers(line);
    let index = tokens.iter().position(|token| token == "fn")?;
    tokens.get(index + 1).cloned()
}

fn const_name(line: &str) -> Option<String> {
    let tokens = identifiers(line);
    let index = tokens
        .iter()
        .position(|token| token == "const" || token == "static")?;
    let name = tokens.get(index + 1)?;
    if name == "fn"
        || !name
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
    {
        None
    } else {
        Some(name.clone())
    }
}

fn identifiers(line: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    for character in line.chars() {
        if character.is_ascii_alphanumeric() || character == '_' {
            current.push(character);
        } else if !current.is_empty() {
            tokens.push(std::mem::take(&mut current));
        }
    }
    if !current.is_empty() {
        tokens.push(current);
    }
    tokens
}

fn abi_constant_name(name: &str) -> bool {
    [
        "ABI",
        "MAGIC",
        "VERSION",
        "SCHEMA",
        "LAYOUT",
        "WIRE",
        "WORDS",
        "WORD_",
        "_WORD",
        "OFFSET",
        "STRIDE",
        "HEADER",
        "RECORD",
        "STATUS",
        "REGISTER",
        "CONTACT",
        "CARRIER",
        "RADIATION",
        "COMPLETION",
        "OWN_CELL",
        "OWN_REGISTER",
    ]
    .iter()
    .any(|fragment| name.contains(fragment))
}

fn abi_category(source: &str, name: &str) -> &'static str {
    if source.contains("surface/src")
        || ["SLEEP", "ARCHIVE", "MAGIC", "VERSION", "SCHEMA", "WIRE"]
            .iter()
            .any(|fragment| name.contains(fragment))
    {
        "archive-or-schema"
    } else {
        "word-layout"
    }
}

fn discovery_abi_id(crate_name: &str, source: &str, name: &str) -> String {
    format!("discovery:abi:{}:{}:{}", crate_name, source, name)
}

fn declaration_from(lines: &[&str], start: usize) -> String {
    let mut declaration = String::new();
    for line in lines.iter().skip(start).take(8) {
        let line = strip_comment(line).trim();
        if !line.is_empty() {
            if !declaration.is_empty() {
                declaration.push(' ');
            }
            declaration.push_str(line);
        }
        if line.contains(';') {
            break;
        }
    }
    normalize_declaration(&declaration, 240)
}

fn normalize_declaration(value: &str, limit: usize) -> String {
    let normalized = value.split_whitespace().collect::<Vec<_>>().join(" ");
    if normalized.chars().count() <= limit {
        normalized
    } else {
        let mut truncated: String = normalized.chars().take(limit.saturating_sub(1)).collect();
        truncated.push('…');
        truncated
    }
}

fn insert_registry(inventory: &mut Inventory, record: RegistryRecord) -> Result<(), IndexError> {
    if let Some(previous) = inventory.registry.insert(record.id.clone(), record.clone()) {
        return Err(IndexError::DuplicateId {
            id: record.id,
            first: previous.source,
            second: record.source,
        });
    }
    Ok(())
}

fn lexical_marks(text: &str) -> Vec<&'static str> {
    let uppercase = text.to_uppercase();
    MARKS
        .iter()
        .copied()
        .filter(|mark| contains_mark(&uppercase, mark))
        .collect()
}

fn formula_heading_marks(heading: &str) -> Vec<&'static str> {
    let mut found = BTreeSet::new();
    for mark in MARKS {
        if contains_mark(heading, mark) {
            found.insert(mark);
        }
    }
    let mut rest = heading;
    while let Some((_, after_open)) = rest.split_once('(') {
        let Some((parenthetical, after_close)) = after_open.split_once(')') else {
            break;
        };
        if date_in_heading(parenthetical).is_some() {
            found.extend(lexical_marks(parenthetical));
        }
        rest = after_close;
    }
    MARKS
        .iter()
        .copied()
        .filter(|mark| found.contains(mark))
        .collect()
}

fn contains_mark(text: &str, mark: &str) -> bool {
    text.match_indices(mark).any(|(start, value)| {
        if mark == "MEASURED" && text[..start].ends_with("CUDA-") {
            return false;
        }
        let before = text[..start].chars().next_back();
        let after = text[start + value.len()..].chars().next();
        !before.is_some_and(|character| character.is_ascii_alphanumeric() || character == '_')
            && !after.is_some_and(|character| character.is_ascii_alphanumeric() || character == '_')
    })
}

fn preamble_marks(text: &str) -> Vec<&'static str> {
    let mut preamble = String::new();
    for line in text.lines() {
        if line.starts_with("## ") {
            break;
        }
        preamble.push_str(line);
        preamble.push('\n');
    }
    lexical_marks(&preamble)
}

fn first_h1(text: &str) -> Option<String> {
    text.lines().find_map(|line| {
        line.strip_prefix("# ")
            .map(|title| title.trim().to_string())
    })
}

fn filename_date(stem: &str) -> Option<String> {
    let date = stem.get(..10)?;
    if valid_date(date) {
        Some(date.to_string())
    } else {
        None
    }
}

fn date_in_heading(heading: &str) -> Option<String> {
    heading
        .as_bytes()
        .windows(10)
        .filter_map(|window| std::str::from_utf8(window).ok())
        .find(|candidate| valid_date(candidate))
        .map(str::to_string)
}

fn valid_date(value: &str) -> bool {
    value.len() == 10
        && value.as_bytes()[4] == b'-'
        && value.as_bytes()[7] == b'-'
        && value
            .bytes()
            .enumerate()
            .all(|(index, byte)| matches!(index, 4 | 7) || byte.is_ascii_digit())
}

fn strip_comment(line: &str) -> &str {
    line.split_once("//").map_or(line, |(before, _)| before)
}

fn direct_files(directory: &Path) -> Result<Vec<PathBuf>, IndexError> {
    if !directory.is_dir() {
        return Err(IndexError::MissingSource {
            path: directory.to_path_buf(),
        });
    }
    let entries = fs::read_dir(directory).map_err(|source| {
        IndexError::io("read source directory", directory.to_path_buf(), source)
    })?;
    let mut files = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|source| {
            IndexError::io(
                "read source directory entry",
                directory.to_path_buf(),
                source,
            )
        })?;
        let file_type = entry
            .file_type()
            .map_err(|source| IndexError::io("read source file type", entry.path(), source))?;
        if file_type.is_file() {
            files.push(entry.path());
        }
    }
    files.sort();
    Ok(files)
}

#[derive(Clone, Copy)]
enum WalkKind {
    Documents,
    RustSources,
}

fn walk_files(directory: &Path, kind: WalkKind) -> Result<Vec<PathBuf>, IndexError> {
    if !directory.is_dir() {
        return Err(IndexError::MissingSource {
            path: directory.to_path_buf(),
        });
    }
    let mut pending = vec![directory.to_path_buf()];
    let mut files = Vec::new();
    while let Some(current) = pending.pop() {
        let entries = fs::read_dir(&current)
            .map_err(|source| IndexError::io("walk source directory", current.clone(), source))?;
        let mut children = Vec::new();
        for entry in entries {
            let entry = entry.map_err(|source| {
                IndexError::io("walk source directory entry", current.clone(), source)
            })?;
            children.push(entry);
        }
        children.sort_by_key(|entry| entry.file_name());
        for entry in children.into_iter().rev() {
            let path = entry.path();
            let file_type = entry
                .file_type()
                .map_err(|source| IndexError::io("read source file type", path.clone(), source))?;
            if file_type.is_symlink() {
                continue;
            }
            if file_type.is_dir() {
                let name = entry.file_name();
                let name = name
                    .to_str()
                    .ok_or_else(|| IndexError::NonUtf8Path { path: path.clone() })?;
                if skip_directory(name, kind) {
                    continue;
                }
                pending.push(path);
            } else if file_type.is_file() {
                files.push(path);
            }
        }
    }
    files.sort();
    Ok(files)
}

fn skip_directory(name: &str, kind: WalkKind) -> bool {
    if matches!(
        name,
        "target" | ".git" | ".ruff_cache" | "__pycache__" | "generated"
    ) {
        return true;
    }
    match kind {
        WalkKind::Documents => false,
        WalkKind::RustSources => matches!(name, "diet" | "observations"),
    }
}

fn relative_path(root: &Path, path: &Path) -> Result<String, IndexError> {
    let relative = path.strip_prefix(root).map_err(|_| {
        IndexError::invalid(path, None, "source path is outside the laboratory root")
    })?;
    let mut rendered = String::new();
    for component in relative.components() {
        let value = component
            .as_os_str()
            .to_str()
            .ok_or_else(|| IndexError::NonUtf8Path {
                path: path.to_path_buf(),
            })?;
        if !rendered.is_empty() {
            rendered.push('/');
        }
        rendered.push_str(value);
    }
    Ok(rendered)
}

fn file_stem(path: &Path) -> Result<String, IndexError> {
    path.file_stem()
        .and_then(|value| value.to_str())
        .map(str::to_string)
        .ok_or_else(|| IndexError::NonUtf8Path {
            path: path.to_path_buf(),
        })
}

#[cfg(test)]
mod tests {
    use super::{
        formula_heading, formula_heading_marks, lexical_marks, parse_package_name,
        public_declaration, quoted_strings, valid_formula_handle,
    };
    use std::path::Path;

    #[test]
    fn formula_handles_are_conservative() {
        assert!(valid_formula_handle("XXVIII-b"));
        assert_eq!(
            formula_heading("## XXVIII-b · THE STROKE (RATIFIED)"),
            Some(("XXVIII-b".to_string(), "THE STROKE (RATIFIED)".to_string()))
        );
        assert_eq!(
            formula_heading("### §XXV-b · THE NECK"),
            Some(("XXV-b".to_string(), "THE NECK".to_string()))
        );
        assert_eq!(formula_heading("## Verdict"), None);
    }

    #[test]
    fn marks_require_token_boundaries() {
        assert_eq!(
            lexical_marks("(RATIFIED, BUILT)"),
            vec!["RATIFIED", "BUILT"]
        );
        assert!(lexical_marks("unratified").is_empty());
    }

    #[test]
    fn formula_marks_do_not_promote_incidental_heading_words() {
        assert!(
            formula_heading_marks("## IV · THE POLE (the cut this space is built around)")
                .is_empty()
        );
        assert_eq!(
            formula_heading_marks("## XIV · THE PRECESSION (2026-07-09; checked, built, measured)"),
            vec!["BUILT", "MEASURED"]
        );
        assert_eq!(
            formula_heading_marks("## LV · CONTACT (2026-07-14; RATIFIED, BUILT, CUDA-MEASURED)"),
            vec!["RATIFIED", "BUILT", "CUDA-MEASURED"]
        );
    }

    #[test]
    fn public_declarations_are_lexical_and_external() {
        assert_eq!(
            public_declaration("pub unsafe extern \"C\" fn cross() {"),
            Some(("fn".to_string(), "cross".to_string()))
        );
        assert_eq!(
            public_declaration("pub const fn words() -> usize {"),
            Some(("fn".to_string(), "words".to_string()))
        );
        assert_eq!(public_declaration("pub(crate) fn hidden() {}"), None);
    }

    #[test]
    fn tiny_toml_reads_package_and_arrays() {
        assert_eq!(
            quoted_strings("[\"body\", \"tools/record-index\"]"),
            vec!["body", "tools/record-index"]
        );
        assert_eq!(
            parse_package_name(Path::new("Cargo.toml"), "[package]\nname = \"body\"\n").unwrap(),
            Some("body".to_string())
        );
    }
}
