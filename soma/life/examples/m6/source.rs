//! The content-addressed development occurrence for M6 / Athena-A0.
//!
//! This is an apparatus mouth, not a theorem router.  `prepare` is allowed to consult Git and
//! writes exactly one historical tree.  `mount` has no Git or repository argument: it opens only
//! the manifest and the files that manifest addresses, refuses path escape and unexpected files,
//! and returns the exact opened population.  The productive process uses only `mount`.

use std::{
    collections::BTreeSet,
    fs,
    io::{BufRead, BufReader, Read, Write},
    path::{Component, Path},
    process::{Command, Stdio},
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

pub const SOURCE_REVISION: &str = "75597c4";
pub const SOURCE_ROOT: &str = "soma/formal/elementary-holonics";
pub const MANIFEST: &str = "source-manifest.json";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceFileFace {
    pub relative_path: String,
    pub git_blob: String,
    pub octets: u64,
    pub sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceManifest {
    pub schema: String,
    pub occurrence: String,
    pub revision: String,
    pub source_root: String,
    pub git_tree: String,
    pub content_sha256: String,
    pub files: Vec<SourceFileFace>,
}

#[derive(Debug)]
pub struct MountedSource {
    pub manifest: SourceManifest,
    pub opened_paths: Vec<String>,
}

pub fn prepare(workspace: &Path, destination: &Path) -> Result<SourceManifest, String> {
    if destination.exists() {
        return Err(format!(
            "source destination already exists: {}",
            destination.display()
        ));
    }
    fs::create_dir_all(destination)
        .map_err(|error| format!("create {}: {error}", destination.display()))?;

    let tree = git_text(
        workspace,
        &["rev-parse", &format!("{SOURCE_REVISION}:{SOURCE_ROOT}")],
    )?;
    let listing = git_bytes(
        workspace,
        &[
            "ls-tree",
            "-r",
            "-z",
            "-l",
            SOURCE_REVISION,
            "--",
            SOURCE_ROOT,
        ],
    )?;
    let mut declared = Vec::new();
    for row in listing
        .split(|octet| *octet == 0)
        .filter(|row| !row.is_empty())
    {
        let row = std::str::from_utf8(row)
            .map_err(|error| format!("Git tree row is not UTF-8: {error}"))?;
        let (standing, path) = row
            .split_once('\t')
            .ok_or_else(|| format!("Git tree row has no path: {row}"))?;
        let fields = standing.split_ascii_whitespace().collect::<Vec<_>>();
        if fields.len() != 4 || fields[1] != "blob" {
            return Err(format!("unsupported Git tree row: {row}"));
        }
        let relative = path
            .strip_prefix(&format!("{SOURCE_ROOT}/"))
            .ok_or_else(|| format!("Git returned a path outside the source root: {path}"))?;
        lawful_relative(relative)?;
        let declared_octets = fields[3]
            .parse::<u64>()
            .map_err(|error| format!("Git size for {path}: {error}"))?;
        declared.push((relative.to_owned(), fields[2].to_owned(), declared_octets));
    }
    declared.sort_by(|left, right| left.0.cmp(&right.0));
    if declared.is_empty() {
        return Err("the historical source tree is empty".to_owned());
    }

    // One Git process carries the whole blob population.  Spawning one `cat-file` per source was
    // an apparatus serialization unrelated to the source topology and dominated this bounded deed.
    let mut batch = Command::new("git")
        .arg("-C")
        .arg(workspace)
        .args(["cat-file", "--batch"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("open Git blob batch: {error}"))?;
    {
        let input = batch
            .stdin
            .as_mut()
            .ok_or_else(|| "Git blob batch has no input".to_owned())?;
        for (_, blob, _) in &declared {
            writeln!(input, "{blob}")
                .map_err(|error| format!("write Git blob request: {error}"))?;
        }
    }
    drop(batch.stdin.take());
    let output = batch
        .stdout
        .take()
        .ok_or_else(|| "Git blob batch has no output".to_owned())?;
    let mut output = BufReader::new(output);
    let mut files = Vec::with_capacity(declared.len());
    for (relative, blob, declared_octets) in declared {
        let mut header = String::new();
        output
            .read_line(&mut header)
            .map_err(|error| format!("read Git blob header for {relative}: {error}"))?;
        let fields = header.split_ascii_whitespace().collect::<Vec<_>>();
        if fields.len() != 3 || fields[0] != blob || fields[1] != "blob" {
            return Err(format!(
                "Git blob header disagrees for {relative}: {header}"
            ));
        }
        let batch_octets = fields[2]
            .parse::<u64>()
            .map_err(|error| format!("Git batch size for {relative}: {error}"))?;
        if batch_octets != declared_octets {
            return Err(format!(
                "Git tree and batch extent disagree for {relative}: {declared_octets} != {batch_octets}"
            ));
        }
        let extent = usize::try_from(batch_octets).map_err(|_| "source file extent".to_owned())?;
        let mut bytes = vec![0u8; extent];
        output
            .read_exact(&mut bytes)
            .map_err(|error| format!("read Git blob {relative}: {error}"))?;
        let mut delimiter = [0u8; 1];
        output
            .read_exact(&mut delimiter)
            .map_err(|error| format!("read Git blob delimiter {relative}: {error}"))?;
        if delimiter != [b'\n'] {
            return Err(format!("Git blob delimiter moved for {relative}"));
        }
        let octets = u64::try_from(bytes.len()).map_err(|_| "source file extent".to_owned())?;
        if octets != declared_octets {
            return Err(format!(
                "Git tree and blob extent disagree for {relative}: {declared_octets} != {octets}"
            ));
        }
        let target = destination.join(&relative);
        if let Some(parent) = target.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| format!("create {}: {error}", parent.display()))?;
        }
        fs::write(&target, &bytes)
            .map_err(|error| format!("write {}: {error}", target.display()))?;
        files.push(SourceFileFace {
            relative_path: relative,
            git_blob: blob,
            octets,
            sha256: sha256(&bytes),
        });
    }
    let status = batch
        .wait_with_output()
        .map_err(|error| format!("close Git blob batch: {error}"))?;
    if !status.status.success() {
        return Err(format!(
            "Git blob batch refused: {}",
            String::from_utf8_lossy(&status.stderr)
        ));
    }
    let content_sha256 = population_digest(&files);
    let manifest = SourceManifest {
        schema: "holonics.m6.formal-source-occurrence.v1".to_owned(),
        occurrence: format!("athena-a0/source/{SOURCE_REVISION}/{tree}"),
        revision: SOURCE_REVISION.to_owned(),
        source_root: SOURCE_ROOT.to_owned(),
        git_tree: tree,
        content_sha256,
        files,
    };
    write_json(&destination.join(MANIFEST), &manifest)?;
    Ok(manifest)
}

pub fn mount(source: &Path) -> Result<MountedSource, String> {
    let manifest_path = source.join(MANIFEST);
    let manifest_bytes = fs::read(&manifest_path)
        .map_err(|error| format!("read {}: {error}", manifest_path.display()))?;
    let manifest: SourceManifest = serde_json::from_slice(&manifest_bytes)
        .map_err(|error| format!("decode {}: {error}", manifest_path.display()))?;
    if manifest.schema != "holonics.m6.formal-source-occurrence.v1"
        || manifest.revision != SOURCE_REVISION
        || manifest.source_root != SOURCE_ROOT
        || manifest.files.is_empty()
    {
        return Err("the formal-source manifest is not the admitted M6 occurrence".to_owned());
    }
    if manifest.content_sha256 != population_digest(&manifest.files) {
        return Err("the formal-source population address moved".to_owned());
    }

    let mut prior: Option<&str> = None;
    let mut expected = BTreeSet::from([MANIFEST.to_owned()]);
    let mut opened_paths = vec![MANIFEST.to_owned()];
    for face in &manifest.files {
        lawful_relative(&face.relative_path)?;
        if prior.is_some_and(|held| held >= face.relative_path.as_str()) {
            return Err("the formal-source manifest is not strictly ordered".to_owned());
        }
        prior = Some(&face.relative_path);
        if !expected.insert(face.relative_path.clone()) {
            return Err(format!("duplicate source path {}", face.relative_path));
        }
        let path = source.join(&face.relative_path);
        let bytes = fs::read(&path).map_err(|error| format!("read {}: {error}", path.display()))?;
        let octets = u64::try_from(bytes.len()).map_err(|_| "source file extent".to_owned())?;
        if octets != face.octets || sha256(&bytes) != face.sha256 {
            return Err(format!("source file moved: {}", face.relative_path));
        }
        opened_paths.push(face.relative_path.clone());
    }
    let actual = relative_files(source)?;
    if actual != expected {
        let unexpected = actual.difference(&expected).cloned().collect::<Vec<_>>();
        let absent = expected.difference(&actual).cloned().collect::<Vec<_>>();
        return Err(format!(
            "the formal-source directory differs from its manifest; unexpected {unexpected:?}, absent {absent:?}"
        ));
    }
    Ok(MountedSource {
        manifest,
        opened_paths,
    })
}

fn git_text(workspace: &Path, arguments: &[&str]) -> Result<String, String> {
    let bytes = git_bytes(workspace, arguments)?;
    String::from_utf8(bytes)
        .map(|text| text.trim().to_owned())
        .map_err(|error| format!("Git returned non-UTF-8 text: {error}"))
}

fn git_bytes(workspace: &Path, arguments: &[&str]) -> Result<Vec<u8>, String> {
    let returned = Command::new("git")
        .arg("-C")
        .arg(workspace)
        .args(arguments)
        .output()
        .map_err(|error| format!("execute git {arguments:?}: {error}"))?;
    if !returned.status.success() {
        return Err(format!(
            "git {arguments:?} refused: {}",
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    Ok(returned.stdout)
}

fn lawful_relative(relative: &str) -> Result<(), String> {
    if relative.is_empty() {
        return Err("an empty source path was declared".to_owned());
    }
    let path = Path::new(relative);
    if path.is_absolute()
        || path
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err(format!("source path escapes its occurrence: {relative}"));
    }
    Ok(())
}

fn relative_files(root: &Path) -> Result<BTreeSet<String>, String> {
    fn walk(root: &Path, at: &Path, out: &mut BTreeSet<String>) -> Result<(), String> {
        let mut entries = fs::read_dir(at)
            .map_err(|error| format!("read directory {}: {error}", at.display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| format!("read directory {}: {error}", at.display()))?;
        entries.sort_by_key(|entry| entry.file_name());
        for entry in entries {
            let kind = entry
                .file_type()
                .map_err(|error| format!("read type {}: {error}", entry.path().display()))?;
            if kind.is_symlink() {
                return Err(format!(
                    "source occurrence contains a symlink: {}",
                    entry.path().display()
                ));
            }
            if kind.is_dir() {
                walk(root, &entry.path(), out)?;
            } else if kind.is_file() {
                let relative = entry
                    .path()
                    .strip_prefix(root)
                    .map_err(|error| format!("source path rebase: {error}"))?
                    .to_string_lossy()
                    .replace('\\', "/");
                lawful_relative(&relative)?;
                out.insert(relative);
            } else {
                return Err(format!(
                    "unsupported source occurrence entry: {}",
                    entry.path().display()
                ));
            }
        }
        Ok(())
    }
    let mut files = BTreeSet::new();
    walk(root, root, &mut files)?;
    Ok(files)
}

fn population_digest(files: &[SourceFileFace]) -> String {
    let mut hasher = Sha256::new();
    for file in files {
        framed(&mut hasher, file.relative_path.as_bytes());
        framed(&mut hasher, file.git_blob.as_bytes());
        framed(&mut hasher, &file.octets.to_le_bytes());
        framed(&mut hasher, file.sha256.as_bytes());
    }
    hex(&hasher.finalize())
}

fn framed(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

pub fn sha256(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|octet| format!("{octet:02x}")).collect()
}

pub fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    let bytes = serde_json::to_vec_pretty(value)
        .map_err(|error| format!("encode {}: {error}", path.display()))?;
    fs::write(path, bytes).map_err(|error| format!("write {}: {error}", path.display()))
}
