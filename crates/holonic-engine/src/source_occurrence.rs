//! **The source occurrence a resident passage binds to, authenticated by content — the file, the
//! symbol, the slice, the field, the shape and the region.**
//!
//! Occasion, 2026-08-18: the audit of the paused resident passage found that `SourceAuthentication`
//! hashed `modeling_gemma4.py` and nothing else — every `Implementation.symbol` was an unchecked
//! `String`, configuration and shape testimony were accepted as written, the safetensors container
//! was not content-addressed in the receipt, and two intervention laws were typed as source
//! implementation symbols. A fabricated symbol on a valid file compiled. This owner is the repair,
//! and its rule is one sentence: **a binding is source-authenticated when every piece of testimony
//! it cites resolves against authenticated content, and a fabricated one refuses at compile.**
//!
//! # What an occurrence binds
//!
//! ```text
//!   implementation   locator · sha-256 · version · the text, for symbol and slice resolution
//!   configuration    locator · sha-256 · the text · the object every field is read under
//!   container        locator · size · header sha-256 · whole-content sha-256 · one RegionIdentity
//!                    per population the deed reads (offset, octets, dtype, shape, region sha-256
//!                    where the region was hashed as it was read)
//!   assets           processor / tokenizer / template files, each declared USED or UNUSED by this
//!                    aperture, with its digest
//! ```
//!
//! # The symbol grammar, and why a symbol is not a name
//!
//! `SourceTestimony::Implementation { locator, symbol }` is admitted only when `symbol` parses as
//!
//! ```text
//!   symbol := path [ " (" slice ")" ]        path := segment { "." segment }
//! ```
//!
//! and **resolves**: every segment is a `class`, `def`, attribute (`self.seg`), assignment
//! (`seg =`), or call/subscript (`seg(`, `seg[`) occurring in the authenticated text — a segment
//! after the first inside the scope the previous one opens — and the slice, when present, occurs
//! **verbatim** in that scope. The slice is the relation by which the testimony entails the bound
//! operation: it is the source line that IS the operation, and it is checked, not quoted.
//!
//! # Interventions are not source law
//!
//! A matched sibling's withdrawal and a control's collapse are the caller's interventions. They
//! carry [`crate::ported_operation::SourceTestimony::Intervention`] and are admissible only on a
//! quotient-species binding; an intervention offered as testimony for a transport or construction
//! refuses. Nothing here reads a float: configuration values are compared as the exact JSON spans
//! `crate::exact_json` returns.

use std::collections::BTreeMap;
use std::io::Read;

use sha2::{Digest, Sha256};

use crate::exact_json;
use crate::ported_operation::{OperationSpecies, PortedOperationComplex, SourceTestimony};

/// Every way an occurrence refuses. Each names the material that refused; none is a count.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SourceRefusal {
    Unreadable { locator: String, reason: String },
    /// The content at the locator no longer hashes to what the occurrence declared.
    Drifted { locator: String, declared: String, measured: String },
    /// Testimony cites a locator this occurrence does not authenticate.
    LocatorForeign { operation: String, locator: String },
    SymbolMalformed { operation: String, symbol: String, why: &'static str },
    /// A path segment occurs nowhere in the scope the previous segment opened.
    SymbolUnresolved { operation: String, symbol: String, segment: String },
    /// The parenthesised slice does not occur verbatim in the symbol's scope.
    SliceAbsent { operation: String, symbol: String, slice: String },
    ConfigurationFieldAbsent { operation: String, field: String },
    ConfigurationValueDiffers { operation: String, field: String, declared: String, measured: String },
    /// A declared shape disagrees with the authenticated container header.
    ShapeDiffers { operation: String, population: String, declared: Vec<usize>, measured: Vec<usize> },
    /// The container header declares a dtype for the population other than the exact carrier the
    /// deed decodes — checked, not recorded.
    DtypeDiffers { operation: String, population: String, declared: String, measured: String },
    /// A binding names a stored population the container does not identify by region.
    PopulationNotIdentified { operation: String, population: String },
    /// An intervention offered as testimony for a source law, or a source law with none.
    InterventionOnSourceLaw { operation: String, species: OperationSpecies },
    /// An operation whose testimony is a description alone — a name — has no source behind it.
    TestimonyNotExterior { operation: String, testimony: Vec<String> },
    ContainerMalformed { locator: String, reason: String },
}

impl std::fmt::Display for SourceRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

fn hex(digest: &[u8]) -> String {
    digest.iter().map(|byte| format!("{byte:02x}")).collect()
}

/// A text file authenticated by content: read once, hashed, retained for resolution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuthenticatedText {
    pub locator: String,
    pub sha256: String,
    pub octets: u64,
    /// An exterior version string the caller read from the source's own metadata, if any.
    pub version: Option<String>,
    text: String,
    /// The text with every Python comment body and string-literal body replaced by spaces of the
    /// same length (newlines kept), so symbol and slice resolution reads CODE and never a comment
    /// or a docstring. Same length, same offsets, same line numbers as `text`.
    scrubbed: String,
    /// Whether the text was read from `locator` (and can be re-read to detect drift) or declared
    /// by content by a caller that already held it.
    read_from_locator: bool,
}

impl AuthenticatedText {
    /// Read and hash the file at `locator`. The one place this owner touches the filesystem for
    /// text, and it is an admission audit at the apparatus boundary.
    pub fn read(locator: &str, version: Option<&str>) -> Result<Self, SourceRefusal> {
        let bytes = std::fs::read(locator).map_err(|error| SourceRefusal::Unreadable {
            locator: locator.to_owned(),
            reason: error.to_string(),
        })?;
        let text = String::from_utf8(bytes.clone()).map_err(|error| SourceRefusal::Unreadable {
            locator: locator.to_owned(),
            reason: format!("not UTF-8: {error}"),
        })?;
        Ok(Self {
            locator: locator.to_owned(),
            sha256: hex(&Sha256::digest(&bytes)),
            octets: bytes.len() as u64,
            version: version.map(str::to_owned),
            scrubbed: scrub_python(&text),
            text,
            read_from_locator: true,
        })
    }

    /// The text this occurrence authenticated, for a caller that resolves against it.
    pub fn text(&self) -> &str {
        &self.text
    }
    /// The scrubbed text resolution reads — see [`scrub_python`].
    pub fn scrubbed(&self) -> &str {
        &self.scrubbed
    }

    /// Re-read the locator and compare: the content must still hash to what was declared. A text
    /// declared by content has no locator to re-read and verifies against itself.
    pub fn verify(&self) -> Result<(), SourceRefusal> {
        if !self.read_from_locator {
            let measured = hex(&Sha256::digest(self.text.as_bytes()));
            if measured != self.sha256 {
                return Err(SourceRefusal::Drifted { locator: self.locator.clone(), declared: self.sha256.clone(), measured });
            }
            return Ok(());
        }
        let now = Self::read(&self.locator, self.version.as_deref())?;
        if now.sha256 != self.sha256 {
            return Err(SourceRefusal::Drifted {
                locator: self.locator.clone(),
                declared: self.sha256.clone(),
                measured: now.sha256,
            });
        }
        Ok(())
    }

    /// Declare a text by content rather than reading it — for a caller that already holds the
    /// bytes, and for tests. The hash is taken here, never trusted from the caller.
    pub fn of_text(locator: &str, text: &str, version: Option<&str>) -> Self {
        Self {
            locator: locator.to_owned(),
            sha256: hex(&Sha256::digest(text.as_bytes())),
            octets: text.len() as u64,
            version: version.map(str::to_owned),
            scrubbed: scrub_python(text),
            text: text.to_owned(),
            read_from_locator: false,
        }
    }
}

/// One stored population's byte region in the container, with its content identity where the
/// region was hashed as it was read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegionIdentity {
    pub population: String,
    pub dtype: String,
    pub shape: Vec<usize>,
    /// Payload-relative octet span, exactly as the header declares it.
    pub start: u64,
    pub end: u64,
    /// The region's own SHA-256, when the mouth hashed the bytes it read; `None` for a table only
    /// rows of which were read at runtime — the whole-content digest still covers it.
    pub sha256: Option<String>,
}

/// The container, content-addressed: size, header, whole content, and every region the deed reads.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuthenticatedContainer {
    pub locator: String,
    pub octets: u64,
    pub header_octets: u64,
    pub header_sha256: String,
    /// The SHA-256 of the whole file, when the caller took it (16 GB is a decision the caller
    /// makes and records; `None` says it was not taken, never that it was).
    pub content_sha256: Option<String>,
    pub regions: BTreeMap<String, RegionIdentity>,
    /// The one file occurrence every read of this container must have been of: device, inode,
    /// size, modification and change instants, taken when the container was authenticated.
    /// `verify_still` re-reads it and refuses when it moved. `None` says it was not taken.
    pub identity: Option<crate::foreign_map::FileIdentity>,
}

impl AuthenticatedContainer {
    /// Re-read the file occurrence at the locator and refuse when it is not the one authenticated.
    pub fn verify_still(&self) -> Result<(), SourceRefusal> {
        let Some(declared) = &self.identity else { return Ok(()) };
        let now = crate::foreign_map::FileIdentity::at(&self.locator).map_err(|error| SourceRefusal::Unreadable { locator: self.locator.clone(), reason: error.to_string() })?;
        if now != *declared {
            return Err(SourceRefusal::Drifted { locator: self.locator.clone(), declared: format!("{declared:?}"), measured: format!("{now:?}") });
        }
        Ok(())
    }

    /// Hash the safetensors header (the eight-octet length and the JSON it declares).
    pub fn read_header(locator: &str) -> Result<(u64, u64, String), SourceRefusal> {
        let mut file = std::fs::File::open(locator).map_err(|error| SourceRefusal::Unreadable {
            locator: locator.to_owned(),
            reason: error.to_string(),
        })?;
        let octets = file
            .metadata()
            .map_err(|error| SourceRefusal::Unreadable { locator: locator.to_owned(), reason: error.to_string() })?
            .len();
        let mut length = [0u8; 8];
        file.read_exact(&mut length).map_err(|error| SourceRefusal::ContainerMalformed {
            locator: locator.to_owned(),
            reason: error.to_string(),
        })?;
        let header_octets = u64::from_le_bytes(length);
        let extent = usize::try_from(header_octets).map_err(|_| SourceRefusal::ContainerMalformed {
            locator: locator.to_owned(),
            reason: format!("a header of {header_octets} octets exceeds this machine"),
        })?;
        let mut header = vec![0u8; extent];
        file.read_exact(&mut header).map_err(|error| SourceRefusal::ContainerMalformed {
            locator: locator.to_owned(),
            reason: error.to_string(),
        })?;
        let mut hasher = Sha256::new();
        hasher.update(length);
        hasher.update(&header);
        Ok((octets, header_octets, hex(&hasher.finalize())))
    }

    /// The SHA-256 of the whole file, streamed. Expensive on a large container and said so by the
    /// caller that chooses to take it.
    pub fn digest_whole(locator: &str) -> Result<String, SourceRefusal> {
        let mut file = std::fs::File::open(locator).map_err(|error| SourceRefusal::Unreadable {
            locator: locator.to_owned(),
            reason: error.to_string(),
        })?;
        let mut hasher = Sha256::new();
        let mut buffer = vec![0u8; 1 << 22];
        loop {
            let read = file.read(&mut buffer).map_err(|error| SourceRefusal::Unreadable {
                locator: locator.to_owned(),
                reason: error.to_string(),
            })?;
            if read == 0 {
                break;
            }
            hasher.update(&buffer[..read]);
        }
        Ok(hex(&hasher.finalize()))
    }
}

/// A sibling asset of the source — processor, tokenizer, template — declared used or unused by
/// this aperture. Declared, never inferred from its presence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AssetDeclaration {
    pub role: String,
    pub locator: String,
    pub sha256: Option<String>,
    pub used: bool,
}

/// One resolved implementation symbol: the relation by which the testimony entails the operation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedSymbol {
    pub symbol: String,
    pub path: Vec<String>,
    /// The verbatim slice found in the symbol's scope, if the testimony carried one.
    pub slice: Option<String>,
    /// The line (1-based) at which the last path segment resolved.
    pub line: usize,
}

/// What one bound operation's testimony resolved to. Every entry was checked against content.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BindingValidation {
    pub operation: String,
    pub species: OperationSpecies,
    pub symbols: Vec<ResolvedSymbol>,
    pub fields: Vec<(String, String)>,
    pub shapes: Vec<(String, Vec<usize>)>,
    pub interventions: Vec<String>,
}

/// **The source occurrence.** Built by the caller at the apparatus boundary; consumed by the
/// passage's compile, which refuses on the first testimony that does not resolve.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceOccurrence {
    pub implementation: AuthenticatedText,
    pub configuration: AuthenticatedText,
    /// The object every configuration field is read under — `text_config` for a Gemma text tower.
    pub configuration_scope: Vec<String>,
    pub container: AuthenticatedContainer,
    pub assets: Vec<AssetDeclaration>,
}

/// **Scrub Python for resolution**: every `#` comment body and every string-literal body — single-
/// or triple-quoted, with `r`/`b`/`f`/`u` prefixes in any case — is replaced by spaces of the same
/// length, newlines kept, so offsets and line numbers are unchanged and a symbol or slice can only
/// resolve against code. A slice that occurs only inside a docstring or a comment therefore does
/// not resolve, which is what "a valid but unrelated slice must not authenticate" requires of the
/// resolver. Escapes inside strings are honoured; an unterminated string scrubs to the end of
/// the text, which refuses rather than admits.
pub fn scrub_python(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out: Vec<u8> = bytes.to_vec();
    let mut i = 0usize;
    let n = bytes.len();
    let blank = |out: &mut Vec<u8>, from: usize, to: usize| {
        for k in from..to.min(out.len()) {
            if out[k] != b'\n' {
                out[k] = b' ';
            }
        }
    };
    while i < n {
        let c = bytes[i];
        if c == b'#' {
            let mut j = i;
            while j < n && bytes[j] != b'\n' {
                j += 1;
            }
            blank(&mut out, i + 1, j);
            i = j;
            continue;
        }
        if c == b'\'' || c == b'"' {
            // a string literal; its prefix letters (r, b, f, u) precede the quote and are left as code
            let triple = i + 2 < n && bytes[i + 1] == c && bytes[i + 2] == c;
            let quote_len = if triple { 3 } else { 1 };
            let mut j = i + quote_len;
            let mut closed = false;
            while j < n {
                if bytes[j] == b'\\' {
                    j += 2;
                    continue;
                }
                if triple {
                    if j + 2 < n && bytes[j] == c && bytes[j + 1] == c && bytes[j + 2] == c {
                        closed = true;
                        break;
                    }
                } else if bytes[j] == c {
                    closed = true;
                    break;
                } else if bytes[j] == b'\n' {
                    // a single-quoted string does not cross a line; treat as closed at the newline
                    break;
                }
                j += 1;
            }
            blank(&mut out, i + quote_len, j.min(n));
            i = if closed { j + quote_len } else { j };
            continue;
        }
        i += 1;
    }
    // every byte we touched was ASCII, so the result is valid UTF-8
    String::from_utf8(out).unwrap_or_else(|_| text.to_owned())
}

/// One segment resolves at a position, or nowhere. The forms a segment may take in the text.
fn segment_position(scope: &str, segment: &str) -> Option<usize> {
    let forms = [
        format!("class {segment}"),
        format!("def {segment}"),
        format!("self.{segment}"),
        format!("{segment} ="),
        format!("{segment}("),
        format!("{segment}["),
    ];
    let identifier_octet = |octet: u8| octet.is_ascii_alphanumeric() || octet == b'_';
    let mut best: Option<usize> = None;
    for form in forms {
        let ends_in_identifier = form.as_bytes().last().is_some_and(|octet| identifier_octet(*octet));
        let mut from = 0usize;
        while let Some(found) = scope[from..].find(&form) {
            let at = from + found;
            // A whole identifier: the octet before must not continue one, and where the form itself
            // ends in an identifier the octet after must not either — `class Norm` may not resolve
            // at `class NormOutput`.
            let before = at == 0 || !identifier_octet(scope.as_bytes()[at - 1]);
            let after = !ends_in_identifier || scope.as_bytes().get(at + form.len()).is_none_or(|octet| !identifier_octet(*octet));
            if before && after && best.is_none_or(|b| at < b) {
                best = Some(at);
                break;
            }
            from = at + form.len();
        }
    }
    best
}

/// The scope a `class`/`def` opens: from its position to the next line at column zero that begins
/// a declaration or decorator, or the end of the text.
fn scope_after(text: &str, at: usize) -> &str {
    let rest = &text[at..];
    let mut end = rest.len();
    let mut offset = 0usize;
    for (index, line) in rest.split_inclusive('\n').enumerate() {
        if index > 0 && (line.starts_with("class ") || line.starts_with("def ") || line.starts_with('@')) {
            end = offset;
            break;
        }
        offset += line.len();
    }
    &rest[..end]
}

fn line_of(text: &str, at: usize) -> usize {
    text[..at].matches('\n').count() + 1
}

impl SourceOccurrence {
    /// Every population the occurrence identifies by region, for a caller that mounts them.
    pub fn identifies(&self, population: &str) -> bool {
        self.container.regions.contains_key(population)
    }

    /// Resolve one implementation symbol against the authenticated implementation text.
    pub fn resolve_symbol(&self, operation: &str, symbol: &str) -> Result<ResolvedSymbol, SourceRefusal> {
        let (path_text, slice) = match symbol.find(" (") {
            Some(open) => {
                let close = symbol.rfind(')').ok_or(SourceRefusal::SymbolMalformed {
                    operation: operation.to_owned(),
                    symbol: symbol.to_owned(),
                    why: "an opening ' (' with no closing ')'",
                })?;
                if close <= open + 2 {
                    return Err(SourceRefusal::SymbolMalformed {
                        operation: operation.to_owned(),
                        symbol: symbol.to_owned(),
                        why: "an empty slice",
                    });
                }
                (&symbol[..open], Some(&symbol[open + 2..close]))
            }
            None => (symbol, None),
        };
        if path_text.is_empty() {
            return Err(SourceRefusal::SymbolMalformed {
                operation: operation.to_owned(),
                symbol: symbol.to_owned(),
                why: "an empty path",
            });
        }
        let path: Vec<String> = path_text.split('.').map(str::to_owned).collect();
        for segment in &path {
            let lawful = !segment.is_empty()
                && segment.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
                && !segment.chars().next().is_some_and(|c| c.is_ascii_digit());
            if !lawful {
                return Err(SourceRefusal::SymbolMalformed {
                    operation: operation.to_owned(),
                    symbol: symbol.to_owned(),
                    why: "a path segment that is not an identifier",
                });
            }
        }
        // Resolution reads the SCRUBBED text: comments and string bodies are blank, so a segment
        // or a slice that occurs only in a docstring or a comment does not resolve.
        let text = self.implementation.scrubbed();
        let mut scope: &str = text;
        let mut scope_offset = 0usize;
        let mut line = 0usize;
        for (index, segment) in path.iter().enumerate() {
            let Some(at) = segment_position(scope, segment) else {
                return Err(SourceRefusal::SymbolUnresolved {
                    operation: operation.to_owned(),
                    symbol: symbol.to_owned(),
                    segment: segment.clone(),
                });
            };
            line = line_of(text, scope_offset + at);
            if index + 1 < path.len() {
                // The next segment resolves inside the scope this one opens.
                let opened = scope_after(scope, at);
                scope_offset += at;
                scope = opened;
            } else if slice.is_some() {
                let opened = scope_after(scope, at);
                scope_offset += at;
                scope = opened;
            }
        }
        if let Some(slice) = slice {
            // The slice must occur in the scope as CODE: its own string bodies are blanked the way
            // the text's are, the blanked slice must occur in the blanked scope, and at that very
            // position the raw text must carry the slice verbatim — so a slice is matched by its
            // code structure AND its literal contents, never inside a comment or a docstring.
            let scrubbed_slice = scrub_python(slice);
            let raw_scope = &self.implementation.text()[scope_offset..scope_offset + scope.len()];
            let mut found = false;
            let mut from = 0usize;
            while let Some(hit) = scope[from..].find(&scrubbed_slice) {
                let at = from + hit;
                if raw_scope.get(at..at + slice.len()) == Some(slice) {
                    found = true;
                    break;
                }
                from = at + 1;
            }
            if !found {
                return Err(SourceRefusal::SliceAbsent {
                    operation: operation.to_owned(),
                    symbol: symbol.to_owned(),
                    slice: slice.to_owned(),
                });
            }
        }
        Ok(ResolvedSymbol {
            symbol: symbol.to_owned(),
            path,
            slice: slice.map(str::to_owned),
            line,
        })
    }

    /// The exact JSON span of a configuration field under the declared scope. Field grammar:
    /// `a.b.c`, with `[i]` for an array element.
    pub fn configuration_span(&self, field: &str) -> Option<String> {
        let mut span: &str = self.configuration.text();
        for key in &self.configuration_scope {
            span = exact_json::field(span, key)?;
        }
        for part in field.split('.') {
            let (name, index) = match part.find('[') {
                Some(open) => {
                    let close = part.rfind(']')?;
                    (&part[..open], Some(part[open + 1..close].parse::<usize>().ok()?))
                }
                None => (part, None),
            };
            if !name.is_empty() {
                span = exact_json::field(span, name)?;
            }
            if let Some(index) = index {
                let elements = exact_json::array_elements(span).ok()?;
                span = elements.get(index)?;
            }
        }
        Some(span.trim().to_owned())
    }

    /// Verify one configuration testimony: the declared value must equal the exact span, or the
    /// string it quotes.
    pub fn verify_field(&self, operation: &str, field: &str, value: &str) -> Result<(String, String), SourceRefusal> {
        let span = self.configuration_span(field).ok_or_else(|| SourceRefusal::ConfigurationFieldAbsent {
            operation: operation.to_owned(),
            field: field.to_owned(),
        })?;
        let measured = exact_json::as_string(&span).unwrap_or_else(|| span.clone());
        if measured != value {
            return Err(SourceRefusal::ConfigurationValueDiffers {
                operation: operation.to_owned(),
                field: field.to_owned(),
                declared: value.to_owned(),
                measured,
            });
        }
        Ok((field.to_owned(), measured))
    }

    /// **Validate every bound operation's testimony against this occurrence.** Refuses on the
    /// first testimony that does not resolve; returns what each binding resolved to.
    pub fn validate(&self, complex: &PortedOperationComplex) -> Result<Vec<BindingValidation>, SourceRefusal> {
        self.implementation.verify()?;
        self.configuration.verify()?;
        let mut validated = Vec::with_capacity(complex.operations.len());
        for operation in complex.operations.values() {
            let name = complex
                .shape
                .laws
                .get(&operation.law)
                .map(|law| law.name.clone())
                .unwrap_or_default();
            let mut validation = BindingValidation {
                operation: name.clone(),
                species: operation.species,
                symbols: Vec::new(),
                fields: Vec::new(),
                shapes: Vec::new(),
                interventions: Vec::new(),
            };
            let mut exterior = false;
            for testimony in &operation.testimony {
                match testimony {
                    SourceTestimony::Implementation { locator, symbol } => {
                        if *locator != self.implementation.locator {
                            return Err(SourceRefusal::LocatorForeign { operation: name, locator: locator.clone() });
                        }
                        validation.symbols.push(self.resolve_symbol(&name, symbol)?);
                        exterior = true;
                    }
                    SourceTestimony::Configuration { field, value } => {
                        validation.fields.push(self.verify_field(&name, field, value)?);
                        exterior = true;
                    }
                    SourceTestimony::DeclaredShape { population, shape } => {
                        let region = self.container.regions.get(population).ok_or_else(|| {
                            SourceRefusal::PopulationNotIdentified { operation: name.clone(), population: population.clone() }
                        })?;
                        if region.shape != *shape {
                            return Err(SourceRefusal::ShapeDiffers {
                                operation: name,
                                population: population.clone(),
                                declared: shape.clone(),
                                measured: region.shape.clone(),
                            });
                        }
                        if region.dtype != "Bf16" && region.dtype != "BF16" {
                            return Err(SourceRefusal::DtypeDiffers { operation: name.clone(), population: population.clone(), declared: "BF16".to_owned(), measured: region.dtype.clone() });
                        }
                        validation.shapes.push((population.clone(), shape.clone()));
                        exterior = true;
                    }
                    SourceTestimony::Intervention { statement } => {
                        validation.interventions.push(statement.clone());
                    }
                    SourceTestimony::AuthoritativeDescription { .. } | SourceTestimony::Undecided { .. } => {}
                }
            }
            // An intervention is the caller's, never source law: an operation carrying both an
            // intervention and exterior testimony (implementation, configuration, shape) is refused
            // — a quotient may carry interventions freely (it removes), and a transport or
            // construction may be an intervention occurrence only when it carries NOTHING else, so a
            // rebase, a permutation or a replacement sibling is admitted as wholly the caller's.
            if !validation.interventions.is_empty() && exterior && operation.species != OperationSpecies::Quotient {
                return Err(SourceRefusal::InterventionOnSourceLaw { operation: name, species: operation.species });
            }
            if !exterior && validation.interventions.is_empty() {
                return Err(SourceRefusal::TestimonyNotExterior {
                    operation: name,
                    testimony: operation.testimony.iter().map(|t| format!("{t:?}")).collect(),
                });
            }
            if let Some(carrier) = &operation.carrier {
                if !self.identifies(carrier) {
                    return Err(SourceRefusal::PopulationNotIdentified { operation: name, population: carrier.clone() });
                }
            }
            validated.push(validation);
        }
        Ok(validated)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::category::BoundaryId;

    const IMPLEMENTATION: &str = "\
class Norm(nn.Module):
    def __init__(self, dim, eps=1e-6, with_scale=True):
        self.eps = eps

    def forward(self, hidden_states):
        normed_output = self._norm(hidden_states.float())
        if self.with_scale:
            normed_output = normed_output * self.weight.float()
        return normed_output


def rotate_half(x):
    return torch.cat((-x2, x1), dim=-1)


class Attention(nn.Module):
    def __init__(self, config):
        self.scaling = 1.0
";
    const CONFIGURATION: &str = r#"{"text_config": {"rms_norm_eps": 1e-06, "hidden_size": 2560, "layer_types": ["sliding_attention", "full_attention"], "rope_parameters": {"sliding_attention": {"rope_theta": 10000.0, "rope_type": "default"}}}}"#;

    fn occurrence() -> SourceOccurrence {
        let mut regions = BTreeMap::new();
        regions.insert(
            "w".to_owned(),
            RegionIdentity { population: "w".to_owned(), dtype: "BF16".to_owned(), shape: vec![4, 2], start: 0, end: 16, sha256: Some("00".repeat(32)) },
        );
        SourceOccurrence {
            implementation: AuthenticatedText::of_text("/impl.py", IMPLEMENTATION, Some("test")),
            configuration: AuthenticatedText::of_text("/config.json", CONFIGURATION, None),
            configuration_scope: vec!["text_config".to_owned()],
            container: AuthenticatedContainer {
                locator: "/model.safetensors".to_owned(),
                octets: 16,
                header_octets: 0,
                header_sha256: String::new(),
                content_sha256: None,
                regions,
                identity: None,
            },
            assets: Vec::new(),
        }
    }

    #[test]
    fn resolution_reads_code_and_not_a_comment_or_a_docstring() {
        let scrubbed = scrub_python("x = 1  # self.fake = 2\ns = \"self.other(\"\nt = '''doc self.third( more\nlines'''\ny = self.real(\n");
        assert!(scrubbed.contains("x = 1  #"));
        assert!(!scrubbed.contains("self.fake"));
        assert!(!scrubbed.contains("self.other"));
        assert!(!scrubbed.contains("self.third"));
        assert!(scrubbed.contains("self.real("));
        assert_eq!(scrubbed.matches('\n').count(), 5, "newlines are kept so line numbers hold");
        // a symbol whose only occurrence is in a comment does not resolve
        let text = "class Site:\n    def enter(self):\n        # self.phantom = words\n        x = words * scale\n        doc = \"\"\"phantom = x\"\"\"\n";
        let occurrence = SourceOccurrence {
            implementation: AuthenticatedText::of_text("/site.py", text, None),
            configuration: AuthenticatedText::of_text("/config.json", "{}", None),
            configuration_scope: Vec::new(),
            container: AuthenticatedContainer { locator: "/none".to_owned(), octets: 0, header_octets: 0, header_sha256: String::new(), content_sha256: None, regions: BTreeMap::new(), identity: None },
            assets: Vec::new(),
        };
        assert!(matches!(occurrence.resolve_symbol("op", "Site.enter.phantom"), Err(SourceRefusal::SymbolUnresolved { .. })));
        assert!(matches!(occurrence.resolve_symbol("op", "Site.enter (phantom = x)"), Err(SourceRefusal::SliceAbsent { .. })));
        assert!(occurrence.resolve_symbol("op", "Site.enter (x = words * scale)").is_ok());
    }

    #[test]
    fn a_symbol_resolves_in_scope_and_a_slice_must_be_verbatim() {
        let occurrence = occurrence();
        let resolved = occurrence.resolve_symbol("op", "Norm.forward (normed_output * self.weight.float())").expect("resolves");
        assert_eq!(resolved.path, vec!["Norm", "forward"]);
        assert_eq!(resolved.line, 5);
        assert!(occurrence.resolve_symbol("op", "rotate_half (torch.cat((-x2, x1), dim=-1))").is_ok());
        assert!(occurrence.resolve_symbol("op", "Attention.__init__ (self.scaling = 1.0)").is_ok());
        // A fabricated segment refuses by name.
        assert!(matches!(
            occurrence.resolve_symbol("op", "Norm.backward"),
            Err(SourceRefusal::SymbolUnresolved { segment, .. }) if segment == "backward"
        ));
        // A slice that is not in the scope refuses, even if it is elsewhere in the file.
        assert!(matches!(
            occurrence.resolve_symbol("op", "Norm.forward (self.scaling = 1.0)"),
            Err(SourceRefusal::SliceAbsent { .. })
        ));
        // A segment outside the class scope does not resolve through it.
        assert!(matches!(occurrence.resolve_symbol("op", "Norm.rotate_half"), Err(SourceRefusal::SymbolUnresolved { .. })));
        // A class whose name is a prefix of another's resolves at its own declaration, not the other's.
        let prefixed = SourceOccurrence {
            implementation: AuthenticatedText::of_text("/impl.py", "class NormOutput:\n    def other(self):\n        pass\n\nclass Norm:\n    def forward(self):\n        return x\n", None),
            ..occurrence.clone()
        };
        assert_eq!(prefixed.resolve_symbol("op", "Norm.forward (return x)").expect("resolves").line, 6);
        assert!(matches!(occurrence.resolve_symbol("op", "Norm.forward ()"), Err(SourceRefusal::SymbolMalformed { .. })));
        assert!(matches!(occurrence.resolve_symbol("op", "1Norm"), Err(SourceRefusal::SymbolMalformed { .. })));
    }

    #[test]
    fn a_configuration_field_is_the_exact_span_and_a_drifted_value_refuses() {
        let occurrence = occurrence();
        assert_eq!(occurrence.verify_field("op", "rms_norm_eps", "1e-06").expect("field").1, "1e-06");
        assert_eq!(occurrence.verify_field("op", "hidden_size", "2560").expect("field").1, "2560");
        assert_eq!(occurrence.verify_field("op", "layer_types[0]", "sliding_attention").expect("field").1, "sliding_attention");
        assert_eq!(occurrence.verify_field("op", "rope_parameters.sliding_attention.rope_theta", "10000.0").expect("field").1, "10000.0");
        assert_eq!(occurrence.verify_field("op", "rope_parameters.sliding_attention.rope_type", "default").expect("field").1, "default");
        assert!(matches!(occurrence.verify_field("op", "rms_norm_eps", "1e-05"), Err(SourceRefusal::ConfigurationValueDiffers { .. })));
        assert!(matches!(occurrence.verify_field("op", "no_such_field", "1"), Err(SourceRefusal::ConfigurationFieldAbsent { .. })));
        assert!(matches!(occurrence.verify_field("op", "layer_types[7]", "x"), Err(SourceRefusal::ConfigurationFieldAbsent { .. })));
    }

    fn complex_with(testimony: Vec<SourceTestimony>, species: OperationSpecies, carrier: Option<String>) -> PortedOperationComplex {
        let mut complex = PortedOperationComplex::new("test");
        let port: BoundaryId = complex.port("p");
        let inputs = if species == OperationSpecies::Construction { vec![] } else { vec![port] };
        let law = complex.bind_operation("op", species, inputs, vec![port], carrier, testimony).expect("law");
        complex.occur(law).expect("occur");
        complex
    }

    #[test]
    fn validation_refuses_a_fabricated_symbol_a_wrong_shape_a_foreign_locator_and_an_intervention_on_a_law() {
        let occurrence = occurrence();
        let good = complex_with(
            vec![
                SourceTestimony::Implementation { locator: "/impl.py".to_owned(), symbol: "Norm.forward".to_owned() },
                SourceTestimony::DeclaredShape { population: "w".to_owned(), shape: vec![4, 2] },
            ],
            OperationSpecies::Transport,
            Some("w".to_owned()),
        );
        let validated = occurrence.validate(&good).expect("validates");
        assert_eq!(validated.len(), 1);
        assert_eq!(validated[0].symbols[0].path, vec!["Norm", "forward"]);
        let fabricated = complex_with(
            vec![SourceTestimony::Implementation { locator: "/impl.py".to_owned(), symbol: "Norm.forwardz".to_owned() }],
            OperationSpecies::Transport,
            None,
        );
        assert!(matches!(occurrence.validate(&fabricated), Err(SourceRefusal::SymbolUnresolved { .. })));
        let wrong_shape = complex_with(
            vec![SourceTestimony::DeclaredShape { population: "w".to_owned(), shape: vec![4, 3] }],
            OperationSpecies::Transport,
            None,
        );
        assert!(matches!(occurrence.validate(&wrong_shape), Err(SourceRefusal::ShapeDiffers { .. })));
        let foreign = complex_with(
            vec![SourceTestimony::Implementation { locator: "/other.py".to_owned(), symbol: "Norm.forward".to_owned() }],
            OperationSpecies::Transport,
            None,
        );
        assert!(matches!(occurrence.validate(&foreign), Err(SourceRefusal::LocatorForeign { .. })));
        let intervention_on_law = complex_with(
            vec![SourceTestimony::Intervention { statement: "withdraw".to_owned() }, SourceTestimony::Implementation { locator: "/impl.py".to_owned(), symbol: "Norm.forward".to_owned() }],
            OperationSpecies::Transport,
            None,
        );
        assert!(matches!(occurrence.validate(&intervention_on_law), Err(SourceRefusal::InterventionOnSourceLaw { .. })), "an intervention offered beside source law on a transport refuses");
        let intervention_only = complex_with(vec![SourceTestimony::Intervention { statement: "rebase by two".to_owned() }], OperationSpecies::Transport, None);
        assert!(occurrence.validate(&intervention_only).is_ok(), "a transport that is wholly the caller's intervention is admitted as one");
        let intervention_on_quotient = complex_with(
            vec![SourceTestimony::Intervention { statement: "withdraw".to_owned() }],
            OperationSpecies::Quotient,
            None,
        );
        assert_eq!(occurrence.validate(&intervention_on_quotient).expect("lawful").len(), 1);
        let described = complex_with(
            vec![SourceTestimony::AuthoritativeDescription { statement: "enter".to_owned() }],
            OperationSpecies::Construction,
            None,
        );
        assert!(matches!(occurrence.validate(&described), Err(SourceRefusal::TestimonyNotExterior { .. })));
        let unidentified_carrier = complex_with(
            vec![SourceTestimony::Implementation { locator: "/impl.py".to_owned(), symbol: "Norm.forward".to_owned() }],
            OperationSpecies::Transport,
            Some("q".to_owned()),
        );
        assert!(matches!(occurrence.validate(&unidentified_carrier), Err(SourceRefusal::PopulationNotIdentified { .. })));
    }

    #[test]
    fn a_text_read_from_disk_verifies_by_content_and_a_drift_refuses() {
        let path = std::env::temp_dir().join(format!("source_occurrence_{}.py", std::process::id()));
        std::fs::write(&path, IMPLEMENTATION).expect("write");
        let text = AuthenticatedText::read(path.to_str().expect("utf-8 path"), None).expect("read");
        assert_eq!(text.octets, IMPLEMENTATION.len() as u64);
        text.verify().expect("verifies");
        std::fs::write(&path, "drifted").expect("write");
        assert!(matches!(text.verify(), Err(SourceRefusal::Drifted { .. })));
        let _ = std::fs::remove_file(&path);
    }
}
