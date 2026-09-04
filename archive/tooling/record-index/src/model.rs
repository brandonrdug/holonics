use std::collections::BTreeMap;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct FormulaEntry {
    pub id: String,
    pub handle: String,
    pub title: String,
    pub marks: Vec<&'static str>,
    pub source: String,
    pub line: usize,
    pub sha256: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ResearchEntry {
    pub id: String,
    pub date: String,
    pub title: String,
    pub marks: Vec<&'static str>,
    pub source: String,
    pub sha256: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ObservationEntry {
    pub observation_id: String,
    pub evidence_id: String,
    pub campaign: String,
    pub record_kind: String,
    pub title: String,
    pub marks: Vec<&'static str>,
    pub source: String,
    pub sha256: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CorrespondenceEntry {
    pub id: String,
    pub date: String,
    pub from: String,
    pub to: String,
    pub title: String,
    pub marks: Vec<&'static str>,
    pub source: String,
    pub sha256: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LedgerEntry {
    pub date: String,
    pub title: String,
    pub marks: Vec<&'static str>,
    pub source: String,
    pub line: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CrateEntry {
    pub id: String,
    pub name: String,
    pub relationship: String,
    pub manifest: String,
    pub sha256: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PublicSymbol {
    pub crate_name: String,
    pub kind: String,
    pub name: String,
    pub source: String,
    pub line: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct AbiIdentifier {
    pub id: String,
    pub category: String,
    pub crate_name: String,
    pub name: String,
    pub declaration: String,
    pub source: String,
    pub line: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RegistryRecord {
    pub id: String,
    pub kind: String,
    pub alias: String,
    pub title: String,
    pub source: String,
    pub line: Option<usize>,
    pub marks: Vec<&'static str>,
    pub sha256: Option<String>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Inventory {
    pub formula: Vec<FormulaEntry>,
    pub research: Vec<ResearchEntry>,
    pub observations: Vec<ObservationEntry>,
    pub correspondence: Vec<CorrespondenceEntry>,
    pub ledger: Vec<LedgerEntry>,
    pub crates: Vec<CrateEntry>,
    pub public_symbols: Vec<PublicSymbol>,
    pub abi: Vec<AbiIdentifier>,
    pub registry: BTreeMap<String, RegistryRecord>,
    pub source_hashes: BTreeMap<String, String>,
}
