//! A small, source-detached cultivated product over one immutable native rest.
//!
//! This owner is deliberately a product boundary, not a trainer or a runtime. The implementation
//! is routed into small owner-local modules: schema/payload, native morphology, directory, wire,
//! and focused tests.

use sha2::{Digest, Sha256};

const PREFIX: &[u8] = b"HOLONIC-CULTIVATED-REST\0\x01";
const DIGEST_OCTETS: usize = 32;
const SCHEMA: &str = "holonic-engine.phoenix.cultivated-rest.v1";
const DIRECTORY_SCHEMA: &str = "holonic-engine.phoenix.cultivated-rest-directory.v1";

fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}
fn digest_bytes(bytes: &[u8]) -> [u8; DIGEST_OCTETS] {
    Sha256::digest(bytes).into()
}
fn valid_digest(value: &str) -> bool {
    value.len() == 64 && value.as_bytes().iter().all(u8::is_ascii_hexdigit)
}
fn append_text(bytes: &mut Vec<u8>, text: &str) {
    bytes.extend_from_slice(&(text.len() as u64).to_le_bytes());
    bytes.extend_from_slice(text.as_bytes());
}
fn canonical_laws_digest(laws: &[schema::TypedLaw]) -> String {
    let mut bytes = Vec::new();
    for law in laws {
        append_text(&mut bytes, &law.name);
        append_text(&mut bytes, &law.constitutive_digest);
        bytes.extend_from_slice(&(law.inputs.len() as u64).to_le_bytes());
        for port in &law.inputs {
            append_text(&mut bytes, port);
        }
        bytes.extend_from_slice(&(law.outputs.len() as u64).to_le_bytes());
        for port in &law.outputs {
            append_text(&mut bytes, port);
        }
        bytes.extend_from_slice(&(law.extent_agreements.len() as u64).to_le_bytes());
        for agreement in &law.extent_agreements {
            bytes.push(agreement.axis_tag());
            let (left, right) = agreement.endpoints();
            append_text(&mut bytes, left);
            append_text(&mut bytes, right);
        }
    }
    digest(&bytes)
}
fn factor_values_bytes(values: &[i64]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(values.len() * 8);
    for value in values {
        bytes.extend_from_slice(&value.to_le_bytes());
    }
    bytes
}
mod directory;
mod native_morphology;
mod schema;
#[cfg(test)]
mod tests;
mod wire;

pub use directory::{DirectoryCompanion, MountedCultivatedRest};
pub use native_morphology::{
    NativeMorphologyInput, NativeMorphologyWitness, native_morphology_bytes,
    write_native_morphology,
};
pub use schema::{
    AlignedFactor, CodebookGraphIdentity, CultivatedRestInput, CultivatedRestRefusal,
    DerivationAdjointRankReceipt, ExactCertificate, ExtentOrigin, MorphologyPayload,
    OctaveBoundOrigin, PortDirection, PortExtentAgreement, PredecessorProductIdentity,
    ReconstructionCandidate, ReconstructionFibre, SparseDelta, SparseDeltaEntry, TargetedAblation,
    TypedLaw, TypedPort,
};
pub use wire::CultivatedRest;
