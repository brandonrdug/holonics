//! Native terminal potential compiled through an anatomical quotient.
//!
//! An exterior dismantling passage may construct this rest, but neither the rest nor its resident
//! conduct contains source occurrences, source nodes, ancestry testimony, or a callable exterior
//! edge. Situated history addresses are native lineage. The hot law carries exact native incidence
//! on the card and returns the declared terminal receiver together with its open successor fibre.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::{
    cuda_refine::{
        CudaRefineExecutor, ResidentIntervalPotentialReceiver, ResidentIntervalPotentialReturn,
    },
    receiver_history_compression::NativeStateId,
};

const SCHEMA: &str = "holonic-engine.native-anatomical-potential-rest.v2";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativePotentialClassCertificate {
    pub native: NativeStateId,
    pub history_addresses: Vec<String>,
    pub selected_native_address: u32,
}

/// The hot terminal receiver after an exterior realization has factored through native anatomy.
/// Exterior reconstruction testimony remains physically outside this owner.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAnatomicalPotentialRest {
    pub schema: String,
    pub native_population: Vec<NativeStateId>,
    pub receiver_rows: Vec<u32>,
    pub lower_incidence: Vec<i64>,
    pub upper_incidence: Vec<i64>,
    pub decoder: BTreeMap<u32, String>,
    pub class_certificates: Vec<NativePotentialClassCertificate>,
    pub open_exterior: Vec<String>,
    pub identity_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "status", rename_all = "kebab-case")]
pub enum NativeAddressedPotentialSuccessor {
    Admitted {
        predecessor_history_address: String,
        emitted_native_address: u32,
        emitted_surface: String,
        successor_history_address: String,
        native_history_state: NativeStateId,
    },
    Open(NativePotentialSectionObstruction),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativePotentialSectionObstruction {
    pub predecessor_history_address: String,
    pub emitted_native_address: u32,
    pub emitted_surface: String,
    pub requested_history_address: String,
    pub admitted_history_addresses: Vec<String>,
    pub source_fallback_permitted: bool,
}

#[derive(Debug, Error)]
pub enum NativeAnatomicalPotentialRefusal {
    #[error("the native anatomical potential has malformed or inconsistent incidence")]
    Shape,
    #[error("the native anatomical potential identity does not reconstruct")]
    Identity,
    #[error("native anatomical potential wire refused: {0}")]
    Wire(String),
    #[error("resident native anatomical potential apparatus refused: {0}")]
    Apparatus(String),
}

impl NativeAnatomicalPotentialRest {
    pub fn seal(
        native_population: Vec<NativeStateId>,
        receiver_rows: Vec<u32>,
        lower_incidence: Vec<i64>,
        upper_incidence: Vec<i64>,
        decoder: BTreeMap<u32, String>,
        class_certificates: Vec<NativePotentialClassCertificate>,
        open_exterior: Vec<String>,
    ) -> Result<Self, NativeAnatomicalPotentialRefusal> {
        let mut rest = Self {
            schema: SCHEMA.to_owned(),
            native_population,
            receiver_rows,
            lower_incidence,
            upper_incidence,
            decoder,
            class_certificates,
            open_exterior,
            identity_sha256: String::new(),
        };
        rest.validate_shape()?;
        rest.identity_sha256 = hex(&Sha256::digest(rest.identity_body()?));
        Ok(rest)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, NativeAnatomicalPotentialRefusal> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| NativeAnatomicalPotentialRefusal::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, NativeAnatomicalPotentialRefusal> {
        self.validate()?;
        serde_json::to_vec(self)
            .map_err(|error| NativeAnatomicalPotentialRefusal::Wire(error.to_string()))
    }

    pub fn validate(&self) -> Result<(), NativeAnatomicalPotentialRefusal> {
        self.validate_shape()?;
        if self.identity_sha256 != hex(&Sha256::digest(self.identity_body()?)) {
            return Err(NativeAnatomicalPotentialRefusal::Identity);
        }
        Ok(())
    }

    pub fn one_hot_for_native(
        &self,
        native: NativeStateId,
    ) -> Result<Vec<Rat>, NativeAnatomicalPotentialRefusal> {
        let Some(at) = self
            .native_population
            .iter()
            .position(|candidate| *candidate == native)
        else {
            return Err(NativeAnatomicalPotentialRefusal::Shape);
        };
        Ok((0..self.native_population.len())
            .map(|candidate| Rat::from_integer(BigInt::from((candidate == at) as u8)))
            .collect())
    }

    pub fn decode(&self, native: u32) -> Result<&str, NativeAnatomicalPotentialRefusal> {
        self.decoder
            .get(&native)
            .map(String::as_str)
            .ok_or(NativeAnatomicalPotentialRefusal::Shape)
    }

    pub fn native_for_history(
        &self,
        history_address: &str,
    ) -> Result<NativeStateId, NativeAnatomicalPotentialRefusal> {
        self.class_certificates
            .iter()
            .find(|certificate| {
                certificate
                    .history_addresses
                    .iter()
                    .any(|address| address == history_address)
            })
            .map(|certificate| certificate.native)
            .ok_or(NativeAnatomicalPotentialRefusal::Shape)
    }

    pub fn addressed_successor(
        &self,
        predecessor_history_address: &str,
        emitted_native_address: u32,
    ) -> Result<NativeAddressedPotentialSuccessor, NativeAnatomicalPotentialRefusal> {
        let _ = self.native_for_history(predecessor_history_address)?;
        let emitted_surface = self.decode(emitted_native_address)?.to_owned();
        let successor_history_address =
            format!("{predecessor_history_address}/emission/{emitted_native_address}");
        match self.native_for_history(&successor_history_address) {
            Ok(native_history_state) => Ok(NativeAddressedPotentialSuccessor::Admitted {
                predecessor_history_address: predecessor_history_address.to_owned(),
                emitted_native_address,
                emitted_surface,
                successor_history_address,
                native_history_state,
            }),
            Err(NativeAnatomicalPotentialRefusal::Shape) => Ok(
                NativeAddressedPotentialSuccessor::Open(NativePotentialSectionObstruction {
                    predecessor_history_address: predecessor_history_address.to_owned(),
                    emitted_native_address,
                    emitted_surface,
                    requested_history_address: successor_history_address,
                    admitted_history_addresses: self
                        .class_certificates
                        .iter()
                        .flat_map(|certificate| certificate.history_addresses.iter().cloned())
                        .collect(),
                    source_fallback_permitted: false,
                }),
            ),
            Err(error) => Err(error),
        }
    }

    pub fn mount_receiver(
        &self,
    ) -> Result<ResidentNativeAnatomicalPotentialReceiver, NativeAnatomicalPotentialRefusal> {
        let card = CudaRefineExecutor::new()
            .map_err(|error| NativeAnatomicalPotentialRefusal::Apparatus(error.to_string()))?;
        self.mount_receiver_on(card)
    }

    pub fn mount_receiver_on(
        &self,
        card: CudaRefineExecutor,
    ) -> Result<ResidentNativeAnatomicalPotentialReceiver, NativeAnatomicalPotentialRefusal> {
        self.validate()?;
        let resident = ResidentIntervalPotentialReceiver::mount(
            card,
            "native/anatomical-potential-receiver",
            self.receiver_rows.len(),
            self.native_population.len(),
            &self.receiver_rows,
            &self.lower_incidence,
            &self.upper_incidence,
        )
        .map_err(|error| NativeAnatomicalPotentialRefusal::Apparatus(error.to_string()))?;
        Ok(ResidentNativeAnatomicalPotentialReceiver { resident })
    }

    fn validate_shape(&self) -> Result<(), NativeAnatomicalPotentialRefusal> {
        let natives = self
            .native_population
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        let rows = self.receiver_rows.iter().copied().collect::<BTreeSet<_>>();
        let decoded_rows = self.decoder.keys().copied().collect::<BTreeSet<_>>();
        let expected = self
            .native_population
            .len()
            .checked_mul(self.receiver_rows.len());
        if self.schema != SCHEMA
            || natives.is_empty()
            || natives.len() != self.native_population.len()
            || rows.is_empty()
            || rows.len() != self.receiver_rows.len()
            || decoded_rows != rows
            || self.decoder.values().any(|surface| surface.is_empty())
            || expected != Some(self.lower_incidence.len())
            || expected != Some(self.upper_incidence.len())
            || self.class_certificates.len() != self.native_population.len()
            || self.open_exterior.iter().any(String::is_empty)
        {
            return Err(NativeAnatomicalPotentialRefusal::Shape);
        }
        let mut certified_natives = BTreeSet::new();
        let mut histories = BTreeSet::new();
        for certificate in &self.class_certificates {
            if !natives.contains(&certificate.native)
                || !certified_natives.insert(certificate.native)
                || certificate.history_addresses.is_empty()
                || certificate
                    .history_addresses
                    .iter()
                    .any(|address| address.is_empty() || !histories.insert(address))
                || !rows.contains(&certificate.selected_native_address)
            {
                return Err(NativeAnatomicalPotentialRefusal::Shape);
            }
        }
        if certified_natives != natives {
            return Err(NativeAnatomicalPotentialRefusal::Shape);
        }
        Ok(())
    }

    fn identity_body(&self) -> Result<Vec<u8>, NativeAnatomicalPotentialRefusal> {
        serde_json::to_vec(&(
            &self.schema,
            &self.native_population,
            &self.receiver_rows,
            &self.lower_incidence,
            &self.upper_incidence,
            &self.decoder,
            &self.class_certificates,
            &self.open_exterior,
        ))
        .map_err(|error| NativeAnatomicalPotentialRefusal::Wire(error.to_string()))
    }
}

pub struct ResidentNativeAnatomicalPotentialReceiver {
    resident: ResidentIntervalPotentialReceiver,
}

impl ResidentNativeAnatomicalPotentialReceiver {
    pub fn conduct(
        &mut self,
        fronts: &[Vec<Rat>],
    ) -> Result<ResidentIntervalPotentialReturn, NativeAnatomicalPotentialRefusal> {
        self.resident
            .conduct(fronts)
            .map_err(|error| NativeAnatomicalPotentialRefusal::Apparatus(error.to_string()))
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn addressed_successor_closes_only_where_the_native_history_exists() {
        let rest = NativeAnatomicalPotentialRest::seal(
            vec![NativeStateId(0), NativeStateId(1)],
            vec![7, 9],
            vec![2, 0, 0, 2],
            vec![3, 1, 1, 3],
            BTreeMap::from([(7, "A".to_owned()), (9, "B".to_owned())]),
            vec![
                NativePotentialClassCertificate {
                    native: NativeStateId(0),
                    history_addresses: vec!["root".to_owned()],
                    selected_native_address: 7,
                },
                NativePotentialClassCertificate {
                    native: NativeStateId(1),
                    history_addresses: vec!["root/emission/7".to_owned()],
                    selected_native_address: 9,
                },
            ],
            vec!["the next history is open".to_owned()],
        )
        .expect("native rest");
        assert!(matches!(
            rest.addressed_successor("root", 7).expect("successor"),
            NativeAddressedPotentialSuccessor::Admitted { .. }
        ));
        assert!(matches!(
            rest.addressed_successor("root/emission/7", 9)
                .expect("open"),
            NativeAddressedPotentialSuccessor::Open(_)
        ));
    }
}
