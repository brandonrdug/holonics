//! Source-detached rest of a foreign terminal potential complex on one cultivated reachable
//! section.
//!
//! The large inherited tower is absent.  The rest retains the exact predecessor potential fibre
//! on the addressed coefficient basis, the final hidden incidence needed by the sparse returned
//! factors, and the smallest row cover through which the declared terminal-order receiver was
//! proved to factor.  A broader receiver can reopen the cold potential fibre without reopening the
//! foreign model.  Hot continuation mounts only the sufficient cover and coefficient current.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::cuda_refine::{
    CudaRefineExecutor, ResidentIntervalPotentialReceiver, ResidentIntervalPotentialReturn,
};
use crate::native_anatomical_potential::{
    NativeAnatomicalPotentialRest, NativePotentialClassCertificate,
};

use super::{
    foreign_section_descent::CarrierSectionRest,
    receiver_restricted_transport::ExteriorNativeAnatomyWitness,
};
use crate::native_anatomy::NativeAnatomyRest;

const SCHEMA: &str = "holonic-engine.soulkiller.foreign-potential-complex-rest.v1";
const MAGIC: &[u8] = b"HOLONIC-FOREIGN-POTENTIAL-COMPLEX\x01";

/// One support-gated returned factor after composing its selector with the captured final hidden
/// incidence. The multiplier is an exact apparatus-chart integer at the common rested grain.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RestedPotentialFactor {
    pub address: String,
    pub parent_factor_addresses: Vec<String>,
    pub target_native_address: u32,
    pub selector_coordinate: usize,
    pub multiplier: i64,
    pub founding_native_history_states: Vec<u64>,
}

/// The complete exact order-receiver separator for one admitted coefficient node.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PotentialReceiverCertificate {
    pub history_address: String,
    pub native_history_state: u64,
    pub predecessor_selected_native_addresses: Vec<u32>,
    pub cultivated_selected_native_addresses: Vec<u32>,
    pub predecessor_top_lower: i64,
    pub cultivated_top_lower: i64,
    pub greatest_omitted_upper: i64,
    pub shortest_omitted_competitor: u32,
    pub admitted_factor_addresses: Vec<String>,
    pub complete_predecessor_potential_sha256: String,
}

#[derive(Debug, PartialEq, Eq)]
pub struct ForeignPotentialComplexRest {
    pub history_addresses: Vec<String>,
    pub native_history_states: Vec<u64>,
    pub final_hidden: CarrierSectionRest,
    pub vocabulary_extent: usize,
    /// Row-major predecessor lower endpoints. Upper endpoints are `lower + interval_width`.
    pub predecessor_lower: Vec<i64>,
    pub interval_width: i64,
    pub factors: Vec<RestedPotentialFactor>,
    pub receiver_rows: Vec<u32>,
    pub decoder: BTreeMap<u32, String>,
    pub receiver_certificates: Vec<PotentialReceiverCertificate>,
    pub open_exterior: Vec<String>,
    pub identity_sha256: String,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Metadata {
    schema: String,
    history_addresses: Vec<String>,
    native_history_states: Vec<u64>,
    hidden_address: String,
    hidden_rows: usize,
    hidden_columns: usize,
    hidden_grain: u32,
    vocabulary_extent: usize,
    interval_width: i64,
    factors: Vec<RestedPotentialFactor>,
    receiver_rows: Vec<u32>,
    decoder: BTreeMap<u32, String>,
    receiver_certificates: Vec<PotentialReceiverCertificate>,
    open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ForeignPotentialObstruction {
    pub native_history_state: u64,
    pub admitted_native_history_states: Vec<u64>,
    pub foreign_fallback_permitted: bool,
}

/// The addressed next occurrence requested by a rested terminal receiver but not carried by its
/// current coefficient section. This is the only receipt which may ask construction to enlarge
/// that section; it never licenses inference-time foreign fallback.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AddressedPotentialSectionObstruction {
    pub predecessor_history_address: String,
    pub emitted_native_address: u32,
    pub emitted_surface: String,
    pub requested_history_address: String,
    pub admitted_history_addresses: Vec<String>,
    pub foreign_fallback_permitted: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "status", rename_all = "kebab-case")]
pub enum AddressedPotentialSuccessor {
    Admitted {
        predecessor_history_address: String,
        emitted_native_address: u32,
        emitted_surface: String,
        successor_history_address: String,
        native_history_state: u64,
    },
    OutOfSection(AddressedPotentialSectionObstruction),
}

#[derive(Debug, Error)]
pub enum ForeignPotentialRestRefusal {
    #[error("the foreign potential rest has malformed or inconsistent incidence")]
    Shape,
    #[error("the foreign potential rest identity does not reconstruct")]
    Identity,
    #[error("foreign potential rest wire refused: {0}")]
    Wire(String),
    #[error("the exact cultivated potential left the signed-word carrier")]
    CarrierOverflow,
    #[error("native history left the cultivated reachable section")]
    OutOfSection(#[from] ForeignPotentialObstructionError),
    #[error("resident foreign potential apparatus refused: {0}")]
    Apparatus(String),
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
#[error("native history {0:?} leaves the cultivated potential section")]
pub struct ForeignPotentialObstructionError(pub ForeignPotentialObstruction);

impl ForeignPotentialComplexRest {
    #[allow(clippy::too_many_arguments)]
    pub fn seal(
        history_addresses: Vec<String>,
        native_history_states: Vec<u64>,
        final_hidden: CarrierSectionRest,
        vocabulary_extent: usize,
        predecessor_lower: Vec<i64>,
        interval_width: i64,
        factors: Vec<RestedPotentialFactor>,
        receiver_rows: Vec<u32>,
        decoder: BTreeMap<u32, String>,
        receiver_certificates: Vec<PotentialReceiverCertificate>,
        open_exterior: Vec<String>,
    ) -> Result<Self, ForeignPotentialRestRefusal> {
        let mut rest = Self {
            history_addresses,
            native_history_states,
            final_hidden,
            vocabulary_extent,
            predecessor_lower,
            interval_width,
            factors,
            receiver_rows,
            decoder,
            receiver_certificates,
            open_exterior,
            identity_sha256: String::new(),
        };
        rest.validate_shape()?;
        rest.identity_sha256 = hex(&Sha256::digest(rest.body_bytes()?));
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, ForeignPotentialRestRefusal> {
        self.validate()?;
        let mut bytes = self.body_bytes()?;
        bytes.extend(Sha256::digest(&bytes));
        Ok(bytes)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, ForeignPotentialRestRefusal> {
        if bytes.len() < MAGIC.len() + 8 + 32 || !bytes.starts_with(MAGIC) {
            return Err(ForeignPotentialRestRefusal::Wire("header".to_owned()));
        }
        let (body, expected_digest) = bytes.split_at(bytes.len() - 32);
        if Sha256::digest(body).as_slice() != expected_digest {
            return Err(ForeignPotentialRestRefusal::Identity);
        }
        let mut cursor = MAGIC.len();
        let metadata_len = take_u64(body, &mut cursor)? as usize;
        let metadata_end = cursor
            .checked_add(metadata_len)
            .filter(|end| *end <= body.len())
            .ok_or_else(|| ForeignPotentialRestRefusal::Wire("metadata extent".to_owned()))?;
        let metadata: Metadata = serde_json::from_slice(&body[cursor..metadata_end])
            .map_err(|error| ForeignPotentialRestRefusal::Wire(error.to_string()))?;
        if metadata.schema != SCHEMA {
            return Err(ForeignPotentialRestRefusal::Wire("schema".to_owned()));
        }
        cursor = metadata_end;
        let hidden_entries = metadata
            .hidden_rows
            .checked_mul(metadata.hidden_columns)
            .ok_or(ForeignPotentialRestRefusal::Shape)?;
        let hidden = take_i64s(body, &mut cursor, hidden_entries)?;
        let potential_entries = metadata
            .vocabulary_extent
            .checked_mul(metadata.history_addresses.len())
            .ok_or(ForeignPotentialRestRefusal::Shape)?;
        let predecessor_lower = take_i64s(body, &mut cursor, potential_entries)?;
        if cursor != body.len() {
            return Err(ForeignPotentialRestRefusal::Wire(
                "trailing body".to_owned(),
            ));
        }
        let rest = Self {
            history_addresses: metadata.history_addresses,
            native_history_states: metadata.native_history_states,
            final_hidden: CarrierSectionRest {
                address: metadata.hidden_address,
                rows: metadata.hidden_rows,
                columns: metadata.hidden_columns,
                grain: metadata.hidden_grain,
                entries: hidden,
            },
            vocabulary_extent: metadata.vocabulary_extent,
            predecessor_lower,
            interval_width: metadata.interval_width,
            factors: metadata.factors,
            receiver_rows: metadata.receiver_rows,
            decoder: metadata.decoder,
            receiver_certificates: metadata.receiver_certificates,
            open_exterior: metadata.open_exterior,
            identity_sha256: hex(&Sha256::digest(body)),
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn validate(&self) -> Result<(), ForeignPotentialRestRefusal> {
        self.validate_shape()?;
        if self.identity_sha256 != hex(&Sha256::digest(self.body_bytes()?)) {
            return Err(ForeignPotentialRestRefusal::Identity);
        }
        Ok(())
    }

    pub fn one_hot_for_native(
        &self,
        native_history_state: u64,
    ) -> Result<Vec<Rat>, ForeignPotentialObstructionError> {
        let Some(history) = self
            .native_history_states
            .iter()
            .position(|native| *native == native_history_state)
        else {
            return Err(ForeignPotentialObstructionError(
                ForeignPotentialObstruction {
                    native_history_state,
                    admitted_native_history_states: self.native_history_states.clone(),
                    foreign_fallback_permitted: false,
                },
            ));
        };
        Ok((0..self.history_addresses.len())
            .map(|at| {
                if at == history {
                    Rat::from_integer(BigInt::from(1))
                } else {
                    Rat::from_integer(BigInt::from(0))
                }
            })
            .collect())
    }

    /// Resolve one emitted face as an addressed successor occurrence. Address construction is a
    /// lineage operation over an already-returned receiver face; it neither selects the face nor
    /// conducts the foreign organ. An absent successor remains a typed open-section receipt.
    pub fn addressed_successor(
        &self,
        predecessor_history_address: &str,
        emitted_native_address: u32,
    ) -> Result<AddressedPotentialSuccessor, ForeignPotentialRestRefusal> {
        if !self
            .history_addresses
            .iter()
            .any(|address| address == predecessor_history_address)
        {
            return Err(ForeignPotentialRestRefusal::Shape);
        }
        let emitted_surface = self.decode(emitted_native_address)?.to_owned();
        let successor_history_address =
            format!("{predecessor_history_address}/emission/{emitted_native_address}");
        if let Some(successor) = self
            .history_addresses
            .iter()
            .position(|address| address == &successor_history_address)
        {
            Ok(AddressedPotentialSuccessor::Admitted {
                predecessor_history_address: predecessor_history_address.to_owned(),
                emitted_native_address,
                emitted_surface,
                successor_history_address,
                native_history_state: self.native_history_states[successor],
            })
        } else {
            Ok(AddressedPotentialSuccessor::OutOfSection(
                AddressedPotentialSectionObstruction {
                    predecessor_history_address: predecessor_history_address.to_owned(),
                    emitted_native_address,
                    emitted_surface,
                    requested_history_address: successor_history_address,
                    admitted_history_addresses: self.history_addresses.clone(),
                    foreign_fallback_permitted: false,
                },
            ))
        }
    }

    pub fn cultivated_receiver_incidence(
        &self,
    ) -> Result<(Vec<i64>, Vec<i64>), ForeignPotentialRestRefusal> {
        let histories = self.history_addresses.len();
        let mut lower = Vec::with_capacity(self.receiver_rows.len() * histories);
        let mut upper = Vec::with_capacity(self.receiver_rows.len() * histories);
        for row in &self.receiver_rows {
            for history in 0..histories {
                let base = self.predecessor_lower[*row as usize * histories + history];
                let mut delta = 0i128;
                for factor in self
                    .factors
                    .iter()
                    .filter(|factor| factor.target_native_address == *row)
                    .filter(|factor| {
                        factor
                            .founding_native_history_states
                            .contains(&self.native_history_states[history])
                    })
                {
                    let hidden =
                        self.final_hidden.entries[factor.selector_coordinate * histories + history];
                    delta += i128::from(factor.multiplier) * i128::from(hidden);
                }
                let from = i128::from(base) + delta;
                let until = from + i128::from(self.interval_width);
                lower.push(
                    i64::try_from(from)
                        .map_err(|_| ForeignPotentialRestRefusal::CarrierOverflow)?,
                );
                upper.push(
                    i64::try_from(until)
                        .map_err(|_| ForeignPotentialRestRefusal::CarrierOverflow)?,
                );
            }
        }
        Ok((lower, upper))
    }

    pub fn mount_receiver(
        &self,
    ) -> Result<ResidentForeignPotentialReceiver, ForeignPotentialRestRefusal> {
        let card = CudaRefineExecutor::new()
            .map_err(|error| ForeignPotentialRestRefusal::Apparatus(error.to_string()))?;
        self.mount_receiver_on(card)
    }

    /// Transfer an already-used apparatus chart into the terminal receiver. Independent organ
    /// returns may therefore precede this mount without constructing a second device ecology.
    pub fn mount_receiver_on(
        &self,
        card: CudaRefineExecutor,
    ) -> Result<ResidentForeignPotentialReceiver, ForeignPotentialRestRefusal> {
        self.validate()?;
        let (lower, upper) = self.cultivated_receiver_incidence()?;
        let resident = ResidentIntervalPotentialReceiver::mount(
            card,
            "native/terminal-potential-receiver",
            self.receiver_rows.len(),
            self.history_addresses.len(),
            &self.receiver_rows,
            &lower,
            &upper,
        )
        .map_err(|error| ForeignPotentialRestRefusal::Apparatus(error.to_string()))?;
        Ok(ResidentForeignPotentialReceiver { resident })
    }

    pub fn decode(&self, native: u32) -> Result<&str, ForeignPotentialRestRefusal> {
        self.decoder
            .get(&native)
            .map(String::as_str)
            .ok_or(ForeignPotentialRestRefusal::Shape)
    }

    fn validate_shape(&self) -> Result<(), ForeignPotentialRestRefusal> {
        let histories = self.history_addresses.len();
        let unique_histories = self.history_addresses.iter().collect::<BTreeSet<_>>();
        let unique_native = self.native_history_states.iter().collect::<BTreeSet<_>>();
        let unique_rows = self.receiver_rows.iter().collect::<BTreeSet<_>>();
        let expected_potential = self.vocabulary_extent.checked_mul(histories);
        if histories == 0
            || unique_histories.len() != histories
            || self.native_history_states.len() != histories
            || unique_native.len() != histories
            || self.final_hidden.columns != histories
            || self.final_hidden.rows == 0
            || self.final_hidden.entries.len() != self.final_hidden.rows * histories
            || self.vocabulary_extent == 0
            || expected_potential != Some(self.predecessor_lower.len())
            || self.interval_width <= 0
            || self.receiver_rows.is_empty()
            || unique_rows.len() != self.receiver_rows.len()
            || self.receiver_rows.iter().any(|row| {
                *row as usize >= self.vocabulary_extent || !self.decoder.contains_key(row)
            })
            || self.receiver_certificates.len() != histories
        {
            return Err(ForeignPotentialRestRefusal::Shape);
        }
        let admitted = self
            .native_history_states
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        if self.factors.iter().any(|factor| {
            factor.address.is_empty()
                || factor.parent_factor_addresses.is_empty()
                || factor.target_native_address as usize >= self.vocabulary_extent
                || factor.selector_coordinate >= self.final_hidden.rows
                || factor.founding_native_history_states.is_empty()
                || factor
                    .founding_native_history_states
                    .iter()
                    .any(|native| !admitted.contains(native))
                || !self.receiver_rows.contains(&factor.target_native_address)
        }) {
            return Err(ForeignPotentialRestRefusal::Shape);
        }
        Ok(())
    }

    fn body_bytes(&self) -> Result<Vec<u8>, ForeignPotentialRestRefusal> {
        let metadata = Metadata {
            schema: SCHEMA.to_owned(),
            history_addresses: self.history_addresses.clone(),
            native_history_states: self.native_history_states.clone(),
            hidden_address: self.final_hidden.address.clone(),
            hidden_rows: self.final_hidden.rows,
            hidden_columns: self.final_hidden.columns,
            hidden_grain: self.final_hidden.grain,
            vocabulary_extent: self.vocabulary_extent,
            interval_width: self.interval_width,
            factors: self.factors.clone(),
            receiver_rows: self.receiver_rows.clone(),
            decoder: self.decoder.clone(),
            receiver_certificates: self.receiver_certificates.clone(),
            open_exterior: self.open_exterior.clone(),
        };
        let metadata = serde_json::to_vec(&metadata)
            .map_err(|error| ForeignPotentialRestRefusal::Wire(error.to_string()))?;
        let mut bytes = Vec::with_capacity(
            MAGIC.len()
                + 8
                + metadata.len()
                + 8 * (self.final_hidden.entries.len() + self.predecessor_lower.len()),
        );
        bytes.extend(MAGIC);
        bytes.extend((metadata.len() as u64).to_le_bytes());
        bytes.extend(metadata);
        bytes.extend(
            self.final_hidden
                .entries
                .iter()
                .flat_map(|entry| entry.to_le_bytes()),
        );
        bytes.extend(
            self.predecessor_lower
                .iter()
                .flat_map(|entry| entry.to_le_bytes()),
        );
        Ok(bytes)
    }
}

/// Soulkiller-side exterior testimony at one receiver-exact potential boundary.
/// The returned owner has no reverse edge into this module.
pub fn condense_native_anatomical_potential(
    foreign: &ForeignPotentialComplexRest,
    anatomy: &NativeAnatomyRest,
    exterior: &ExteriorNativeAnatomyWitness,
) -> Result<NativeAnatomicalPotentialRest, ForeignPotentialRestRefusal> {
    foreign.validate()?;
    anatomy
        .validate()
        .map_err(|error| ForeignPotentialRestRefusal::Wire(error.to_string()))?;
    exterior
        .validate(anatomy)
        .map_err(|error| ForeignPotentialRestRefusal::Wire(error.to_string()))?;
    if exterior.occurrences.len() != foreign.history_addresses.len()
        || exterior.quotient.source_population.len() != foreign.history_addresses.len()
        || exterior
            .occurrences
            .iter()
            .enumerate()
            .any(|(node, occurrence)| {
                occurrence.coefficient_node != node
                    || occurrence.occurrence != foreign.history_addresses[node]
            })
    {
        return Err(ForeignPotentialRestRefusal::Shape);
    }
    let (source_lower, source_upper) = foreign.cultivated_receiver_incidence()?;
    let histories = foreign.history_addresses.len();
    let native_population = anatomy.native_population.clone();
    if exterior.quotient.quotient.len() != histories {
        return Err(ForeignPotentialRestRefusal::Shape);
    }
    let mut lower_incidence = Vec::with_capacity(
        foreign
            .receiver_rows
            .len()
            .saturating_mul(native_population.len()),
    );
    let mut upper_incidence = Vec::with_capacity(lower_incidence.capacity());
    let mut class_certificates = Vec::with_capacity(native_population.len());
    for native in &native_population {
        let class = exterior
            .classes
            .iter()
            .find(|class| class.native == *native)
            .ok_or(ForeignPotentialRestRefusal::Shape)?;
        let representative = *class
            .coefficient_nodes
            .iter()
            .min()
            .ok_or(ForeignPotentialRestRefusal::Shape)?;
        if class.coefficient_nodes.iter().any(|node| {
            foreign.receiver_certificates[*node]
                .cultivated_selected_native_addresses
                .as_slice()
                != [class.emitted_native_address]
        }) {
            return Err(ForeignPotentialRestRefusal::Shape);
        }
        for row in 0..foreign.receiver_rows.len() {
            lower_incidence.push(source_lower[row * histories + representative]);
            upper_incidence.push(source_upper[row * histories + representative]);
        }
        class_certificates.push(NativePotentialClassCertificate {
            native: *native,
            history_addresses: class.occurrences.clone(),
            selected_native_address: class.emitted_native_address,
        });
    }
    let lower_incidence = transpose_class_major(
        &lower_incidence,
        native_population.len(),
        foreign.receiver_rows.len(),
    )?;
    let upper_incidence = transpose_class_major(
        &upper_incidence,
        native_population.len(),
        foreign.receiver_rows.len(),
    )?;
    NativeAnatomicalPotentialRest::seal(
        native_population,
        foreign.receiver_rows.clone(),
        lower_incidence,
        upper_incidence,
        foreign.decoder.clone(),
        class_certificates,
        foreign.open_exterior.clone(),
    )
    .map_err(|error| ForeignPotentialRestRefusal::Wire(error.to_string()))
}

pub struct ResidentForeignPotentialReceiver {
    resident: ResidentIntervalPotentialReceiver,
}

fn transpose_class_major(
    values: &[i64],
    classes: usize,
    rows: usize,
) -> Result<Vec<i64>, ForeignPotentialRestRefusal> {
    if values.len() != classes.saturating_mul(rows) {
        return Err(ForeignPotentialRestRefusal::Shape);
    }
    Ok((0..rows)
        .flat_map(|row| (0..classes).map(move |class| values[class * rows + row]))
        .collect())
}

impl ResidentForeignPotentialReceiver {
    pub fn conduct(
        &mut self,
        fronts: &[Vec<Rat>],
    ) -> Result<ResidentIntervalPotentialReturn, ForeignPotentialRestRefusal> {
        self.resident
            .conduct(fronts)
            .map_err(|error| ForeignPotentialRestRefusal::Apparatus(error.to_string()))
    }
}

fn take_u64(bytes: &[u8], cursor: &mut usize) -> Result<u64, ForeignPotentialRestRefusal> {
    let end = cursor
        .checked_add(8)
        .filter(|end| *end <= bytes.len())
        .ok_or_else(|| ForeignPotentialRestRefusal::Wire("u64 extent".to_owned()))?;
    let value = u64::from_le_bytes(
        bytes[*cursor..end]
            .try_into()
            .map_err(|_| ForeignPotentialRestRefusal::Wire("u64".to_owned()))?,
    );
    *cursor = end;
    Ok(value)
}

fn take_i64s(
    bytes: &[u8],
    cursor: &mut usize,
    count: usize,
) -> Result<Vec<i64>, ForeignPotentialRestRefusal> {
    let octets = count
        .checked_mul(8)
        .ok_or(ForeignPotentialRestRefusal::Shape)?;
    let end = cursor
        .checked_add(octets)
        .filter(|end| *end <= bytes.len())
        .ok_or_else(|| ForeignPotentialRestRefusal::Wire("i64 extent".to_owned()))?;
    let values = bytes[*cursor..end]
        .chunks_exact(8)
        .map(|word| i64::from_le_bytes(word.try_into().expect("exact chunk")))
        .collect();
    *cursor = end;
    Ok(values)
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_potential_rest_roundtrips_and_gates_each_factor_by_its_founding_history() {
        let hidden = CarrierSectionRest {
            address: "hidden".to_owned(),
            rows: 2,
            columns: 2,
            grain: 0,
            entries: vec![3, 5, 7, 11],
        };
        let factors = vec![RestedPotentialFactor {
            address: "factor-a".to_owned(),
            parent_factor_addresses: vec!["parent-a".to_owned()],
            target_native_address: 2,
            selector_coordinate: 1,
            multiplier: 2,
            founding_native_history_states: vec![10],
        }];
        let certificates = [10u64, 20]
            .into_iter()
            .enumerate()
            .map(|(history, native)| PotentialReceiverCertificate {
                history_address: format!("history-{history}"),
                native_history_state: native,
                predecessor_selected_native_addresses: vec![0],
                cultivated_selected_native_addresses: vec![2],
                predecessor_top_lower: 1,
                cultivated_top_lower: 2,
                greatest_omitted_upper: 0,
                shortest_omitted_competitor: 1,
                admitted_factor_addresses: if history == 0 {
                    vec!["factor-a".to_owned()]
                } else {
                    Vec::new()
                },
                complete_predecessor_potential_sha256: format!("{history:064x}"),
            })
            .collect();
        let rest = ForeignPotentialComplexRest::seal(
            vec!["history-0".to_owned(), "history-1".to_owned()],
            vec![10, 20],
            hidden,
            3,
            vec![1, 2, 0, 0, 4, 6],
            1,
            factors,
            vec![0, 2],
            BTreeMap::from([(0, "zero".to_owned()), (2, "two".to_owned())]),
            certificates,
            vec!["other histories remain open".to_owned()],
        )
        .expect("rest");
        let bytes = rest.canonical_bytes().expect("bytes");
        let returned = ForeignPotentialComplexRest::read(&bytes).expect("read");
        assert_eq!(returned.identity_sha256, rest.identity_sha256);
        let (lower, upper) = returned.cultivated_receiver_incidence().expect("incidence");
        assert_eq!(lower, vec![1, 2, 18, 6]);
        assert_eq!(upper, vec![2, 3, 19, 7]);
        assert!(returned.one_hot_for_native(10).is_ok());
        assert!(returned.one_hot_for_native(99).is_err());
        let obstruction = returned
            .addressed_successor("history-0", 2)
            .expect("addressed successor");
        assert!(matches!(
            obstruction,
            AddressedPotentialSuccessor::OutOfSection(AddressedPotentialSectionObstruction {
                foreign_fallback_permitted: false,
                ..
            })
        ));
    }
}
