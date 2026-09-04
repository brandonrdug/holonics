//! Native mathematical cultivation after a separately addressed world return.
//!
//! This owner moves one `NativeHexisRest` into continuing standing and stores only a local
//! returned cultivation face beside it. The same resident fixed-section law receives either the
//! predecessor or cultivated bits. No checker status, theorem syntax, subject label, or file kind
//! participates. Withdrawal consumes the wrapper and returns the exact predecessor owner.

use holonic_engine::cuda_refine::{CudaRefineExecutor, DeviceNativeFixedSectionFamilies};
use life::mathematical_particle::{
    NativeHexisRest, NativeMathematicalConsequence, NativeMathematicalInquiry,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeMathematicalWorldReturn {
    pub occurrence: String,
    pub emitted_native_consequence: String,
    pub returned_optical_occurrence: String,
    pub returned_multimodal_rest_sha256: String,
    pub causing_laboratory_occurrences: Vec<String>,
    pub exact_return_difference_sha256: String,
    pub support_families: Vec<u32>,
    pub separately_addressed_after_emission: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCultivationDelta {
    pub occurrence: String,
    pub predecessor_rest_sha256: String,
    pub world_return_occurrence: String,
    pub predecessor_flags: Vec<u32>,
    pub successor_flags: Vec<u32>,
    pub exact_support_families: Vec<u32>,
    pub metric_adjoint_orientation: Vec<i8>,
    pub exact_rank: u32,
    pub open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCultivationStanding {
    pub schema: String,
    pub predecessor_rest_sha256: String,
    pub world_return: NativeMathematicalWorldReturn,
    pub delta: NativeCultivationDelta,
    pub developmental_family_occurrences: Vec<String>,
    pub held_out_family_occurrences: Vec<String>,
    pub disjoint_control_occurrences: Vec<String>,
}

/// One continuing native mathematical ecology; intentionally not `Clone`.
#[derive(Debug, PartialEq, Eq)]
pub struct NativeCultivatedMathematicalRest {
    predecessor: NativeHexisRest,
    standing: NativeCultivationStanding,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeRouteReturn {
    pub transported_sections: Vec<i64>,
    pub constraint_residuals: Vec<i64>,
    pub selected_routes: Vec<u32>,
    pub locally_ablated_routes: Vec<u32>,
    pub joint_cultivated: bool,
    pub local_ablated_joint: Vec<u32>,
    pub device: String,
    pub launches: u64,
    pub synchronizations: u64,
    pub typed_reductions: u64,
    pub semantic_work: String,
    pub semantic_span: u64,
    pub resident_octets: u64,
    pub transfer_octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCultivationWithdrawal {
    pub cultivated_rest_sha256: String,
    pub predecessor_rest_sha256: String,
    pub restored_rest_sha256: String,
    pub exact_predecessor_restored: bool,
}

impl NativeCultivatedMathematicalRest {
    #[allow(clippy::too_many_arguments)]
    pub fn cultivate(
        predecessor: NativeHexisRest,
        world_return: NativeMathematicalWorldReturn,
        developmental_family_occurrences: Vec<String>,
        held_out_family_occurrences: Vec<String>,
        disjoint_control_occurrences: Vec<String>,
    ) -> Result<Self, String> {
        predecessor.validate().map_err(|error| error.to_string())?;
        let predecessor_rest_sha256 = predecessor
            .canonical_identity()
            .map_err(|error| error.to_string())?;
        let families = predecessor.standing().carrier_charts.len();
        let expected_support = (0..families as u32).collect::<Vec<_>>();
        if world_return.occurrence.is_empty()
            || world_return.emitted_native_consequence.is_empty()
            || world_return.returned_optical_occurrence.is_empty()
            || !digest_like(&world_return.returned_multimodal_rest_sha256)
            || world_return.causing_laboratory_occurrences.len() < 3
            || !digest_like(&world_return.exact_return_difference_sha256)
            || world_return.support_families != expected_support
            || !world_return.separately_addressed_after_emission
            || developmental_family_occurrences.len() < 3
            || held_out_family_occurrences.is_empty()
            || disjoint_control_occurrences.is_empty()
        {
            return Err(
                "the native world return does not found the declared cultivation".to_owned(),
            );
        }
        let predecessor_flags = vec![0; families];
        let successor_flags = vec![1; families];
        let delta_body = (
            &predecessor_rest_sha256,
            &world_return.occurrence,
            &predecessor_flags,
            &successor_flags,
            &expected_support,
        );
        let delta = NativeCultivationDelta {
            occurrence: format!("n3/delta/{}", value_digest(&delta_body)?),
            predecessor_rest_sha256: predecessor_rest_sha256.clone(),
            world_return_occurrence: world_return.occurrence.clone(),
            predecessor_flags,
            successor_flags,
            exact_support_families: expected_support,
            metric_adjoint_orientation: predecessor
                .standing()
                .generator
                .constraint_orientation
                .clone(),
            exact_rank: 1,
            open_exterior: vec![
                "the local returned cultivation is exact only for the declared fixed-section successor family".to_owned(),
                "nonlinear varieties and successor words outside the native decoder remain open".to_owned(),
            ],
        };
        let rest = Self {
            predecessor,
            standing: NativeCultivationStanding {
                schema: "holonics.n3.native-cultivation-standing.v1".to_owned(),
                predecessor_rest_sha256,
                world_return,
                delta,
                developmental_family_occurrences,
                held_out_family_occurrences,
                disjoint_control_occurrences,
            },
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(
        predecessor_standing: &[u8],
        predecessor_decoder: &[u8],
        predecessor_fibres: &[u8],
        cultivation_standing: &[u8],
    ) -> Result<Self, String> {
        let predecessor = NativeHexisRest::read(
            predecessor_standing,
            predecessor_decoder,
            predecessor_fibres,
        )
        .map_err(|error| error.to_string())?;
        let standing =
            serde_json::from_slice(cultivation_standing).map_err(|error| error.to_string())?;
        let rest = Self {
            predecessor,
            standing,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn standing_bytes(&self) -> Result<Vec<u8>, String> {
        self.validate()?;
        serde_json::to_vec(&self.standing).map_err(|error| error.to_string())
    }

    pub fn canonical_identity(&self) -> Result<String, String> {
        let mut digest = Sha256::new();
        for bytes in [
            self.predecessor
                .standing_bytes()
                .map_err(|error| error.to_string())?,
            self.predecessor
                .decoder_bytes()
                .map_err(|error| error.to_string())?,
            self.predecessor
                .fibre_bytes()
                .map_err(|error| error.to_string())?,
            self.standing_bytes()?,
        ] {
            digest.update((bytes.len() as u64).to_le_bytes());
            digest.update(bytes);
        }
        Ok(hex(digest.finalize()))
    }

    pub fn predecessor(&self) -> &NativeHexisRest {
        &self.predecessor
    }

    pub fn standing(&self) -> &NativeCultivationStanding {
        &self.standing
    }

    pub fn conduct_predecessor(
        &self,
        sections: &[Vec<i64>],
        card: &mut CudaRefineExecutor,
    ) -> Result<NativeRouteReturn, String> {
        self.conduct(sections, &self.standing.delta.predecessor_flags, card)
    }

    pub fn conduct_cultivated(
        &self,
        sections: &[Vec<i64>],
        card: &mut CudaRefineExecutor,
    ) -> Result<NativeRouteReturn, String> {
        self.conduct(sections, &self.standing.delta.successor_flags, card)
    }

    pub fn conduct_rich_cultivated_consequence(
        &self,
        inquiry: &NativeMathematicalInquiry,
        card: &mut CudaRefineExecutor,
    ) -> Result<NativeMathematicalConsequence, String> {
        self.predecessor
            .conduct_native_mathematical_inquiry_on_card(inquiry, card)
            .map_err(|error| error.to_string())
    }

    pub fn withdraw(self) -> Result<(NativeHexisRest, NativeCultivationWithdrawal), String> {
        self.validate()?;
        let cultivated_rest_sha256 = self.canonical_identity()?;
        let restored_rest_sha256 = self
            .predecessor
            .canonical_identity()
            .map_err(|error| error.to_string())?;
        let receipt = NativeCultivationWithdrawal {
            cultivated_rest_sha256,
            predecessor_rest_sha256: self.standing.predecessor_rest_sha256.clone(),
            restored_rest_sha256: restored_rest_sha256.clone(),
            exact_predecessor_restored: restored_rest_sha256
                == self.standing.predecessor_rest_sha256,
        };
        if !receipt.exact_predecessor_restored {
            return Err("native cultivation withdrawal did not restore its predecessor".to_owned());
        }
        Ok((self.predecessor, receipt))
    }

    fn conduct(
        &self,
        sections: &[Vec<i64>],
        cultivation: &[u32],
        card: &mut CudaRefineExecutor,
    ) -> Result<NativeRouteReturn, String> {
        let families = self.predecessor.standing().carrier_charts.len();
        let dimension = self.predecessor.standing().generator.dimension as usize;
        if sections.len() != families || sections.iter().any(|section| section.len() != dimension) {
            return Err("the cultivated section family leaves the native boundary".to_owned());
        }
        let returned = card
            .conduct_native_fixed_section_families_on_device(
                &sections.iter().flatten().copied().collect::<Vec<_>>(),
                &self.predecessor.standing().generator.constraint_orientation,
                &self
                    .predecessor
                    .standing()
                    .generator
                    .action_difference_orientation,
                &self
                    .predecessor
                    .standing()
                    .carrier_charts
                    .iter()
                    .map(|chart| chart.modulus)
                    .collect::<Vec<_>>(),
                cultivation,
            )
            .map_err(|error| error.to_string())?;
        Ok(route_return(returned, card.device_name().to_owned()))
    }

    fn validate(&self) -> Result<(), String> {
        self.predecessor
            .validate()
            .map_err(|error| error.to_string())?;
        let predecessor = self
            .predecessor
            .canonical_identity()
            .map_err(|error| error.to_string())?;
        let families = self.predecessor.standing().carrier_charts.len();
        if self.standing.schema != "holonics.n3.native-cultivation-standing.v1"
            || self.standing.predecessor_rest_sha256 != predecessor
            || self.standing.delta.predecessor_rest_sha256 != predecessor
            || self.standing.delta.world_return_occurrence != self.standing.world_return.occurrence
            || self.standing.delta.predecessor_flags != vec![0; families]
            || self.standing.delta.successor_flags != vec![1; families]
            || self.standing.delta.exact_support_families
                != (0..families as u32).collect::<Vec<_>>()
            || self.standing.delta.metric_adjoint_orientation
                != self.predecessor.standing().generator.constraint_orientation
            || self.standing.delta.exact_rank != 1
            || self.standing.delta.open_exterior.is_empty()
        {
            return Err("the native cultivation standing moved".to_owned());
        }
        Ok(())
    }
}

fn route_return(returned: DeviceNativeFixedSectionFamilies, device: String) -> NativeRouteReturn {
    NativeRouteReturn {
        transported_sections: returned.transported_sections,
        constraint_residuals: returned.constraint_residuals,
        selected_routes: returned.selected_route,
        locally_ablated_routes: returned.ablated_route,
        joint_cultivated: returned.joint_cultivated,
        local_ablated_joint: returned.local_ablated_joint,
        device,
        launches: returned.launches,
        synchronizations: returned.synchronizations,
        typed_reductions: returned.typed_reductions,
        semantic_work: returned.semantic_work.to_string(),
        semantic_span: returned.semantic_span,
        resident_octets: returned.resident_octets,
        transfer_octets: returned.host_ingress_octets + returned.host_egress_octets,
    }
}

fn digest_like(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn value_digest(value: &impl Serialize) -> Result<String, String> {
    serde_json::to_vec(value)
        .map(|bytes| hex(Sha256::digest(bytes)))
        .map_err(|error| error.to_string())
}

fn hex(bytes: impl AsRef<[u8]>) -> String {
    bytes
        .as_ref()
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}
