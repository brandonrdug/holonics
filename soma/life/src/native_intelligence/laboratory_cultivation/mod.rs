//! Affine laboratory cultivation over the existing rank-four situated Athena ecology.
//!
//! The exchange world-tube is a finite addressed base complex.  Each admitted receiver-history
//! landmark already has four exact L2 reconstruction fibres, one on every period-lattice thread.
//! Relational faces and triangular cells are cultivated over that base and returned as one
//! move-owned organ.  They do not become a fifth thread and no global count vector replaces the
//! base occurrence population.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::receiver_history_compression::NativeStateId;
use holonic_engine::{
    cuda_refine::{
        CudaRefineExecutor, ResidentIntegratedFront, ResidentParticipantCausalFrontReturn,
    },
    is_sha256_digest as is_digest,
    receiver_exact_compression::ItemId,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::exchange_world_tube::{
    ContinuationAperture, ContinuationFamily, MessageAddress, VisibleMessageProjection,
};
use crate::relational_language::{realize_relational_clauses, RelationalClause, RelationalEntity};

use super::situated_cultivation::{derive_recurrent_resident_coupling, derive_resident_coupling};
use super::{
    native_relational_potential::{
        NativeDeliveryPhase, NativeRelationalCodec, NativeRelationalPotentialBuilder,
        NativeRelationalPotentialComplex,
    },
    EmanationDeed, EmanationParticipant, ExchangeSituatedProduct, LaboratoryCultivatedRest,
    MaterialAffineCellTransportReceipt, MaterialAffineTransportReceipt,
    MaterialFactorizationStanding, MaterialIntegratedResidentApparatusReceipt,
    MaterialNativeFactorization, PerspectiveChart, RecurrentLaboratoryCultivatedRest,
    RecurrentLaboratoryPredecessor, RecurrentSituatedDifferenceWithdrawal,
    SituatedCultivatedConductReturn, SituatedCultivatedEcologyRest, SituatedCultivationBranch,
    SituatedDifferenceSection, SituatedReturnedDifferenceWithdrawal,
};

include!("types.rs");
include!("affine_rest.rs");
include!("returned_rest.rs");
include!("recurrent_rest.rs");
include!("resident.rs");
include!("standing.rs");
include!("transport.rs");
