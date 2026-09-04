//! Fine exterior current carried as a sparse boundary-port complex over Athena's admitted causal
//! particles.
//!
//! Exterior octets are apparatus faces, not native states, tokens, characters, or semantic
//! classes. The native particle population is the predecessor's complete receiver/history factor
//! quotient. Cultivation records oriented local incidence between exterior port occurrences and
//! exact factor support. Ingress reflects that boundary path into factor current; resident
//! Complex-Parametron conduct acts on the factor body; radiation returns plural addressed ports.
//! Longer forms are paths in this complex. No complete source string or authored unit boundary is
//! retained.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, BigUint};
use num_rational::BigRational as Rat;
use num_traits::{ToPrimitive, Zero};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use soma_membrane::ReceiverFiberIdentity;
use thiserror::Error;

use holonic_engine::{
    cuda_refine::{
        ResidentAddressedCurrentPassageReturn, ResidentBoundaryRestrictionAtlas,
        ResidentBoundaryRestrictionFront, ResidentFactoredMomentAddress,
        ResidentGeneratedPortCurrentPassageReturn, ResidentQuadraticMomentRestriction,
    },
    dimensional_wave::ExactComplexWaveCurrent,
    is_sha256_digest as is_digest,
    receiver_exact_compression::{InputId, Observation, ReceiverId},
    receiver_history_compression::NativeStateId,
};

use crate::resonance_ecology::fiber_from_bytes;

include!("basic.rs");
include!("action_builder.rs");
include!("native_projective.rs");
include!("mounted.rs");
include!("current_helpers.rs");
include!("tests.rs");
