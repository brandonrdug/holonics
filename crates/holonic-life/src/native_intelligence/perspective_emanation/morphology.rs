use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::ExactRatMatrix;
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::Serialize;
use sha2::{Digest, Sha256};

use super::{
    AddressedEmanationIngress, EmanationDeed, EmanationError, EmanationMorphology,
    NativePotentialCellBody, NativeProsePotentialComplex,
};

pub(super) fn population_surface(population: usize, singular: &str) -> String {
    if population == 1 {
        format!("one {singular}")
    } else {
        format!("{population} {singular}s")
    }
}

pub(super) fn morphology_atoms(
    potential: &NativeProsePotentialComplex,
    morphology: &EmanationMorphology,
    deed: EmanationDeed,
) -> BTreeMap<String, i64> {
    let mut atoms = BTreeMap::new();
    // The complete potential and condensation receipts retain every cell.  The loss support uses
    // their natural quotient coordinates rather than expanding unchanged cells into a dense
    // diagonal matrix.
    atoms.insert(format!("potential/{}", potential.identity_sha256), 1);
    for kind in &morphology.condensation.requested_future_receiver_family {
        atoms.insert(format!("requested-receiver/{kind:?}"), 1);
    }
    for kind in &morphology.condensation.dependency_closed_family {
        atoms.insert(format!("dependency-closure/{kind:?}"), 1);
    }
    for pair in morphology.kind_order.windows(2) {
        atoms.insert(format!("kind-order/{:?}/{:?}", pair[0], pair[1]), 1);
    }
    for participant in &potential.cells {
        let NativePotentialCellBody::Participant {
            participant_identity,
        } = &participant.body
        else {
            continue;
        };
        let role = if morphology.perspective.speaker.as_deref() == Some(participant_identity) {
            "speaker"
        } else if morphology.perspective.addressee.as_deref() == Some(participant_identity) {
            "addressee"
        } else {
            "referent"
        };
        atoms.insert(format!("perspective/{participant_identity}/{role}"), 1);
    }
    atoms.insert(format!("voice/{:?}", morphology.voice), 1);
    atoms.insert(format!("deed/{deed:?}"), 1);
    for continuation in &morphology.continuation_occurrences {
        atoms.insert(format!("continuation/{continuation}"), 1);
    }
    atoms
}

pub(super) fn sparse_difference(
    candidate: &BTreeMap<String, i64>,
    returned: &BTreeMap<String, i64>,
) -> Result<(Vec<String>, Vec<i64>, Vec<i64>, Vec<i64>, BTreeSet<String>), EmanationError> {
    let complete_basis = candidate
        .keys()
        .chain(returned.keys())
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    if complete_basis.is_empty() {
        return Err(EmanationError::Difference(
            "the addressed basis is empty".to_owned(),
        ));
    }
    let zero_difference_reconstruction_fibre = complete_basis
        .iter()
        .filter(|address| {
            candidate.get(*address).copied().unwrap_or(0)
                == returned.get(*address).copied().unwrap_or(0)
        })
        .cloned()
        .collect::<BTreeSet<_>>();
    let basis = complete_basis
        .into_iter()
        .filter(|address| !zero_difference_reconstruction_fibre.contains(address))
        .collect::<Vec<_>>();
    if basis.is_empty() {
        return Err(EmanationError::ZeroDifference);
    }
    let candidate_coordinates = basis
        .iter()
        .map(|address| candidate.get(address).copied().unwrap_or(0))
        .collect::<Vec<_>>();
    let returned_coordinates = basis
        .iter()
        .map(|address| returned.get(address).copied().unwrap_or(0))
        .collect::<Vec<_>>();
    let oriented_difference = returned_coordinates
        .iter()
        .zip(&candidate_coordinates)
        .map(|(right, left)| right - left)
        .collect();
    Ok((
        basis,
        candidate_coordinates,
        returned_coordinates,
        oriented_difference,
        zero_difference_reconstruction_fibre,
    ))
}

pub(super) fn exact_morphology_metric(
    candidate: &[i64],
    returned: &[i64],
) -> Result<ExactRatMatrix, EmanationError> {
    if candidate.len() != returned.len() || candidate.is_empty() {
        return Err(EmanationError::Difference(
            "the morphology coordinates have unequal rank".to_owned(),
        ));
    }
    let rank = candidate.len();
    ExactRatMatrix::new(
        (0..rank)
            .map(|row| {
                (0..rank)
                    .map(|column| {
                        if row == column {
                            rat(1
                                + candidate[row].unsigned_abs() as i64
                                + returned[row].unsigned_abs() as i64)
                        } else {
                            rat(0)
                        }
                    })
                    .collect()
            })
            .collect(),
    )
    .map_err(|error| EmanationError::Difference(error.to_string()))
}

pub(super) fn participant_identities(ingress: &AddressedEmanationIngress) -> BTreeSet<String> {
    ingress
        .participants
        .iter()
        .map(|participant| participant.identity.clone())
        .collect()
}

pub(super) fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

pub(super) fn digest_json(value: &impl Serialize) -> Result<String, EmanationError> {
    serde_json::to_vec(value)
        .map(|bytes| hex_sha256(&bytes))
        .map_err(|error| EmanationError::Wire(error.to_string()))
}

pub(super) fn hex_sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

pub(super) fn unique_nonempty<'a>(values: impl Iterator<Item = &'a str>) -> bool {
    let mut seen = BTreeSet::new();
    values
        .into_iter()
        .all(|value| !value.is_empty() && seen.insert(value))
}

pub(super) fn unique_copy<T: Copy + Ord>(values: &[T]) -> bool {
    values.iter().copied().collect::<BTreeSet<_>>().len() == values.len()
}
