use std::collections::BTreeSet;

use sha2::{Digest, Sha256};
use thiserror::Error;

use super::{
    rest::MultimodalTransportRest,
    types::{
        MathematicalMediaPort, UnmatchedMediaMember, JOINT_MEDIA_DECODER_SCHEMA,
        JOINT_MEDIA_FIBRES_SCHEMA, JOINT_MEDIA_STANDING_SCHEMA,
    },
};

#[derive(Debug, Error, PartialEq, Eq)]
pub enum MultimodalTransportRefusal {
    #[error("the joint-media schema changed")]
    Schema,
    #[error("the product lineage is absent or malformed")]
    Lineage,
    #[error("the media family is not contiguous and plural")]
    Family,
    #[error("the separately typed media ports do not close")]
    Port,
    #[error("the common-world shared subcomplex does not close")]
    Shared,
    #[error("a source interior lost exact spatial or artifact testimony")]
    Interior,
    #[error("the native consequence decoder does not close")]
    Decoder,
    #[error("a candidate correspondence is outside its declared population")]
    Candidate,
    #[error("anchor {0} does not meet all three media ports")]
    IncompleteJointAnchor(u32),
    #[error("a generator-wise naturality square does not commute")]
    Naturality,
    #[error("the card-derived held-out multiplicities differ from the retained fibre")]
    CardCount,
    #[error("one exact extent overflowed its apparatus representation")]
    Extent,
    #[error("the persisted joint-media wire was refused: {0}")]
    Wire(String),
}

impl MultimodalTransportRest {
    pub(super) fn validate(&self) -> Result<(), MultimodalTransportRefusal> {
        if self.standing.schema != JOINT_MEDIA_STANDING_SCHEMA
            || self.decoder.schema != JOINT_MEDIA_DECODER_SCHEMA
            || self.fibres.schema != JOINT_MEDIA_FIBRES_SCHEMA
        {
            return Err(MultimodalTransportRefusal::Schema);
        }
        self.validate_lineage()?;
        self.validate_ports_and_shared()?;
        self.validate_interiors_and_decoder()?;
        self.validate_correspondence_fibres()?;
        self.validate_naturality()?;
        Ok(())
    }

    fn validate_lineage(&self) -> Result<(), MultimodalTransportRefusal> {
        let lineage = &self.standing.lineage;
        if !is_digest(&lineage.m0_source_sha256)
            || !is_digest(&lineage.m0_product_sha256)
            || !is_digest(&lineage.i4_rest_sha256)
            || !is_digest(&lineage.r4_boundary_sha256)
            || lineage.source_occurrence.is_empty()
            || self.standing.family_occurrences.len() < 2
            || self
                .standing
                .family_occurrences
                .iter()
                .any(String::is_empty)
            || self.standing.heldout_family == 0
            || self.standing.heldout_family as usize >= self.standing.family_occurrences.len()
            || self.standing.open_exterior.is_empty()
            || self.fibres.open_exterior.is_empty()
        {
            return Err(MultimodalTransportRefusal::Lineage);
        }
        Ok(())
    }

    fn validate_ports_and_shared(&self) -> Result<(), MultimodalTransportRefusal> {
        let expected_ports = [
            MathematicalMediaPort::Notation,
            MathematicalMediaPort::Vector,
            MathematicalMediaPort::RasterVision,
        ];
        if self.standing.ports.len() != expected_ports.len()
            || self
                .standing
                .ports
                .iter()
                .zip(expected_ports)
                .any(|(actual, expected)| {
                    actual.port != expected
                        || actual.boundary.is_empty()
                        || actual.family_widths.len() != self.standing.family_occurrences.len()
                        || actual.family_widths.contains(&0)
                        || !is_digest(&actual.incidence)
                })
        {
            return Err(MultimodalTransportRefusal::Port);
        }
        let shared = &self.standing.shared;
        let world = expected_ports.len() as u32;
        if shared.common_world_receiver.is_empty()
            || shared.generator_lineage.is_empty()
            || shared.predecessor != 0
            || shared.successor != 1
            || shared.successor_action != [1, 1]
            || shared.vertices.len() != expected_ports.len() + 1
            || shared.contacts.len() != expected_ports.len()
            || !shared.higher_cells.is_empty()
        {
            return Err(MultimodalTransportRefusal::Shared);
        }
        for (at, port) in expected_ports.into_iter().enumerate() {
            let vertex = &shared.vertices[at];
            let contact = &shared.contacts[at];
            if vertex.address != at as u32
                || vertex.port != Some(port)
                || vertex.boundary != self.standing.ports[at].boundary
                || contact.address != at as u32
                || contact.from != at as u32
                || contact.to != world
                || contact.hand != 1
            {
                return Err(MultimodalTransportRefusal::Shared);
            }
        }
        let world_vertex = &shared.vertices[world as usize];
        if world_vertex.address != world
            || world_vertex.port.is_some()
            || world_vertex.boundary != shared.common_world_receiver
        {
            return Err(MultimodalTransportRefusal::Shared);
        }
        Ok(())
    }

    fn validate_interiors_and_decoder(&self) -> Result<(), MultimodalTransportRefusal> {
        let family_population = self.standing.family_occurrences.len();
        let port_population = self.standing.ports.len();
        let expected_interiors = family_population
            .checked_mul(port_population)
            .ok_or(MultimodalTransportRefusal::Extent)?;
        if self.decoder.interiors.len() != expected_interiors
            || self.decoder.consequences.len() != expected_interiors * 2
            || self.fibres.native_fibres.len() != expected_interiors * 2
        {
            return Err(MultimodalTransportRefusal::Decoder);
        }
        for (at, interior) in self.decoder.interiors.iter().enumerate() {
            let family = at / port_population;
            let port_at = at % port_population;
            let port = self.standing.ports[port_at].port;
            if interior.family != family as u32
                || interior.port != port
                || interior.artifact_occurrence.is_empty()
                || !is_digest(&interior.artifact_sha256)
                || interior.chart.is_empty()
                || interior.occurrence_population == 0
                || !is_digest(&interior.incidence_sha256)
                || digest(&interior.canonical_interior) != interior.incidence_sha256
                || interior.spatial.dimension == 0
                || interior.spatial.axes.len() != interior.spatial.dimension as usize
                || !is_digest(&interior.spatial.uncertainty_fibre_sha256)
                || !is_digest(&interior.spatial.source_lineage_sha256)
                || interior.spatial.source_lineage_sha256 != interior.artifact_sha256
                || interior.spatial.axes.iter().any(|axis| {
                    axis.name.is_empty()
                        || axis.extent_numerator == 0
                        || axis.extent_denominator == 0
                        || axis.common_scale_numerator == 0
                        || axis.common_scale_denominator == 0
                        || !matches!(axis.forward_hand, -1 | 1)
                })
                || self.standing.ports[port_at].family_widths[family]
                    != interior.occurrence_population
            {
                return Err(MultimodalTransportRefusal::Interior);
            }
        }
        for (at, consequence) in self.decoder.consequences.iter().enumerate() {
            let interior_at = at / 2;
            let state = at % 2;
            let interior = &self.decoder.interiors[interior_at];
            let native = &self.fibres.native_fibres[at];
            if consequence.address != at as u32
                || consequence.family != interior.family
                || consequence.state != state as u32
                || consequence.port != interior.port
                || consequence.interior_at != interior_at as u32
                || !is_digest(&consequence.consequence_sha256)
                || consequence.incidence_sha256 != interior.incidence_sha256
                || native.native_address != consequence.address
                || native.family != consequence.family
                || native.state != consequence.state
                || native.port != consequence.port
                || native.interior_at != consequence.interior_at
            {
                return Err(MultimodalTransportRefusal::Decoder);
            }
            if state == 1
                && self.decoder.consequences[at - 1].consequence_sha256
                    == consequence.consequence_sha256
            {
                return Err(MultimodalTransportRefusal::Decoder);
            }
        }
        Ok(())
    }

    fn validate_correspondence_fibres(&self) -> Result<(), MultimodalTransportRefusal> {
        if self.fibres.correspondences.len() != self.standing.family_occurrences.len() {
            return Err(MultimodalTransportRefusal::Candidate);
        }
        for (family_at, fibre) in self.fibres.correspondences.iter().enumerate() {
            if fibre.family != family_at as u32
                || fibre.anchor_population == 0
                || fibre.vector_population == 0
                || fibre.raster_four_population == 0
                || fibre.raster_eight_population == 0
            {
                return Err(MultimodalTransportRefusal::Candidate);
            }
            let mut covered = vec![[false; 3]; fibre.anchor_population as usize];
            for (kind, population, pairs) in [
                (0, fibre.vector_population, fibre.text_vector.as_slice()),
                (
                    1,
                    fibre.raster_four_population,
                    fibre.text_raster_four.as_slice(),
                ),
                (
                    2,
                    fibre.raster_eight_population,
                    fibre.text_raster_eight.as_slice(),
                ),
            ] {
                let mut unique = BTreeSet::new();
                for pair in pairs {
                    if pair.anchor >= fibre.anchor_population
                        || pair.member >= population
                        || !unique.insert((pair.anchor, pair.member))
                    {
                        return Err(MultimodalTransportRefusal::Candidate);
                    }
                    covered[pair.anchor as usize][kind] = true;
                }
            }
            if let Some((at, _)) = covered
                .iter()
                .enumerate()
                .find(|(_, ports)| ports.iter().any(|present| !present))
            {
                return Err(MultimodalTransportRefusal::IncompleteJointAnchor(at as u32));
            }
            for unmatched in &fibre.unmatched {
                let valid = match unmatched {
                    UnmatchedMediaMember::Notation(at) => *at < fibre.anchor_population,
                    UnmatchedMediaMember::Vector(at) => *at < fibre.vector_population,
                    UnmatchedMediaMember::RasterFour(at) => *at < fibre.raster_four_population,
                    UnmatchedMediaMember::RasterEight(at) => *at < fibre.raster_eight_population,
                };
                if !valid {
                    return Err(MultimodalTransportRefusal::Candidate);
                }
            }
        }
        let heldout = &self.fibres.correspondences[self.standing.heldout_family as usize];
        if self.standing.heldout_anchor_sections.len() != heldout.anchor_population as usize
            || self
                .standing
                .heldout_anchor_sections
                .iter()
                .enumerate()
                .any(|(at, section)| {
                    section.ordinal != at as u32
                        || section.vector_candidates == 0
                        || section.raster_four_candidates == 0
                        || section.raster_eight_candidates == 0
                        || section.raster_candidates().is_none()
                })
        {
            return Err(MultimodalTransportRefusal::Candidate);
        }
        Ok(())
    }

    fn validate_naturality(&self) -> Result<(), MultimodalTransportRefusal> {
        let ports = self.standing.ports.len();
        if self.fibres.naturality_squares.len() != self.standing.family_occurrences.len() * ports {
            return Err(MultimodalTransportRefusal::Naturality);
        }
        for (at, square) in self.fibres.naturality_squares.iter().enumerate() {
            let family = at / ports;
            let port_at = at % ports;
            let predecessor = at * 2;
            if square.family != family as u32
                || square.port != self.standing.ports[port_at].port
                || square.source_interior_at != at as u32
                || square.native_predecessor != predecessor as u32
                || square.native_successor != predecessor as u32 + 1
                || square.generator_lineage != self.standing.shared.generator_lineage
                || self.decoder.consequences[predecessor].incidence_sha256
                    != self.decoder.consequences[predecessor + 1].incidence_sha256
            {
                return Err(MultimodalTransportRefusal::Naturality);
            }
        }
        Ok(())
    }
}

fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

use holonic_engine::is_sha256_digest as is_digest;
