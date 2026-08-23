use sha2::{Digest, Sha256};

use super::types::{
    AnchorSection, FamilyCorrespondenceFibre, JointMediaDecoder, JointMediaFibres,
    JointMediaStanding, MathematicalMediaPort, MediaNaturalitySquare, MediaPortDeclaration,
    MediaSourceFamily, MediaSourceInterior, NativeMediaConsequence, NativeMediaFibre,
    ProductLineage, SharedMediaContact, SharedMediaSubcomplex, SharedMediaVertex,
    JOINT_MEDIA_DECODER_SCHEMA, JOINT_MEDIA_FIBRES_SCHEMA, JOINT_MEDIA_STANDING_SCHEMA,
};
use super::validation::MultimodalTransportRefusal;
use super::wire::{decode_decoder, encode_decoder};

fn consequence_digest(interior: &MediaSourceInterior, state: u32, generator: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(interior.incidence_sha256.as_bytes());
    hasher.update(state.to_le_bytes());
    hasher.update(generator.as_bytes());
    hasher
        .finalize()
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

fn ports() -> [MathematicalMediaPort; 3] {
    [
        MathematicalMediaPort::Notation,
        MathematicalMediaPort::Vector,
        MathematicalMediaPort::RasterVision,
    ]
}

fn interior(family: &MediaSourceFamily, port: MathematicalMediaPort) -> &MediaSourceInterior {
    match port {
        MathematicalMediaPort::Notation => &family.notation,
        MathematicalMediaPort::Vector => &family.vector,
        MathematicalMediaPort::RasterVision => &family.raster,
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct MultimodalTransportRest {
    pub standing: JointMediaStanding,
    pub decoder: JointMediaDecoder,
    pub fibres: JointMediaFibres,
}

impl MultimodalTransportRest {
    #[allow(clippy::too_many_arguments)]
    pub fn found(
        lineage: ProductLineage,
        mut families: Vec<MediaSourceFamily>,
        heldout_family: u32,
        common_world_receiver: String,
        generator_lineage: String,
        card_heldout_counts: Vec<u32>,
        open_exterior: Vec<String>,
    ) -> Result<Self, MultimodalTransportRefusal> {
        families.sort_by_key(|family| family.family);
        if families.len() < 2
            || families
                .iter()
                .enumerate()
                .any(|(at, family)| family.family != at as u32)
            || heldout_family as usize >= families.len()
            || heldout_family == 0
            || common_world_receiver.is_empty()
            || generator_lineage.is_empty()
        {
            return Err(MultimodalTransportRefusal::Family);
        }

        let port_population = ports().len();
        let mut declarations = Vec::with_capacity(port_population);
        for port in ports() {
            let family_widths = families
                .iter()
                .map(|family| interior(family, port).occurrence_population)
                .collect::<Vec<_>>();
            let mut incidence = Sha256::new();
            for family in &families {
                incidence.update(interior(family, port).incidence_sha256.as_bytes());
            }
            declarations.push(MediaPortDeclaration {
                port,
                boundary: format!("typed-{}-boundary", interior(&families[0], port).chart),
                family_widths,
                incidence: incidence
                    .finalize()
                    .iter()
                    .map(|octet| format!("{octet:02x}"))
                    .collect(),
            });
        }

        let world_address =
            u32::try_from(port_population).map_err(|_| MultimodalTransportRefusal::Extent)?;
        let mut vertices = declarations
            .iter()
            .enumerate()
            .map(|(at, declaration)| SharedMediaVertex {
                address: at as u32,
                port: Some(declaration.port),
                boundary: declaration.boundary.clone(),
            })
            .collect::<Vec<_>>();
        vertices.push(SharedMediaVertex {
            address: world_address,
            port: None,
            boundary: common_world_receiver.clone(),
        });
        let contacts = declarations
            .iter()
            .enumerate()
            .map(|(at, _)| SharedMediaContact {
                address: at as u32,
                from: at as u32,
                to: world_address,
                hand: 1,
            })
            .collect::<Vec<_>>();
        let shared = SharedMediaSubcomplex {
            common_world_receiver,
            generator_lineage: generator_lineage.clone(),
            predecessor: 0,
            successor: 1,
            successor_action: vec![1, 1],
            vertices,
            contacts,
            // M0 explicitly retained the vector/raster direct pair as undeclared. The shared
            // object is therefore a founded cone; the generator squares below are its 2-cells.
            higher_cells: Vec::new(),
        };

        let heldout = &families[heldout_family as usize].correspondences;
        let heldout_anchor_sections = anchor_sections(heldout)?;
        let expected_counts = heldout_anchor_sections
            .iter()
            .flat_map(|section| {
                [
                    1,
                    section.vector_candidates,
                    section.raster_candidates().unwrap_or(0),
                ]
            })
            .collect::<Vec<_>>();
        if expected_counts != card_heldout_counts {
            return Err(MultimodalTransportRefusal::CardCount);
        }

        let family_occurrences = families
            .iter()
            .map(|family| family.occurrence.clone())
            .collect::<Vec<_>>();
        let mut interiors = Vec::with_capacity(families.len() * port_population);
        let mut correspondences = Vec::with_capacity(families.len());
        for family in families {
            interiors.push(family.notation);
            interiors.push(family.vector);
            interiors.push(family.raster);
            correspondences.push(family.correspondences);
        }

        let mut consequences = Vec::with_capacity(interiors.len() * 2);
        let mut native_fibres = Vec::with_capacity(interiors.len() * 2);
        let mut naturality_squares = Vec::with_capacity(interiors.len());
        for family in 0..family_occurrences.len() as u32 {
            for port in ports() {
                let interior_at =
                    family as usize * port_population + port.device_ordinal() as usize;
                let source = &interiors[interior_at];
                let predecessor = consequences.len() as u32;
                for state in 0..2_u32 {
                    let address = consequences.len() as u32;
                    consequences.push(NativeMediaConsequence {
                        address,
                        family,
                        state,
                        port,
                        interior_at: interior_at as u32,
                        consequence_sha256: consequence_digest(source, state, &generator_lineage),
                        incidence_sha256: source.incidence_sha256.clone(),
                    });
                    native_fibres.push(NativeMediaFibre {
                        native_address: address,
                        family,
                        state,
                        port,
                        interior_at: interior_at as u32,
                    });
                }
                naturality_squares.push(MediaNaturalitySquare {
                    family,
                    port,
                    source_interior_at: interior_at as u32,
                    native_predecessor: predecessor,
                    native_successor: predecessor + 1,
                    generator_lineage: generator_lineage.clone(),
                });
            }
        }
        let rest = Self {
            standing: JointMediaStanding {
                schema: JOINT_MEDIA_STANDING_SCHEMA.to_owned(),
                lineage,
                family_occurrences,
                heldout_family,
                ports: declarations,
                shared,
                heldout_anchor_sections,
                open_exterior,
            },
            decoder: JointMediaDecoder {
                schema: JOINT_MEDIA_DECODER_SCHEMA.to_owned(),
                consequences,
                interiors,
            },
            fibres: JointMediaFibres {
                schema: JOINT_MEDIA_FIBRES_SCHEMA.to_owned(),
                correspondences,
                native_fibres,
                naturality_squares,
                open_exterior: vec![
                    "candidate identities can be reopened from their exact source interiors"
                        .to_owned(),
                    "a new chart or receiver reopens the retained ambiguity population".to_owned(),
                ],
            },
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(
        standing: &[u8],
        decoder: &[u8],
        fibres: &[u8],
    ) -> Result<Self, MultimodalTransportRefusal> {
        let rest = Self {
            standing: serde_json::from_slice(standing)
                .map_err(|error| MultimodalTransportRefusal::Wire(error.to_string()))?,
            decoder: decode_decoder(decoder)?,
            fibres: serde_json::from_slice(fibres)
                .map_err(|error| MultimodalTransportRefusal::Wire(error.to_string()))?,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn standing_bytes(&self) -> Result<Vec<u8>, MultimodalTransportRefusal> {
        self.validate()?;
        serde_json::to_vec(&self.standing)
            .map_err(|error| MultimodalTransportRefusal::Wire(error.to_string()))
    }

    pub fn decoder_bytes(&self) -> Result<Vec<u8>, MultimodalTransportRefusal> {
        self.validate()?;
        encode_decoder(&self.decoder)
    }

    pub fn fibre_bytes(&self) -> Result<Vec<u8>, MultimodalTransportRefusal> {
        self.validate()?;
        serde_json::to_vec(&self.fibres)
            .map_err(|error| MultimodalTransportRefusal::Wire(error.to_string()))
    }

    pub fn device_candidate_counts(&self) -> Vec<u32> {
        self.standing
            .heldout_anchor_sections
            .iter()
            .flat_map(|section| {
                [
                    1,
                    section.vector_candidates,
                    section.raster_candidates().unwrap_or(0),
                ]
            })
            .collect()
    }

    pub fn device_decoder_addresses(&self) -> Vec<u32> {
        self.decoder
            .consequences
            .iter()
            .map(|consequence| consequence.address)
            .collect()
    }

    pub fn device_starts(&self) -> Vec<u32> {
        vec![0; self.standing.family_occurrences.len() * self.standing.ports.len()]
    }

    pub fn source_candidate_wire(
        &self,
        family: u32,
    ) -> Result<(Vec<u32>, Vec<u32>), MultimodalTransportRefusal> {
        let fibre = self
            .fibres
            .correspondences
            .get(family as usize)
            .ok_or(MultimodalTransportRefusal::Family)?;
        let mut anchors = (0..fibre.anchor_population).collect::<Vec<_>>();
        let mut ports = vec![MathematicalMediaPort::Notation.device_ordinal(); anchors.len()];
        for pair in &fibre.text_vector {
            anchors.push(pair.anchor);
            ports.push(MathematicalMediaPort::Vector.device_ordinal());
        }
        for pair in fibre
            .text_raster_four
            .iter()
            .chain(&fibre.text_raster_eight)
        {
            anchors.push(pair.anchor);
            ports.push(MathematicalMediaPort::RasterVision.device_ordinal());
        }
        Ok((anchors, ports))
    }

    pub fn reconstruct_interior(
        &self,
        family: u32,
        port: MathematicalMediaPort,
    ) -> Result<&[u8], MultimodalTransportRefusal> {
        let at = family as usize * self.standing.ports.len() + port.device_ordinal() as usize;
        self.decoder
            .interiors
            .get(at)
            .map(|interior| interior.canonical_interior.as_slice())
            .ok_or(MultimodalTransportRefusal::Decoder)
    }
}

fn anchor_sections(
    fibre: &FamilyCorrespondenceFibre,
) -> Result<Vec<AnchorSection>, MultimodalTransportRefusal> {
    let mut counts = vec![[0_u32; 3]; fibre.anchor_population as usize];
    for (kind, pairs) in [
        (0_usize, fibre.text_vector.as_slice()),
        (1, fibre.text_raster_four.as_slice()),
        (2, fibre.text_raster_eight.as_slice()),
    ] {
        for pair in pairs {
            let cell = counts
                .get_mut(pair.anchor as usize)
                .ok_or(MultimodalTransportRefusal::Candidate)?;
            cell[kind] = cell[kind]
                .checked_add(1)
                .ok_or(MultimodalTransportRefusal::Extent)?;
        }
    }
    counts
        .into_iter()
        .enumerate()
        .map(|(ordinal, count)| {
            if count.iter().any(|population| *population == 0) {
                return Err(MultimodalTransportRefusal::IncompleteJointAnchor(
                    ordinal as u32,
                ));
            }
            Ok(AnchorSection {
                ordinal: ordinal as u32,
                vector_candidates: count[0],
                raster_four_candidates: count[1],
                raster_eight_candidates: count[2],
            })
        })
        .collect()
}
