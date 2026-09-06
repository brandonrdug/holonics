//! Actual next-arrival current through a shared tied cross-section, followed by a retained
//! carrier-local contact word. This is a bounded deterministic boundary chart, not the generic
//! definition of learning and not an internal Add teaching its own endogenous output.
//!
//! AUDIT 2026-09-05: retained as an inherited-model numerical experiment, not the native HNA
//! foundation. Prefix joining does not establish contextual applicability; the map word below
//! has no founded context-dependent restriction. See the contextual-transport audit in research.
//!
//! The former source face and the actual next arrived address return through the SAME coefficient
//! map's Euclidean adjoint. Their difference joins the retained latent carrier. A matched
//! self-return deposits nothing. The new map is staged before joining the same session owner.

use super::{
    full_operation::{carrier_of, ContemporaryCarrier},
    operative_reuse::NativeForwardReuse,
    NativeEmissionReadout, NativeFullCycleOutput, NativeFullOperationError as Error,
    NativeFullOperatorEcology, NativeFullOperatorSession, NativeMorphologyTransition,
    NativeOperationPrimitive, NativeOperatorResidence, NativeTensorOrdinal,
};
use crate::resident_section::{Dyadic, DyadicEnclosure, ResidentSection};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeBoundaryFace {
    pub generation: u64,
    pub address: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeBoundaryContactReceipt {
    pub source_generation: u64,
    pub return_generation: u64,
    pub population: NativeTensorOrdinal,
    pub predicted: u32,
    pub arrived: u32,
    pub deposited: bool,
}

pub(super) struct BoundaryContact<'chart> {
    pub(super) source: ContemporaryCarrier<'chart>,
    pub(super) arrived: ContemporaryCarrier<'chart>,
    pub(super) receipt: NativeBoundaryContactReceipt,
}

pub(super) struct BoundaryCultivation<'chart> {
    pub(super) contacts: Vec<BoundaryContact<'chart>>,
    pub(super) last_face: Option<NativeBoundaryFace>,
    pub(super) last_return: Option<NativeBoundaryContactReceipt>,
    /// Ephemeral observer configuration, restored even after a refused native operation.
    pub(super) suppress_return: bool,
}

impl BoundaryCultivation<'_> {
    pub(super) fn empty() -> Self {
        Self {
            contacts: Vec::new(),
            last_face: None,
            last_return: None,
            suppress_return: false,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct NativeBoundaryContactRest {
    pub source: crate::resident_section::ResidentSectionRest,
    pub arrived: crate::resident_section::ResidentSectionRest,
    pub receipt: NativeBoundaryContactReceipt,
}

#[derive(Debug, PartialEq, Eq)]
pub struct NativeBoundaryCultivationRest {
    pub contacts: Vec<NativeBoundaryContactRest>,
    pub last_face: Option<NativeBoundaryFace>,
    pub last_return: Option<NativeBoundaryContactReceipt>,
}

impl<'chart> BoundaryCultivation<'chart> {
    pub(super) fn detach_rest(
        &self,
        surface: &crate::resident_section::ResidentSurface<'chart>,
    ) -> Result<NativeBoundaryCultivationRest, super::NativeSessionRestError> {
        if self.suppress_return {
            return Err(super::NativeSessionRestError::Unsupported(
                "active boundary observation",
            ));
        }
        Ok(NativeBoundaryCultivationRest {
            contacts: self
                .contacts
                .iter()
                .map(|contact| {
                    Ok(NativeBoundaryContactRest {
                        source: surface.detach_section(
                            &contact.source.section,
                            contact.source.bound_octaves,
                        )?,
                        arrived: surface.detach_section(
                            &contact.arrived.section,
                            contact.arrived.bound_octaves,
                        )?,
                        receipt: contact.receipt.clone(),
                    })
                })
                .collect::<Result<Vec<_>, super::NativeSessionRestError>>()?,
            last_face: self.last_face.clone(),
            last_return: self.last_return.clone(),
        })
    }
    pub(super) fn remount_rest(
        surface: &'chart crate::resident_section::ResidentSurface<'chart>,
        rest: &NativeBoundaryCultivationRest,
    ) -> Result<Self, super::NativeSessionRestError> {
        Ok(Self {
            contacts: rest
                .contacts
                .iter()
                .map(|contact| {
                    Ok(BoundaryContact {
                        source: ContemporaryCarrier {
                            section: surface.mount_section_rest(&contact.source)?,
                            bound_octaves: contact.source.bound_octaves,
                        },
                        arrived: ContemporaryCarrier {
                            section: surface.mount_section_rest(&contact.arrived)?,
                            bound_octaves: contact.arrived.bound_octaves,
                        },
                        receipt: contact.receipt.clone(),
                    })
                })
                .collect::<Result<Vec<_>, super::NativeSessionRestError>>()?,
            last_face: rest.last_face.clone(),
            last_return: rest.last_return.clone(),
            suppress_return: false,
        })
    }
}

fn contact_error(message: &'static str) -> Error {
    Error::Contact(message)
}

impl<'residence, 'chart> NativeFullOperatorSession<'residence, 'chart> {
    pub fn found_with_boundary_contact(
        ecology: &'residence NativeFullOperatorEcology,
        residence: &'residence mut NativeOperatorResidence<'chart>,
    ) -> Result<Self, Error> {
        let mut session = Self::found(ecology, residence)?;
        session.boundary_contact_population()?;
        session.boundary_cultivation = Some(BoundaryCultivation::empty());
        session.forward_reuse = Some(NativeForwardReuse::found(ecology));
        Ok(session)
    }

    pub fn has_boundary_contact(&self) -> bool {
        self.boundary_cultivation.is_some()
    }
    pub fn boundary_contact_count(&self) -> usize {
        self.boundary_cultivation
            .as_ref()
            .map_or(0, |s| s.contacts.len())
    }
    pub fn last_boundary_return(&self) -> Option<&NativeBoundaryContactReceipt> {
        self.boundary_cultivation
            .as_ref()
            .and_then(|s| s.last_return.as_ref())
    }

    /// This specialization requires the actual terminal coefficient map to also be an entering
    /// lookup map. Equal widths, names, or an application-provided ordinal do not supply that tie.
    pub(super) fn boundary_contact_population(&self) -> Result<NativeTensorOrdinal, Error> {
        let terminal = self.terminal_operations()?;
        let population = *terminal[0].coefficients.first().ok_or(Error::Operation)?;
        if terminal[0].coefficients.len() != 1
            || !self.ecology.operations.iter().any(|node| {
                matches!(node.primitive, NativeOperationPrimitive::Lookup { .. })
                    && node.coefficients.as_slice() == [population]
            })
        {
            return Err(contact_error(
                "the next-arrival chart requires an actual shared entering/emitting map",
            ));
        }
        if !self.overlay.is_empty() || self.aperture.is_some() || self.passage_cultivation.is_some()
        {
            return Err(contact_error(
                "the boundary chart cannot silently omit another cultivation map's adjoint",
            ));
        }
        Ok(population)
    }

    pub fn observe_boundary_readout_retained(
        &mut self,
        rows: &[u32],
        readout: NativeEmissionReadout,
    ) -> Result<NativeFullCycleOutput, Error> {
        if self.interruption.is_some() {
            return Err(Error::Interrupted);
        }
        let state = self
            .boundary_cultivation
            .as_mut()
            .ok_or(contact_error("no boundary contact chart"))?;
        if state.suppress_return {
            return Err(contact_error("nested boundary observation"));
        }
        state.suppress_return = true;
        let result = self.advance_cycle_readout_retained(rows, readout);
        self.boundary_cultivation
            .as_mut()
            .expect("same owner")
            .suppress_return = false;
        result
    }

    /// Apply the entire learned local word as one resident passage. Earlier immutable contacts
    /// remain shared standing; only the current latent field is replaced. No host field dump
    /// or per-contact launch/readout loop is used.
    pub(super) fn apply_boundary_word(&mut self) -> Result<(), Error> {
        let Some(state) = self.boundary_cultivation.as_ref() else {
            return Ok(());
        };
        if state.contacts.is_empty() {
            return Ok(());
        }
        let port = self.terminal_operations()?[0].inputs[0];
        let input = carrier_of(&self.carriers, &self.checkpoints, &port).ok_or(Error::Carrier)?;
        let surface = self.residence.surface();
        let outputs = state
            .contacts
            .iter()
            .map(|_| {
                surface.fresh_section(
                    input.section.rows(),
                    input.section.width(),
                    input.section.grain(),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let lineage: Vec<Vec<usize>> = (0..2 * outputs.len())
            .map(|at| if at == 0 { vec![] } else { vec![at - 1] })
            .collect();
        let mut passage = surface.begin_passage(&lineage)?;
        for (at, contact) in state.contacts.iter().enumerate() {
            let query = if at == 0 {
                &input.section
            } else {
                &outputs[at - 1]
            };
            let current = 2 * at;
            {
                let lane = passage.open(current, &lineage[current])?;
                surface.record_passive_contact(
                    &lane,
                    &contact.source.section,
                    &contact.arrived.section,
                    query,
                    &outputs[at],
                )?;
            }
            passage.close(current, &outputs[at], 64)?;
            {
                let lane = passage.open(current + 1, &lineage[current + 1])?;
                surface.record_midpoint_seal(&lane, &outputs[at], 64)?;
            }
            passage.close_fused(current + 1)?;
        }
        let reading = passage.finish()?.launch()?;
        if !reading.obstruction.is_empty() {
            return Err(contact_error(
                "the retained boundary word refused its numerical chart",
            ));
        }
        let bound = reading
            .slots
            .last()
            .ok_or(Error::Operation)?
            .max_octave
            .max(1);
        let mut outputs = outputs;
        let changed = ContemporaryCarrier {
            section: outputs.pop().ok_or(Error::Operation)?,
            bound_octaves: bound,
        };
        // The original pre-contact numerical output stays in the existing immutable reuse cache
        // only where that owner retained it. It is not the contemporary post-contact carrier.
        let previous = self
            .carriers
            .remove(&port)
            .or_else(|| self.checkpoints.remove(&port));
        if let (Some(reuse), Some(previous)) = (&mut self.forward_reuse, previous) {
            reuse.retain(port, previous);
        }
        self.carriers.insert(port, changed);
        Ok(())
    }

    pub(super) fn return_boundary_contact(
        &mut self,
        entering: &[u32],
    ) -> Result<NativeMorphologyTransition, Error> {
        let state = self
            .boundary_cultivation
            .as_ref()
            .ok_or(contact_error("no boundary chart"))?;
        if state.suppress_return {
            return Ok(NativeMorphologyTransition::Unchanged);
        }
        let (Some(previous), Some(face)) =
            (self.previous_context.as_ref(), state.last_face.as_ref())
        else {
            return Ok(NativeMorphologyTransition::Unchanged);
        };
        // This addressed-word application presents one actual next arrival. A nonextending word
        // does not invent a matching fibre. It still runs as an ordinary new native occurrence.
        if entering.len() <= previous.len() || entering[..previous.len()] != *previous {
            self.boundary_cultivation
                .as_mut()
                .expect("same owner")
                .last_return = None;
            return Ok(NativeMorphologyTransition::Unchanged);
        }
        if face.generation != self.generation {
            return Err(contact_error("stale boundary face"));
        }
        let population = self.boundary_contact_population()?;
        let arrived = entering[previous.len()];
        let predicted = face.address;
        let mut receipt = NativeBoundaryContactReceipt {
            source_generation: face.generation,
            return_generation: self.generation,
            population,
            predicted,
            arrived,
            deposited: false,
        };
        if predicted != arrived {
            let source = self.terminal_presented.as_ref().ok_or(Error::Carrier)?;
            // A missing selected/arrived row is an obstruction, not the compact intake's zero
            // complement. The shared map must actually carry both compared covectors.
            if self
                .missing_input_rows(&[predicted, arrived])
                .contains_key(&population.0)
            {
                return Err(contact_error(
                    "the compared tied rows have not been supplied",
                ));
            }
            let pair = self.found_boundary_pair(population, predicted, arrived, source)?;
            if let Some((source, arrived)) = pair {
                let state = self.boundary_cultivation.as_mut().expect("same owner");
                state
                    .contacts
                    .try_reserve(1)
                    .map_err(|_| contact_error("cannot retain the returned contact"))?;
                receipt.deposited = true;
                state.contacts.push(BoundaryContact {
                    source,
                    arrived,
                    receipt: receipt.clone(),
                });
            }
        }
        self.boundary_cultivation
            .as_mut()
            .expect("same owner")
            .last_return = Some(receipt.clone());
        Ok(NativeMorphologyTransition::BoundaryContact { returned: receipt })
    }

    fn found_boundary_pair(
        &self,
        population: NativeTensorOrdinal,
        predicted: u32,
        arrived: u32,
        source: &ContemporaryCarrier<'chart>,
    ) -> Result<Option<(ContemporaryCarrier<'chart>, ContemporaryCarrier<'chart>)>, Error> {
        let selected = self
            .residence
            .gather_rows(population, &[predicted, arrived])?;
        if selected.width != source.section.width() {
            return Err(Error::Operation);
        }
        let surface = self.residence.surface();
        let grain = source.section.grain();
        let width = source.section.width();
        let fields = (0..6)
            .map(|_| surface.fresh_section(1, width, grain))
            .collect::<Result<Vec<_>, _>>()?;
        let entering = surface.shape_enter_resident_bfloat16(
            1,
            width,
            Dyadic::ONE,
            grain,
            selected.frame.exponent,
            selected.entry_octaves,
        )?;
        let negative = DyadicEnclosure {
            lo: -1,
            hi: -1,
            grain: 0,
        };
        let negative_shape = surface.shape_scale(1, width, entering.needed, negative)?;
        let current_shape =
            surface.shape_re_entry(1, width, entering.needed, negative_shape.needed)?;
        let joined_shape =
            surface.shape_re_entry(1, width, source.bound_octaves, current_shape.needed)?;
        let lineage = [vec![], vec![], vec![], vec![0], vec![1, 3], vec![2, 4]];
        let bounds = [
            entering.needed,
            entering.needed,
            source.bound_octaves,
            negative_shape.needed,
            current_shape.needed,
            joined_shape.needed,
        ];
        let mut passage = surface.begin_passage(&lineage)?;
        for at in 0..6 {
            {
                let lane = passage.open(at, &lineage[at])?;
                match at {
                    0 | 1 => surface.record_enter_resident_bfloat16(
                        &lane,
                        selected.address + (at * width * 2) as u64,
                        1,
                        width,
                        Dyadic::ONE,
                        &fields[at],
                    )?,
                    2 => surface.record_terminal_row(&lane, &source.section, &fields[at])?,
                    3 => surface.record_scale(&lane, &fields[0], negative, &fields[at])?,
                    4 => surface.record_re_entry(&lane, &fields[1], &fields[3], &fields[at])?,
                    5 => surface.record_re_entry(&lane, &fields[2], &fields[4], &fields[at])?,
                    _ => unreachable!(),
                }
            }
            passage.close(at, &fields[at], bounds[at])?;
        }
        let reading = passage.finish()?.launch()?;
        if !reading.obstruction.is_empty() {
            return Err(contact_error(
                "the actual next-arrival current refused its chart",
            ));
        }
        if reading.slots[4].max_octave == 0 {
            return Ok(None);
        }
        let mut fields: Vec<Option<ResidentSection<'chart>>> =
            fields.into_iter().map(Some).collect();
        Ok(Some((
            ContemporaryCarrier {
                section: fields[2].take().expect("source"),
                bound_octaves: reading.slots[2].max_octave.max(1),
            },
            ContemporaryCarrier {
                section: fields[5].take().expect("arrived"),
                bound_octaves: reading.slots[5].max_octave.max(1),
            },
        )))
    }
}
