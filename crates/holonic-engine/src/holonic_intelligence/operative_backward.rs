//! The return through the body: SKE1's driver.
//!
//! After the tied-boundary return has formed the differential at the tied contraction's output,
//! this owner carries it back through every operation of the cycle in reverse graph order.  The
//! forward retained every cross-layer carrier as a checkpoint; each layer is replayed from its
//! checkpoints on the card, then walked in reverse: every operation takes the accumulated
//! differential of its output, returns one through each input by its own adjoint law, and every
//! contraction deposits one factorized overlay atom on its cross-section.  Differentials meeting
//! at one carrier accumulate by re-entry.  The support of every returned differential is read out
//! as testimony: for dissection it is the cone; for cultivation the deposits are the change.

use std::collections::BTreeMap;

use serde::Serialize;

use crate::resident_section::{Dyadic, ResidentGrain, ResidentSection, SeriesAperture};

use super::{
    NativeCarrierOrdinal, NativeCausalReach, NativeFullOperationError,
    NativeFullOperationOccurrence, NativeFullOperatorSession, NativeMorphologyDeposit,
    NativeOperationPrimitive, NativeOperatorNode, NativeReturnAperture, NativeScaleConstraint,
    NativeTensorOrdinal, adjoint_contract, differential_support,
    full_operation::{ContemporaryCarrier, binary64_projection, operation_bound, scale_enclosure},
    operative_adjoint::deposit_on_cross_section,
    operative_return::ReturnedDifferential,
};

/// The support of the differential returned to one operation's output.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeAdjointOperationSupport {
    pub operation: u32,
    pub layer: Option<u16>,
    pub rows: usize,
    pub width: usize,
    pub bound_octaves: u32,
    pub nonzero_coordinates: usize,
    pub widest_interval: u64,
}

/// The embedding rows a lookup's differential reached: the cone at the lookup population.  The
/// deposit on those rows is not yet enacted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeLookupReach {
    pub operation: u32,
    pub population: u32,
    pub row_addresses: Vec<u32>,
    pub nonzero_coordinates: usize,
}

/// The complete testimony of one return through the body.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeAdjointReturnTrace {
    pub operations_returned: usize,
    pub layers_replayed: usize,
    pub deposits: Vec<NativeMorphologyDeposit>,
    pub populations_deposited: Vec<u32>,
    pub supports: Vec<NativeAdjointOperationSupport>,
    pub lookups_reached: Vec<NativeLookupReach>,
    pub elapsed_milliseconds: u128,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Segment {
    Prologue,
    Layer(u16),
    Epilogue,
}

impl<'residence, 'chart> NativeFullOperatorSession<'residence, 'chart> {
    /// Carry the returned differential through the body and deposit on every cross-section.
    pub(super) fn adjoint_return(
        &mut self,
        differential: ReturnedDifferential<'chart>,
        aperture: NativeReturnAperture,
    ) -> Result<NativeAdjointReturnTrace, NativeFullOperationError> {
        let started = std::time::Instant::now();
        let operations = self.ecology.operations.len();
        let terminal_start = operations
            .checked_sub(5)
            .ok_or(NativeFullOperationError::Operation)?;
        let first_layer_operation = self
            .ecology
            .operations
            .iter()
            .position(|operation| operation.layer.is_some())
            .ok_or(NativeFullOperationError::Operation)?;
        let tied = self.ecology.operations[terminal_start].clone();
        let tied_population = *tied
            .coefficients
            .first()
            .ok_or(NativeFullOperationError::Operation)?;
        let mut adjoint: BTreeMap<NativeCarrierOrdinal, ContemporaryCarrier<'chart>> =
            BTreeMap::new();
        let mut trace = NativeAdjointReturnTrace {
            operations_returned: 0,
            layers_replayed: 0,
            deposits: Vec::new(),
            populations_deposited: Vec::new(),
            supports: Vec::new(),
            lookups_reached: Vec::new(),
            elapsed_milliseconds: 0,
        };
        // The tied contraction: its deposit was enacted with the differential; here it returns.
        let returned = adjoint_contract(
            self.residence,
            tied_population,
            &differential.section,
            differential.octaves,
        )
        .map_err(|error| NativeFullOperationError::Adjoint(error.to_string()))?;
        trace.supports.push(self.support_of(&tied, &differential.section, differential.octaves)?);
        drop(differential);
        let sealed = self.seal_returned(
            ContemporaryCarrier {
                section: returned.section,
                bound_octaves: returned.bound_octaves,
            },
            tied.ordinal,
        )?;
        adjoint.insert(tied.inputs[0], sealed);
        trace.operations_returned += 1;
        let mut replayed: Option<Segment> = None;
        for index in (0..terminal_start).rev() {
            let operation = self.ecology.operations[index].clone();
            let segment = match operation.layer {
                Some(layer) => Segment::Layer(layer),
                None if index < first_layer_operation => Segment::Prologue,
                None => Segment::Epilogue,
            };
            let Some(dy) = adjoint.remove(&operation.output) else {
                continue;
            };
            if segment != Segment::Epilogue && replayed != Some(segment) {
                self.replay(segment, first_layer_operation, terminal_start)?;
                replayed = Some(segment);
                trace.layers_replayed += 1;
            }
            trace.supports.push(self.support_of(&operation, &dy.section, dy.bound_octaves)?);
            let dy_octaves = dy.bound_octaves;
            self.return_through(&operation, dy, &mut adjoint, aperture, &mut trace)
                .map_err(|error| {
                    let recent: Vec<String> = trace
                        .supports
                        .iter()
                        .rev()
                        .take(6)
                        .map(|support| {
                            format!(
                                "op {} layer {:?} {}x{} bound {} nonzero {} widest {}",
                                support.operation,
                                support.layer,
                                support.rows,
                                support.width,
                                support.bound_octaves,
                                support.nonzero_coordinates,
                                support.widest_interval
                            )
                        })
                        .collect();
                    NativeFullOperationError::Adjoint(format!(
                        "operation {} ({:?}) with a differential of {} octaves: {error}; recent returns: {}",
                        operation.ordinal,
                        operation.primitive,
                        dy_octaves,
                        recent.join(" | ")
                    ))
                })?;
            trace.operations_returned += 1;
        }
        self.carriers.clear();
        trace.elapsed_milliseconds = started.elapsed().as_millis();
        Ok(trace)
    }

    fn support_of(
        &self,
        operation: &NativeOperatorNode,
        section: &ResidentSection<'chart>,
        bound_octaves: u32,
    ) -> Result<NativeAdjointOperationSupport, NativeFullOperationError> {
        let intervals = self.residence.surface().read_out(section)?;
        let support = differential_support(section.rows(), section.width(), &intervals);
        Ok(NativeAdjointOperationSupport {
            operation: operation.ordinal,
            layer: operation.layer,
            rows: section.rows(),
            width: section.width(),
            bound_octaves,
            nonzero_coordinates: support.nonzero_coordinates,
            widest_interval: support.widest_interval,
        })
    }

    /// Replay one segment forward from its checkpoints, keeping every produced carrier.
    fn replay(
        &mut self,
        segment: Segment,
        first_layer_operation: usize,
        terminal_start: usize,
    ) -> Result<(), NativeFullOperationError> {
        self.carriers.clear();
        let rows = self
            .previous_context
            .clone()
            .ok_or(NativeFullOperationError::Occurrence)?;
        let ordinals: Vec<usize> = (0..terminal_start)
            .filter(|index| {
                let operation = &self.ecology.operations[*index];
                match segment {
                    Segment::Prologue => *index < first_layer_operation,
                    Segment::Layer(layer) => operation.layer == Some(layer),
                    Segment::Epilogue => false,
                }
            })
            .collect();
        for index in ordinals {
            let operation = self.ecology.operations[index].clone();
            let occurrence = NativeFullOperationOccurrence {
                ordinal: 0,
                row_addresses: if matches!(operation.primitive, NativeOperationPrimitive::Lookup { .. }) {
                    rows.clone()
                } else {
                    Vec::new()
                },
            };
            let outcome = self.enact_operation(&operation, &occurrence)?;
            self.carriers.insert(
                operation.output,
                ContemporaryCarrier {
                    section: outcome.section,
                    bound_octaves: outcome.bound_octaves,
                },
            );
        }
        Ok(())
    }

    fn presented(
        &self,
        carrier: NativeCarrierOrdinal,
    ) -> Result<&ContemporaryCarrier<'chart>, NativeFullOperationError> {
        self.carriers
            .get(&carrier)
            .or_else(|| self.checkpoints.get(&carrier))
            .ok_or(NativeFullOperationError::Carrier)
    }

    /// The declared successor projection of the forward, applied to a returned differential: an
    /// open enclosure is sealed to its midpoint under its own census, so the return does not
    /// carry the wrapping of every earlier enclosure into the next.  The width it collapsed is
    /// already in the support testimony.
    fn seal_returned(
        &self,
        returned: ContemporaryCarrier<'chart>,
        operation: u32,
    ) -> Result<ContemporaryCarrier<'chart>, NativeFullOperationError> {
        let surface = self.residence.surface();
        let mut builder = surface.begin_passage(&[vec![]])?;
        {
            let lane = builder.open(0, &[])?;
            surface.record_midpoint_seal(&lane, &returned.section, returned.bound_octaves)?;
        }
        builder.close_fused(0)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(operation, &reading)?;
        Ok(ContemporaryCarrier {
            section: returned.section,
            bound_octaves,
        })
    }

    fn accumulate(
        &self,
        adjoint: &mut BTreeMap<NativeCarrierOrdinal, ContemporaryCarrier<'chart>>,
        carrier: NativeCarrierOrdinal,
        returned: ContemporaryCarrier<'chart>,
        operation: u32,
    ) -> Result<(), NativeFullOperationError> {
        let returned = self.seal_returned(returned, operation)?;
        let Some(held) = adjoint.remove(&carrier) else {
            adjoint.insert(carrier, returned);
            return Ok(());
        };
        let surface = self.residence.surface();
        if held.section.rows() != returned.section.rows()
            || held.section.width() != returned.section.width()
        {
            return Err(NativeFullOperationError::Adjoint(format!(
                "differentials meeting at carrier {} disagree in shape",
                carrier.0
            )));
        }
        let shape = surface.shape_re_entry(
            held.section.rows(),
            held.section.width(),
            held.bound_octaves,
            returned.bound_octaves,
        )?;
        let joined = surface.fresh_section(
            held.section.rows(),
            held.section.width(),
            held.section.grain(),
        )?;
        let mut builder = surface.begin_passage(&[vec![]])?;
        {
            let lane = builder.open(0, &[])?;
            surface.record_re_entry(&lane, &held.section, &returned.section, &joined)?;
        }
        builder.close(0, &joined, shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(operation, &reading)?;
        adjoint.insert(
            carrier,
            ContemporaryCarrier {
                section: joined,
                bound_octaves,
            },
        );
        Ok(())
    }

    /// Return the differential of one operation's output through each of its inputs.
    fn return_through(
        &mut self,
        operation: &NativeOperatorNode,
        dy: ContemporaryCarrier<'chart>,
        adjoint: &mut BTreeMap<NativeCarrierOrdinal, ContemporaryCarrier<'chart>>,
        aperture: NativeReturnAperture,
        trace: &mut NativeAdjointReturnTrace,
    ) -> Result<(), NativeFullOperationError> {
        let ordinal = operation.ordinal;
        match &operation.primitive {
            NativeOperationPrimitive::Lookup { .. } => {
                let intervals = self.residence.surface().read_out(&dy.section)?;
                let support = differential_support(dy.section.rows(), dy.section.width(), &intervals);
                trace.lookups_reached.push(NativeLookupReach {
                    operation: ordinal,
                    population: operation.coefficients.first().map(|c| c.0).unwrap_or(u32::MAX),
                    row_addresses: self.previous_context.clone().unwrap_or_default(),
                    nonzero_coordinates: support.nonzero_coordinates,
                });
                Ok(())
            }
            NativeOperationPrimitive::Reshape | NativeOperationPrimitive::Emit => {
                let input = operation.inputs[0];
                let (rows, width) = {
                    let presented = self.presented(input)?;
                    (presented.section.rows(), presented.section.width())
                };
                let returned = self.adjoint_carry(&dy, rows, width, ordinal)?;
                self.accumulate(adjoint, input, returned, ordinal)
            }
            NativeOperationPrimitive::Select { axis, at } => {
                if *axis != 1 {
                    return Err(NativeFullOperationError::Operation);
                }
                let input = operation.inputs[0];
                let width = self.presented(input)?.section.width();
                let span = dy.section.width();
                let returned = self.adjoint_select(&dy, at * span, width, ordinal)?;
                self.accumulate(adjoint, input, returned, ordinal)
            }
            NativeOperationPrimitive::Contract => {
                let input = operation.inputs[0];
                let population = operation.coefficients[0];
                let (deposit, returned) = {
                    let presented = self.presented(input)?;
                    let surface = self.residence.surface();
                    let (atom, mut deposit) = deposit_on_cross_section(
                        surface,
                        &dy.section,
                        dy.bound_octaves,
                        &presented.section,
                        presented.bound_octaves,
                        self.grain,
                        aperture,
                    )?;
                    deposit.population = population.0;
                    let returned = adjoint_contract(
                        self.residence,
                        population,
                        &dy.section,
                        dy.bound_octaves,
                    )
                    .map_err(|error| NativeFullOperationError::Adjoint(error.to_string()))?;
                    self.overlay.entry(population).or_default().push(atom);
                    (
                        deposit,
                        ContemporaryCarrier {
                            section: returned.section,
                            bound_octaves: returned.bound_octaves,
                        },
                    )
                };
                trace.deposits.push(deposit);
                if !trace.populations_deposited.contains(&population.0) {
                    trace.populations_deposited.push(population.0);
                }
                self.accumulate(adjoint, input, returned, ordinal)
            }
            NativeOperationPrimitive::RmsRebase {
                group,
                epsilon,
                has_gain,
            } => {
                let input = operation.inputs[0];
                let returned = self.adjoint_rms(
                    &dy,
                    input,
                    *group,
                    epsilon,
                    if *has_gain {
                        Some(operation.coefficients[0])
                    } else {
                        None
                    },
                    ordinal,
                )?;
                self.accumulate(adjoint, input, returned, ordinal)
            }
            NativeOperationPrimitive::GeluTanh => {
                let input = operation.inputs[0];
                let returned = self.adjoint_gelu(&dy, input, ordinal)?;
                self.accumulate(adjoint, input, returned, ordinal)
            }
            NativeOperationPrimitive::Tanh => {
                let input = operation.inputs[0];
                let returned = self.adjoint_tanh(&dy, operation.output, ordinal)?;
                self.accumulate(adjoint, input, returned, ordinal)
            }
            NativeOperationPrimitive::Hadamard => {
                let (left, right) = (operation.inputs[0], operation.inputs[1]);
                let to_left = self.adjoint_hadamard(&dy, right, ordinal)?;
                let to_right = self.adjoint_hadamard(&dy, left, ordinal)?;
                self.accumulate(adjoint, left, to_left, ordinal)?;
                self.accumulate(adjoint, right, to_right, ordinal)
            }
            NativeOperationPrimitive::Add => {
                let (left, right) = (operation.inputs[0], operation.inputs[1]);
                let copy = self.adjoint_carry(&dy, dy.section.rows(), dy.section.width(), ordinal)?;
                self.accumulate(adjoint, left, dy, ordinal)?;
                self.accumulate(adjoint, right, copy, ordinal)
            }
            NativeOperationPrimitive::Scale { by } => {
                let input = operation.inputs[0];
                let returned = match by {
                    NativeScaleConstraint::Coefficient => {
                        self.adjoint_coefficient_scale(&dy, operation.coefficients[0], ordinal)?
                    }
                    other => self.adjoint_scale(&dy, other, ordinal)?,
                };
                self.accumulate(adjoint, input, returned, ordinal)
            }
            NativeOperationPrimitive::RotaryChronology {
                theta,
                head_width,
                rotated_width,
            } => {
                let input = operation.inputs[0];
                let returned =
                    self.adjoint_chronology(&dy, *theta, *head_width, *rotated_width, ordinal)?;
                self.accumulate(adjoint, input, returned, ordinal)
            }
            NativeOperationPrimitive::CausalContact {
                heads,
                kv_heads,
                head_width,
                reach,
                series_terms,
            } => {
                let (q, k, v) = (operation.inputs[0], operation.inputs[1], operation.inputs[2]);
                let (dq, dk, dv) = self.adjoint_contact(
                    &dy,
                    q,
                    k,
                    v,
                    *heads,
                    *kv_heads,
                    *head_width,
                    reach,
                    *series_terms,
                    ordinal,
                )?;
                self.accumulate(adjoint, q, dq, ordinal)?;
                self.accumulate(adjoint, k, dk, ordinal)?;
                self.accumulate(adjoint, v, dv, ordinal)
            }
        }
    }

    fn launch_one<F>(
        &self,
        rows: usize,
        width: usize,
        grain: ResidentGrain,
        needed: u32,
        ordinal: u32,
        record: F,
    ) -> Result<ContemporaryCarrier<'chart>, NativeFullOperationError>
    where
        F: FnOnce(
            &crate::resident_section::Lane<'_, 'chart>,
            &ResidentSection<'chart>,
        ) -> Result<(), crate::resident_section::ResidentRefusal>,
    {
        let surface = self.residence.surface();
        let out = surface.fresh_section(rows, width, grain)?;
        let mut builder = surface.begin_passage(&[vec![]])?;
        {
            let lane = builder.open(0, &[])?;
            record(&lane, &out)?;
        }
        builder.close(0, &out, needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(ordinal, &reading)?;
        Ok(ContemporaryCarrier {
            section: out,
            bound_octaves,
        })
    }

    fn adjoint_carry(
        &self,
        dy: &ContemporaryCarrier<'chart>,
        rows: usize,
        width: usize,
        ordinal: u32,
    ) -> Result<ContemporaryCarrier<'chart>, NativeFullOperationError> {
        if rows * width != dy.section.rows() * dy.section.width() {
            return Err(NativeFullOperationError::Operation);
        }
        let surface = self.residence.surface();
        let shape = surface.shape_carry(rows, width, dy.bound_octaves)?;
        // The carry copies the flat words; a reshape is a relabeling of the same population.
        let flat = surface.fresh_section(rows, width, dy.section.grain())?;
        let mut builder = surface.begin_passage(&[vec![]])?;
        {
            let lane = builder.open(0, &[])?;
            surface.record_carry_flat(&lane, &dy.section, &flat)?;
        }
        builder.close(0, &flat, shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(ordinal, &reading)?;
        Ok(ContemporaryCarrier {
            section: flat,
            bound_octaves,
        })
    }

    fn adjoint_select(
        &self,
        dy: &ContemporaryCarrier<'chart>,
        at: usize,
        width: usize,
        ordinal: u32,
    ) -> Result<ContemporaryCarrier<'chart>, NativeFullOperationError> {
        let surface = self.residence.surface();
        let shape = surface.shape_place_columns(
            dy.section.rows(),
            dy.section.width(),
            width,
            at,
            dy.bound_octaves,
        )?;
        self.launch_one(dy.section.rows(), width, dy.section.grain(), shape.needed, ordinal, |lane, out| {
            surface.record_place_columns(lane, &dy.section, at, out)
        })
    }

    fn adjoint_scale(
        &self,
        dy: &ContemporaryCarrier<'chart>,
        by: &NativeScaleConstraint,
        ordinal: u32,
    ) -> Result<ContemporaryCarrier<'chart>, NativeFullOperationError> {
        let surface = self.residence.surface();
        let enclosure = scale_enclosure(by)?;
        let shape = surface.shape_scale(
            dy.section.rows(),
            dy.section.width(),
            dy.bound_octaves,
            enclosure,
        )?;
        self.launch_one(
            dy.section.rows(),
            dy.section.width(),
            dy.section.grain(),
            shape.needed,
            ordinal,
            |lane, out| surface.record_scale(lane, &dy.section, enclosure, out),
        )
    }

    fn adjoint_coefficient_scale(
        &mut self,
        dy: &ContemporaryCarrier<'chart>,
        coefficient: NativeTensorOrdinal,
        ordinal: u32,
    ) -> Result<ContemporaryCarrier<'chart>, NativeFullOperationError> {
        let surface = self.residence.surface();
        let tile = self.residence.align_tile(coefficient, 0, 1)?;
        let shape = surface.shape_scale_by_aligned(
            dy.section.rows(),
            dy.section.width(),
            dy.bound_octaves,
            &tile.mounted.readout,
        )?;
        let out = surface.fresh_section(dy.section.rows(), dy.section.width(), dy.section.grain())?;
        let mut builder = surface.begin_passage(&[vec![]])?;
        {
            let lane = builder.open(0, &[])?;
            surface.record_scale_by_aligned(&lane, &dy.section, &tile.mounted.readout, &out)?;
        }
        builder.close(0, &out, shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(ordinal, &reading)?;
        drop(tile);
        Ok(ContemporaryCarrier {
            section: out,
            bound_octaves,
        })
    }

    fn adjoint_hadamard(
        &self,
        dy: &ContemporaryCarrier<'chart>,
        other: NativeCarrierOrdinal,
        ordinal: u32,
    ) -> Result<ContemporaryCarrier<'chart>, NativeFullOperationError> {
        let other = self.presented(other)?;
        let surface = self.residence.surface();
        let shape = surface.shape_hadamard(
            dy.section.rows(),
            dy.section.width(),
            dy.bound_octaves,
            other.bound_octaves,
        )?;
        self.launch_one(
            dy.section.rows(),
            dy.section.width(),
            dy.section.grain(),
            shape.needed,
            ordinal,
            |lane, out| surface.record_hadamard(lane, &dy.section, &other.section, out),
        )
    }

    fn adjoint_tanh(
        &self,
        dy: &ContemporaryCarrier<'chart>,
        reacted: NativeCarrierOrdinal,
        ordinal: u32,
    ) -> Result<ContemporaryCarrier<'chart>, NativeFullOperationError> {
        let reacted = self.presented(reacted)?;
        let surface = self.residence.surface();
        let factor_shape = surface.shape_one_minus_square(
            reacted.section.rows(),
            reacted.section.width(),
            reacted.bound_octaves,
            reacted.section.grain(),
        )?;
        let factor = surface.fresh_section(
            reacted.section.rows(),
            reacted.section.width(),
            reacted.section.grain(),
        )?;
        // The factor is at most one in value: its words carry the grain plus the hand.
        let product_shape = surface.shape_hadamard(
            dy.section.rows(),
            dy.section.width(),
            dy.bound_octaves,
            reacted.section.grain().0 + 2,
        )?;
        let out = surface.fresh_section(dy.section.rows(), dy.section.width(), dy.section.grain())?;
        let mut builder = surface.begin_passage(&[vec![], vec![0]])?;
        {
            let lane = builder.open(0, &[])?;
            surface.record_one_minus_square(&lane, &reacted.section, &factor)?;
        }
        builder.close(0, &factor, factor_shape.needed)?;
        {
            let lane = builder.open(1, &[0])?;
            surface.record_hadamard(&lane, &dy.section, &factor, &out)?;
        }
        builder.close(1, &out, product_shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(ordinal, &reading)?;
        Ok(ContemporaryCarrier {
            section: out,
            bound_octaves,
        })
    }

    fn adjoint_gelu(
        &self,
        dy: &ContemporaryCarrier<'chart>,
        presented: NativeCarrierOrdinal,
        ordinal: u32,
    ) -> Result<ContemporaryCarrier<'chart>, NativeFullOperationError> {
        let presented = self.presented(presented)?;
        let surface = self.residence.surface();
        let c1 = Dyadic::of_binary64_bits(0x3fe9_8845_33d4_3651)?;
        let c2 = Dyadic::of_binary64_bits(0x3fa6_e4e2_6d48_01f7)?;
        let terms = SeriesAperture(14);
        let factor_shape = surface.shape_gelu_tanh_derivative(
            presented.section.rows(),
            presented.section.width(),
            presented.bound_octaves,
            presented.section.grain(),
            c1,
            c2,
            terms,
        )?;
        let factor = surface.fresh_section(
            presented.section.rows(),
            presented.section.width(),
            presented.section.grain(),
        )?;
        // The derivative is below two in value: its words carry the grain plus two hands.
        let product_shape = surface.shape_hadamard(
            dy.section.rows(),
            dy.section.width(),
            dy.bound_octaves,
            presented.section.grain().0 + 3,
        )?;
        let out = surface.fresh_section(dy.section.rows(), dy.section.width(), dy.section.grain())?;
        let mut builder = surface.begin_passage(&[vec![], vec![0]])?;
        {
            let lane = builder.open(0, &[])?;
            surface.record_gelu_tanh_derivative(&lane, &presented.section, c1, c2, terms, &factor)?;
        }
        builder.close(0, &factor, factor_shape.needed)?;
        {
            let lane = builder.open(1, &[0])?;
            surface.record_hadamard(&lane, &dy.section, &factor, &out)?;
        }
        builder.close(1, &out, product_shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(ordinal, &reading)?;
        Ok(ContemporaryCarrier {
            section: out,
            bound_octaves,
        })
    }

    fn adjoint_rms(
        &mut self,
        dy: &ContemporaryCarrier<'chart>,
        presented: NativeCarrierOrdinal,
        group: usize,
        epsilon: &relational_geometry::Rat,
        gain: Option<NativeTensorOrdinal>,
        ordinal: u32,
    ) -> Result<ContemporaryCarrier<'chart>, NativeFullOperationError> {
        let surface = self.residence.surface();
        let tile = match gain {
            Some(gain) => Some(self.residence.align_tile(gain, 0, 1)?),
            None => None,
        };
        let readout = tile.as_ref().map(|tile| &tile.mounted.readout);
        let presented = self
            .carriers
            .get(&presented)
            .or_else(|| self.checkpoints.get(&presented))
            .ok_or(NativeFullOperationError::Carrier)?;
        let shape = surface.shape_rms_rebase_adjoint(
            presented.section.rows(),
            presented.section.width(),
            group,
            presented.bound_octaves,
            dy.bound_octaves,
            readout,
        )?;
        let eps = binary64_projection(epsilon)?;
        let out = surface.fresh_section(
            presented.section.rows(),
            presented.section.width(),
            presented.section.grain(),
        )?;
        let mut builder = surface.begin_passage(&[vec![]])?;
        {
            let lane = builder.open(0, &[])?;
            surface.record_rms_rebase_adjoint(
                &lane,
                &presented.section,
                &dy.section,
                group,
                readout,
                eps,
                &shape,
                &out,
            )?;
        }
        builder.close(0, &out, shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(ordinal, &reading)?;
        drop(tile);
        Ok(ContemporaryCarrier {
            section: out,
            bound_octaves,
        })
    }

    fn adjoint_chronology(
        &self,
        dy: &ContemporaryCarrier<'chart>,
        theta: u64,
        head_width: usize,
        rotated_width: usize,
        ordinal: u32,
    ) -> Result<ContemporaryCarrier<'chart>, NativeFullOperationError> {
        if dy.section.width() % head_width != 0 {
            return Err(NativeFullOperationError::Operation);
        }
        let heads = dy.section.width() / head_width;
        let positions = self
            .positions
            .as_ref()
            .ok_or(NativeFullOperationError::Occurrence)?;
        let bands = self.residence.chronology(theta, head_width, rotated_width)?;
        let surface = self.residence.surface();
        let shape = surface.shape_chronology(
            dy.section.rows(),
            dy.section.width(),
            heads,
            head_width,
            dy.bound_octaves,
            bands,
            positions,
            u32::try_from(dy.section.rows().saturating_sub(1))
                .map_err(|_| NativeFullOperationError::Operation)?,
        )?;
        self.launch_one(
            dy.section.rows(),
            dy.section.width(),
            dy.section.grain(),
            shape.needed,
            ordinal,
            |lane, out| {
                surface.record_chronology_adjoint(
                    lane,
                    &dy.section,
                    heads,
                    head_width,
                    bands,
                    positions,
                    out,
                )
            },
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn adjoint_contact(
        &self,
        dy: &ContemporaryCarrier<'chart>,
        q: NativeCarrierOrdinal,
        k: NativeCarrierOrdinal,
        v: NativeCarrierOrdinal,
        heads: usize,
        kv_heads: usize,
        head_width: usize,
        reach: &NativeCausalReach,
        series_terms: u32,
        ordinal: u32,
    ) -> Result<
        (
            ContemporaryCarrier<'chart>,
            ContemporaryCarrier<'chart>,
            ContemporaryCarrier<'chart>,
        ),
        NativeFullOperationError,
    > {
        let q = self.presented(q)?;
        let k = self.presented(k)?;
        let v = self.presented(v)?;
        let rows = q.section.rows();
        let window = match reach {
            NativeCausalReach::Window(window) if *window > 0 => *window,
            NativeCausalReach::Complete => rows,
            _ => return Err(NativeFullOperationError::Operation),
        };
        let terms = SeriesAperture(series_terms);
        let grain = q.section.grain();
        let surface = self.residence.surface();
        let queries = surface.shape_contact_adjoint_queries(
            rows,
            heads,
            kv_heads,
            head_width,
            window,
            terms,
            grain,
            q.bound_octaves,
            k.bound_octaves,
            v.bound_octaves,
            dy.bound_octaves,
        )?;
        let keys = surface.shape_contact_adjoint_family(
            rows,
            heads,
            kv_heads,
            head_width,
            window,
            grain,
            queries.needed,
            q.bound_octaves,
        )?;
        let values = surface.shape_contact_adjoint_family(
            rows,
            heads,
            kv_heads,
            head_width,
            window,
            grain,
            grain.0 + 1,
            dy.bound_octaves,
        )?;
        let reach_max = rows.min(window.max(1));
        let dq = surface.fresh_section(rows, heads * head_width, grain)?;
        let dk = surface.fresh_section(rows, kv_heads * head_width, grain)?;
        let dv = surface.fresh_section(rows, kv_heads * head_width, grain)?;
        let weights = surface.fresh_section(rows * heads, reach_max, grain)?;
        let differentials = surface.fresh_section(rows * heads, reach_max, grain)?;
        let mut builder = surface.begin_passage(&[vec![], vec![0], vec![0]])?;
        {
            let lane = builder.open(0, &[])?;
            surface.record_contact_adjoint_queries(
                &lane,
                &q.section,
                &k.section,
                &v.section,
                &dy.section,
                heads,
                kv_heads,
                head_width,
                window,
                terms,
                &queries,
                &dq,
                &weights,
                &differentials,
            )?;
        }
        builder.close(0, &dq, queries.needed)?;
        {
            let lane = builder.open(1, &[0])?;
            surface.record_contact_adjoint_family(
                &lane,
                &q.section,
                &differentials,
                heads,
                kv_heads,
                head_width,
                window,
                false,
                &dk,
            )?;
        }
        builder.close(1, &dk, keys.needed)?;
        {
            let lane = builder.open(2, &[0])?;
            surface.record_contact_adjoint_family(
                &lane,
                &dy.section,
                &weights,
                heads,
                kv_heads,
                head_width,
                window,
                true,
                &dv,
            )?;
        }
        builder.close(2, &dv, values.needed)?;
        let reading = builder.finish()?.launch()?;
        if !reading.obstruction.is_empty() {
            return Err(NativeFullOperationError::ResidentObstruction {
                operation: ordinal,
                flags: reading.obstruction.joined_flags(),
            });
        }
        let bound = |index: usize| {
            reading
                .slots
                .get(index)
                .map(|slot| slot.max_octave.max(1))
                .unwrap_or(1)
        };
        Ok((
            ContemporaryCarrier {
                section: dq,
                bound_octaves: bound(0),
            },
            ContemporaryCarrier {
                section: dk,
                bound_octaves: bound(1),
            },
            ContemporaryCarrier {
                section: dv,
                bound_octaves: bound(2),
            },
        ))
    }
}
