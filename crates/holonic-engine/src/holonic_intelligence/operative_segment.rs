//! The cycle as segments, each one passage: SKE4's apparatus obligation under the contract of
//! 2026-08-18.
//!
//! A segment is a run of the ecology's operations that shares at most one use of the single
//! alignment slot (a contraction's tile, a gain, a coefficient scale) or one gather (a lookup).
//! Every section a segment writes is founded before its capture opens; every operation is
//! admitted under an a-priori octave bound derived from its inputs and its law (the bounds of
//! `resident_law.rs`, ported per primitive here), recorded into one graph whose edges are the
//! operations' bonds, with the declared successor projection fused into the graph as a midpoint
//! seal after every operation whose enclosure can widen; the graph is launched once and its
//! census read once, and that reading is the measured bound of every carrier the segment leaves
//! resident and the projection testimony of every operation.  No section crosses to the host.
//!
//! What crosses per segment: the census; what crosses per cycle beyond it: the terminal face,
//! at the declared receiver.  `TransferCensus` measures both.

use std::collections::BTreeMap;

use crate::resident_section::{
    Dyadic, PassageReading, Positions, ResidentGrain, ResidentRefusal, ResidentSection,
    SeriesAperture, SiteMask, SlotReading,
};

use super::{
    NativeCarrierAxis, NativeCarrierOrdinal, NativeCausalReach, NativeFullOperationError,
    NativeFullOperatorEcology, NativeOperationPrimitive, NativeOperatorNode,
    NativeOperatorResidence, NativeScaleConstraint, NativeSuccessorProjection,
    NativeTensorOrdinal,
    full_operation::{ContemporaryCarrier, carrier_of},
    operative_return::{OverlayAtom, OverlayTile, overlay_tile, record_overlay_contribution},
    operative_scalars::{binary64_projection, projected_scale, scale_enclosure},
};

/// Whether an operation needs the alignment slot or the gather before capture, and so begins a
/// segment.
fn begins_segment(operation: &NativeOperatorNode) -> bool {
    matches!(
        operation.primitive,
        NativeOperationPrimitive::Lookup { .. }
            | NativeOperationPrimitive::Contract
            | NativeOperationPrimitive::RmsRebase { has_gain: true, .. }
            | NativeOperationPrimitive::Scale {
                by: NativeScaleConstraint::Coefficient
            }
    )
}

/// The segments of a run of operations, as index ranges over the run.
pub(super) fn segments(operations: &[NativeOperatorNode]) -> Vec<(usize, usize)> {
    let mut ranges = Vec::new();
    let mut start = 0usize;
    for (at, operation) in operations.iter().enumerate() {
        if at > 0 && begins_segment(operation) {
            ranges.push((start, at));
            start = at;
        }
    }
    if start < operations.len() {
        ranges.push((start, operations.len()));
    }
    ranges
}

/// A withdrawal recorded after one operation inside a segment: the intervention of the
/// excitation-founded quotient, out of place, its section founded before the capture.
pub(super) struct SegmentWithdrawal<'a, 'chart> {
    pub mask: &'a SiteMask<'chart>,
    pub offset: usize,
}

/// The outcome of one operation after the segment's one census reading.
pub(super) struct SegmentOutcome<'chart> {
    pub output: NativeCarrierOrdinal,
    pub carrier: ContemporaryCarrier<'chart>,
    pub admitted_octaves: u32,
    pub projection: NativeSuccessorProjection,
}

/// The state one segment reads: disjoint borrows of the session.
pub(super) struct SegmentSite<'a, 'chart> {
    pub residence: &'a NativeOperatorResidence<'chart>,
    pub ecology: &'a NativeFullOperatorEcology,
    pub carriers: &'a BTreeMap<NativeCarrierOrdinal, ContemporaryCarrier<'chart>>,
    pub checkpoints: &'a BTreeMap<NativeCarrierOrdinal, ContemporaryCarrier<'chart>>,
    pub positions: Option<&'a Positions<'chart>>,
    pub overlay: &'a BTreeMap<NativeTensorOrdinal, Vec<OverlayAtom<'chart>>>,
    pub grain: ResidentGrain,
    pub row_addresses: &'a [u32],
    /// Withdrawals keyed by the ordinal of the operation whose output they intervene on.
    pub withdrawals: &'a BTreeMap<u32, SegmentWithdrawal<'a, 'chart>>,
    /// For a tiled boundary: the rows `(first_row, rows)` of the segment's contraction population
    /// this passage aligns and contracts, so a population wider than the slot crosses tile by tile.
    pub tile_window: Option<(usize, usize)>,
    /// Whether the successor projection is fused after every widening operation.  A declared
    /// receiver may read the terminal unsealed: its enclosures are then the apparatus's propagated
    /// remainder at the face, per coordinate, and the seal is withheld for the whole segment.
    pub seal: bool,
}

/// One operation planned before capture: its output section, its admission, whether it widens,
/// and the material it records against.
struct Planned<'chart> {
    out: ResidentSection<'chart>,
    needed: u32,
    /// The a-priori bound on the output as a value, what a consumer in the same segment is
    /// admitted against.
    value_octaves: u32,
    widens: bool,
    material: Material<'chart>,
    withdrawn: Option<ResidentSection<'chart>>,
}

/// Every resident thing an operation reads beyond its input sections.
enum Material<'chart> {
    Enter {
        address: u64,
        scale: Dyadic,
    },
    Carry,
    Select {
        from: usize,
        span: usize,
    },
    Contract {
        atoms: Vec<OverlayTile<'chart>>,
        contributions: Vec<ResidentSection<'chart>>,
        joins: Vec<ResidentSection<'chart>>,
        join_needed: Vec<u32>,
    },
    Rms {
        group: usize,
        eps: Dyadic,
        /// Whether the rebase reads the segment's aligned tile as its gain.  A rebase without a
        /// gain inside a contraction's segment must not read that contraction's tile.
        has_gain: bool,
        shape: crate::resident_section::LawShape,
    },
    Gelu {
        c1: Dyadic,
        c2: Dyadic,
        terms: SeriesAperture,
    },
    Tanh {
        terms: SeriesAperture,
    },
    Hadamard,
    Add,
    Scale {
        by: crate::resident_section::DyadicEnclosure,
    },
    CoefficientScale,
    Chronology {
        heads: usize,
        head_width: usize,
        theta: u64,
        rotated_width: usize,
    },
    Contact {
        heads: usize,
        kv_heads: usize,
        head_width: usize,
        window: usize,
        terms: SeriesAperture,
        shape: crate::resident_section::LawShape,
    },
}

fn slot_bound(slot: &SlotReading) -> u32 {
    slot.max_octave.max(1)
}

fn projection_of(slot: &SlotReading) -> NativeSuccessorProjection {
    if slot.nonzero_widths == 0 {
        NativeSuccessorProjection::Exact
    } else {
        NativeSuccessorProjection::Midpoint {
            nonpoint_coordinates: slot.nonzero_widths as usize,
            widest_interval: slot.max_width,
        }
    }
}

/// Enact one segment: found, admit, bind, launch once, read the census once.
pub(super) fn enact_segment<'chart>(
    site: &SegmentSite<'_, 'chart>,
    operations: &[NativeOperatorNode],
) -> Result<(Vec<SegmentOutcome<'chart>>, PassageReading), NativeFullOperationError> {
    let surface = site.residence.surface();
    let grain = site.grain;
    // The slot: at most one aligned tile per segment, founded before the capture.
    let mut tile = None;
    let mut planned: Vec<Planned<'chart>> = Vec::with_capacity(operations.len());
    // Inputs resolved in order: an in-segment producer's planned output, else a carried section.
    let resolved = |planned: &Vec<Planned<'chart>>, input: &NativeCarrierOrdinal| -> Result<(usize, usize, u32, ResidentGrain, Option<usize>), NativeFullOperationError> {
        if let Some(at) = operations[..planned.len()]
            .iter()
            .rposition(|earlier| earlier.output == *input)
        {
            let p = &planned[at];
            return Ok((p.out.rows(), p.out.width(), p.value_octaves, p.out.grain(), Some(at)));
        }
        let carried = carrier_of(site.carriers, site.checkpoints, input)
            .ok_or(NativeFullOperationError::Carrier)?;
        Ok((carried.section.rows(), carried.section.width(), carried.bound_octaves, carried.section.grain(), None))
    };
    for operation in operations {
        let output_axes = site
            .ecology
            .carriers
            .get(operation.output.0 as usize)
            .ok_or(NativeFullOperationError::Operation)?;
        let plan = (|| -> Result<Planned<'chart>, NativeFullOperationError> { Ok(match &operation.primitive {
            NativeOperationPrimitive::Lookup { scale } => {
                if site.row_addresses.is_empty() || operation.coefficients.len() != 1 {
                    return Err(NativeFullOperationError::Occurrence);
                }
                let coefficient = operation.coefficients[0];
                let population = site
                    .ecology
                    .coefficient_populations
                    .get(coefficient.0 as usize)
                    .ok_or(NativeFullOperationError::Operation)?;
                let [_, width] = population.shape.as_slice() else {
                    return Err(NativeFullOperationError::Operation);
                };
                if output_axes.axes != [NativeCarrierAxis::Occurrence, NativeCarrierAxis::Fixed(*width)] {
                    return Err(NativeFullOperationError::Operation);
                }
                let scale = projected_scale(scale)?;
                let selection = site.residence.gather_rows(coefficient, site.row_addresses)?;
                if selection.width != *width || selection.rows != site.row_addresses.len() {
                    return Err(NativeFullOperationError::Operation);
                }
                let exact_frame = selection
                    .frame
                    .exponent
                    .checked_add(scale.exponent)
                    .ok_or(NativeFullOperationError::Grain)?;
                if exact_frame + (grain.0 as i32) < 0 {
                    return Err(NativeFullOperationError::Grain);
                }
                let shape = surface.shape_enter_resident_bfloat16(
                    selection.rows,
                    selection.width,
                    scale,
                    grain,
                    selection.frame.exponent,
                    selection.entry_octaves,
                )?;
                Planned {
                    out: surface.fresh_section(selection.rows, selection.width, grain)?,
                    needed: shape.needed,
                    value_octaves: shape.needed,
                    widens: false,
                    material: Material::Enter {
                        address: selection.address,
                        scale,
                    },
                    withdrawn: None,
                }
            }
            NativeOperationPrimitive::Reshape | NativeOperationPrimitive::Emit => {
                let (rows, width, octaves, g, _) = resolved(&planned, &operation.inputs[0])?;
                let shape = surface.shape_carry(rows, width, octaves)?;
                Planned {
                    out: surface.fresh_section(rows, width, g)?,
                    needed: shape.needed,
                    value_octaves: octaves,
                    widens: false,
                    material: Material::Carry,
                    withdrawn: None,
                }
            }
            NativeOperationPrimitive::Select { axis, at } => {
                if *axis != 1 {
                    return Err(NativeFullOperationError::Operation);
                }
                let span = match output_axes.axes.last() {
                    Some(NativeCarrierAxis::Fixed(span)) => *span,
                    _ => return Err(NativeFullOperationError::Operation),
                };
                let (rows, width, octaves, g, _) = resolved(&planned, &operation.inputs[0])?;
                let from = at.checked_mul(span).ok_or(NativeFullOperationError::Operation)?;
                let shape = surface.shape_select_columns(rows, width, from, span, octaves)?;
                Planned {
                    out: surface.fresh_section(rows, span, g)?,
                    needed: shape.needed,
                    value_octaves: octaves,
                    widens: false,
                    material: Material::Select { from, span },
                    withdrawn: None,
                }
            }
            NativeOperationPrimitive::Contract => {
                if operation.inputs.len() != 1 || operation.coefficients.len() != 1 || tile.is_some() {
                    return Err(NativeFullOperationError::Operation);
                }
                let (rows, width, octaves, g, _) = resolved(&planned, &operation.inputs[0])?;
                let coefficient = operation.coefficients[0];
                let population = site
                    .ecology
                    .coefficient_populations
                    .get(coefficient.0 as usize)
                    .ok_or(NativeFullOperationError::Operation)?;
                let [population_rows, dim] = population.shape.as_slice() else {
                    return Err(NativeFullOperationError::Operation);
                };
                if width != *dim {
                    return Err(NativeFullOperationError::Operation);
                }
                let (first_row, out_rows) = match site.tile_window {
                    Some((first_row, rows)) if first_row + rows <= *population_rows => (first_row, rows),
                    Some(_) => return Err(NativeFullOperationError::Operation),
                    None => (0usize, *population_rows),
                };
                let out_rows = &out_rows;
                let aligned = site.residence.align_tile(coefficient, first_row, *out_rows)?;
                let shape = surface.shape_contract(rows, width, octaves, &aligned.mounted.readout)?;
                let atoms = site.overlay.get(&coefficient).map(Vec::as_slice).unwrap_or(&[]);
                let input_section = match resolved(&planned, &operation.inputs[0])?.4 {
                    Some(at) => &planned[at].out,
                    None => &carrier_of(site.carriers, site.checkpoints, &operation.inputs[0])
                        .ok_or(NativeFullOperationError::Carrier)?
                        .section,
                };
                let mut overlay_tiles = Vec::with_capacity(atoms.len());
                let mut contributions = Vec::with_capacity(atoms.len());
                let mut joins = Vec::with_capacity(atoms.len());
                let mut join_needed = Vec::with_capacity(atoms.len());
                let mut carrier_octaves = shape.needed;
                for atom in atoms {
                    let overlay = overlay_tile(surface, atom, input_section, octaves, first_row, *out_rows)?;
                    let join = surface.shape_re_entry(rows, *out_rows, carrier_octaves, overlay.needed())?;
                    carrier_octaves = join.needed;
                    contributions.push(surface.fresh_section(rows, *out_rows, g)?);
                    joins.push(surface.fresh_section(rows, *out_rows, g)?);
                    join_needed.push(join.needed);
                    overlay_tiles.push(overlay);
                }
                // The value bound of a contraction: the input's octaves and the population's
                // greatest row mass (`resident_law.rs`, `Contract::bound_octaves`).
                let value_octaves = octaves + aligned.mounted.mass_value_octaves + 1;
                let value_octaves = value_octaves.max(carrier_octaves.min(value_octaves));
                let out = surface.fresh_section(rows, *out_rows, g)?;
                tile = Some(aligned);
                Planned {
                    out,
                    needed: carrier_octaves,
                    value_octaves,
                    widens: true,
                    material: Material::Contract {
                        atoms: overlay_tiles,
                        contributions,
                        joins,
                        join_needed,
                    },
                    withdrawn: None,
                }
            }
            NativeOperationPrimitive::RmsRebase {
                group,
                epsilon,
                has_gain,
            } => {
                let (rows, width, octaves, g, _) = resolved(&planned, &operation.inputs[0])?;
                let gain_value = if *has_gain {
                    if tile.is_some() {
                        return Err(NativeFullOperationError::Operation);
                    }
                    tile = Some(site.residence.align_tile(operation.coefficients[0], 0, 1)?);
                    let readout = &tile.as_ref().expect("aligned").mounted.readout;
                    i64::from(readout.entry_octaves()) + i64::from(readout.exponent())
                } else {
                    0
                };
                let readout = if *has_gain {
                    tile.as_ref().map(|t| &t.mounted.readout)
                } else {
                    None
                };
                let shape = surface.shape_rms_rebase(rows, width, *group, octaves, readout)?;
                // The value bound of the rebase on a point section: `mean(x²) ≥ x_i²/group`, so
                // `|y_i| = |x_i|/sqrt(mean(x²)+eps) ≤ sqrt(group)`, and `|g|` scales it; one octave
                // for the sealed enclosure of the series.  Every carrier a segment consumes is a
                // point section: the fused seal projects every widening operation's enclosure to
                // its midpoint, and the exact operations preserve points, so the enclosure bound
                // `|x|/sqrt(eps)` of `resident_law.rs` never governs here.
                let f = i64::from(grain.0);
                let ceil_log2 = |n: usize| i64::from(if n <= 1 { 0 } else { (n - 1).ilog2() + 1 });
                let value = f + (ceil_log2(*group) + 1) / 2 + gain_value.max(0) + 2;
                Planned {
                    out: surface.fresh_section(rows, width, g)?,
                    needed: shape.needed,
                    value_octaves: u32::try_from(value.max(1)).map_err(|_| NativeFullOperationError::Grain)?,
                    widens: true,
                    material: Material::Rms {
                        group: *group,
                        eps: binary64_projection(epsilon)?,
                        has_gain: *has_gain,
                        shape,
                    },
                    withdrawn: None,
                }
            }
            NativeOperationPrimitive::GeluTanh => {
                let (rows, width, octaves, g, _) = resolved(&planned, &operation.inputs[0])?;
                let c1 = Dyadic::of_binary64_bits(0x3fe9_8845_33d4_3651)?;
                let c2 = Dyadic::of_binary64_bits(0x3fa6_e4e2_6d48_01f7)?;
                let terms = SeriesAperture(14);
                let shape = surface.shape_gelu_tanh(rows, width, octaves, g, c1, c2, terms)?;
                Planned {
                    out: surface.fresh_section(rows, width, g)?,
                    needed: shape.needed,
                    value_octaves: octaves + 1,
                    widens: true,
                    material: Material::Gelu { c1, c2, terms },
                    withdrawn: None,
                }
            }
            NativeOperationPrimitive::Tanh => {
                let (rows, width, octaves, g, _) = resolved(&planned, &operation.inputs[0])?;
                let terms = SeriesAperture(14);
                let shape = surface.shape_tanh(rows, width, octaves, g, terms)?;
                Planned {
                    out: surface.fresh_section(rows, width, g)?,
                    needed: shape.needed,
                    value_octaves: grain.0 + 1,
                    widens: true,
                    material: Material::Tanh { terms },
                    withdrawn: None,
                }
            }
            NativeOperationPrimitive::Hadamard | NativeOperationPrimitive::Add => {
                let (rows, width, a, g, _) = resolved(&planned, &operation.inputs[0])?;
                let (rows_b, width_b, b, g_b, _) = resolved(&planned, &operation.inputs[1])?;
                if rows != rows_b || width != width_b || g != g_b {
                    return Err(NativeFullOperationError::Operation);
                }
                let additive = matches!(operation.primitive, NativeOperationPrimitive::Add);
                let (shape, value_octaves) = if additive {
                    (surface.shape_re_entry(rows, width, a, b)?, a.max(b) + 1)
                } else {
                    (surface.shape_hadamard(rows, width, a, b)?, (a + b + 1).saturating_sub(grain.0).max(1))
                };
                // A sum of points at one grain is exact; a product rounds to the grain and is
                // sealed like every other rounding operation, so every carrier stays a point.
                Planned {
                    out: surface.fresh_section(rows, width, g)?,
                    needed: shape.needed,
                    value_octaves,
                    widens: !additive,
                    material: if additive { Material::Add } else { Material::Hadamard },
                    withdrawn: None,
                }
            }
            NativeOperationPrimitive::Scale { by } if !matches!(by, NativeScaleConstraint::Coefficient) => {
                let (rows, width, octaves, g, _) = resolved(&planned, &operation.inputs[0])?;
                let enclosure = scale_enclosure(by)?;
                let shape = surface.shape_scale(rows, width, octaves, enclosure)?;
                let magnitude = enclosure.lo.unsigned_abs().max(enclosure.hi.unsigned_abs());
                let by_octaves = if magnitude == 0 { 0 } else { 64 - magnitude.leading_zeros() };
                Planned {
                    out: surface.fresh_section(rows, width, g)?,
                    needed: shape.needed,
                    value_octaves: (octaves + by_octaves + 1).saturating_sub(enclosure.grain).max(1),
                    widens: true,
                    material: Material::Scale { by: enclosure },
                    withdrawn: None,
                }
            }
            NativeOperationPrimitive::Scale { .. } => {
                if tile.is_some() || operation.coefficients.len() != 1 {
                    return Err(NativeFullOperationError::Operation);
                }
                let (rows, width, octaves, g, _) = resolved(&planned, &operation.inputs[0])?;
                tile = Some(site.residence.align_tile(operation.coefficients[0], 0, 1)?);
                let readout = &tile.as_ref().expect("aligned").mounted.readout;
                let shape = surface.shape_scale_by_aligned(rows, width, octaves, readout)?;
                let value = i64::from(octaves) + i64::from(readout.entry_octaves()) + i64::from(readout.exponent()) + 1;
                Planned {
                    out: surface.fresh_section(rows, width, g)?,
                    needed: shape.needed,
                    value_octaves: u32::try_from(value.max(1)).map_err(|_| NativeFullOperationError::Grain)?,
                    widens: true,
                    material: Material::CoefficientScale,
                    withdrawn: None,
                }
            }
            NativeOperationPrimitive::RotaryChronology {
                theta,
                head_width,
                rotated_width,
            } => {
                let (rows, width, octaves, g, _) = resolved(&planned, &operation.inputs[0])?;
                if width % head_width != 0 {
                    return Err(NativeFullOperationError::Operation);
                }
                let heads = width / head_width;
                let positions = site.positions.ok_or(NativeFullOperationError::Occurrence)?;
                let bands = site.residence.chronology(*theta, *head_width, *rotated_width)?;
                let shape = surface.shape_chronology(
                    rows,
                    width,
                    heads,
                    *head_width,
                    octaves,
                    bands,
                    positions,
                    u32::try_from(rows.saturating_sub(1)).map_err(|_| NativeFullOperationError::Operation)?,
                )?;
                Planned {
                    out: surface.fresh_section(rows, width, g)?,
                    needed: shape.needed,
                    value_octaves: octaves + 1,
                    widens: true,
                    material: Material::Chronology {
                        heads,
                        head_width: *head_width,
                        theta: *theta,
                        rotated_width: *rotated_width,
                    },
                    withdrawn: None,
                }
            }
            NativeOperationPrimitive::CausalContact {
                heads,
                kv_heads,
                head_width,
                reach,
                series_terms,
            } => {
                let (rows, q_width, q_oct, g, _) = resolved(&planned, &operation.inputs[0])?;
                let (rows_k, k_width, k_oct, g_k, _) = resolved(&planned, &operation.inputs[1])?;
                let (rows_v, v_width, v_oct, g_v, _) = resolved(&planned, &operation.inputs[2])?;
                if rows != rows_k || rows != rows_v || g != g_k || g != g_v {
                    return Err(NativeFullOperationError::Operation);
                }
                let window = match reach {
                    NativeCausalReach::Window(window) if *window > 0 => *window,
                    NativeCausalReach::Complete => rows,
                    _ => return Err(NativeFullOperationError::Operation),
                };
                let terms = SeriesAperture(*series_terms);
                let shape = surface.shape_contact(
                    rows, q_width, k_width, v_width, *heads, *kv_heads, *head_width, window, terms, g,
                    q_oct, k_oct, v_oct,
                )?;
                Planned {
                    out: surface.fresh_section(rows, heads * head_width, g)?,
                    needed: shape.needed,
                    value_octaves: v_oct + 1,
                    widens: true,
                    material: Material::Contact {
                        heads: *heads,
                        kv_heads: *kv_heads,
                        head_width: *head_width,
                        window,
                        terms,
                        shape,
                    },
                    withdrawn: None,
                }
            }
        }) })();
        let plan = match plan {
            Ok(plan) => plan,
            // A carrier obligation the a-priori bounds cannot meet closes the segment before this
            // operation: it is enacted at the head of the next passage on the measured bounds of
            // this one's census.  At the head of a segment the refusal is the law's own.
            Err(NativeFullOperationError::Resident(ResidentRefusal::CarrierRange { .. }))
                if !planned.is_empty() =>
            {
                break;
            }
            Err(refusal) => return Err(refusal),
        };
        let mut plan = plan;
        if let Some(withdrawal) = site.withdrawals.get(&operation.ordinal) {
            let _ = withdrawal;
            plan.withdrawn = Some(surface.fresh_section(plan.out.rows(), plan.out.width(), plan.out.grain())?);
        }
        planned.push(plan);
    }
    // Occurrence indices: an operation, its overlay contributions and joins, its seal, its
    // withdrawal; the index a consumer reads is the last of them.
    let mut base = Vec::with_capacity(planned.len());
    let mut last = Vec::with_capacity(planned.len());
    let mut lineage: Vec<Vec<usize>> = Vec::new();
    for (at, plan) in planned.iter().enumerate() {
        let producers: Vec<usize> = operations[at]
            .inputs
            .iter()
            .filter_map(|input| {
                operations[..at]
                    .iter()
                    .rposition(|earlier| earlier.output == *input)
                    .map(|p| last[p])
            })
            .collect();
        let b = lineage.len();
        base.push(b);
        lineage.push(producers);
        let mut tail = b;
        if let Material::Contract { atoms, .. } = &plan.material {
            let count = atoms.len();
            for _ in 0..count {
                lineage.push(Vec::new());
            }
            for j in 0..count {
                let previous = if j == 0 { b } else { b + count + j };
                lineage.push(vec![previous, b + 1 + j]);
            }
            if count > 0 {
                tail = b + 2 * count;
            }
        }
        if plan.widens && site.seal {
            lineage.push(vec![tail]);
            tail = lineage.len() - 1;
        }
        if plan.withdrawn.is_some() {
            lineage.push(vec![tail]);
            tail = lineage.len() - 1;
        }
        last.push(tail);
    }
    let census_before = surface.census();
    let mut builder = surface.begin_passage(&lineage)?;
    for (at, plan) in planned.iter().enumerate() {
        let operation = &operations[at];
        let input_section = |i: usize| -> Result<&ResidentSection<'chart>, NativeFullOperationError> {
            let input = &operation.inputs[i];
            match operations[..at].iter().rposition(|earlier| earlier.output == *input) {
                Some(p) => Ok(&planned[p].out_or_withdrawn()),
                None => Ok(&carrier_of(site.carriers, site.checkpoints, input)
                    .ok_or(NativeFullOperationError::Carrier)?
                    .section),
            }
        };
        let b = base[at];
        let mut tail = b;
        {
            let lane = builder.open(b, &lineage[b])?;
            match &plan.material {
                Material::Enter { address, scale } => surface.record_enter_resident_bfloat16(
                    &lane, *address, plan.out.rows(), plan.out.width(), *scale, &plan.out,
                )?,
                Material::Carry => surface.record_carry(&lane, input_section(0)?, &plan.out)?,
                Material::Select { from, span } => {
                    surface.record_select_columns(&lane, input_section(0)?, *from, *span, &plan.out)?
                }
                Material::Contract { .. } => {
                    let readout = &tile.as_ref().ok_or(NativeFullOperationError::Operation)?.mounted.readout;
                    surface.record_contract(&lane, input_section(0)?, readout, &plan.out)?
                }
                Material::Rms {
                    group,
                    eps,
                    has_gain,
                    shape,
                } => {
                    let readout = if *has_gain {
                        Some(&tile.as_ref().ok_or(NativeFullOperationError::Operation)?.mounted.readout)
                    } else {
                        None
                    };
                    surface.record_rms_rebase(&lane, input_section(0)?, *group, readout, *eps, shape, &plan.out)?
                }
                Material::Gelu { c1, c2, terms } => {
                    surface.record_gelu_tanh(&lane, input_section(0)?, *c1, *c2, *terms, &plan.out)?
                }
                Material::Tanh { terms } => surface.record_tanh(&lane, input_section(0)?, *terms, &plan.out)?,
                Material::Hadamard => {
                    surface.record_hadamard(&lane, input_section(0)?, input_section(1)?, &plan.out)?
                }
                Material::Add => surface.record_re_entry(&lane, input_section(0)?, input_section(1)?, &plan.out)?,
                Material::Scale { by } => surface.record_scale(&lane, input_section(0)?, *by, &plan.out)?,
                Material::CoefficientScale => {
                    let readout = &tile.as_ref().ok_or(NativeFullOperationError::Operation)?.mounted.readout;
                    surface.record_scale_by_aligned(&lane, input_section(0)?, readout, &plan.out)?
                }
                Material::Chronology {
                    heads,
                    head_width,
                    theta,
                    rotated_width,
                } => {
                    let positions = site.positions.ok_or(NativeFullOperationError::Occurrence)?;
                    let bands = site.residence.chronology(*theta, *head_width, *rotated_width)?;
                    surface.record_chronology(&lane, input_section(0)?, *heads, *head_width, bands, positions, &plan.out)?
                }
                Material::Contact {
                    heads,
                    kv_heads,
                    head_width,
                    window,
                    terms,
                    shape,
                } => surface.record_contact(
                    &lane, input_section(0)?, input_section(1)?, input_section(2)?, *heads, *kv_heads,
                    *head_width, *window, *terms, None, shape, &plan.out,
                )?,
            }
        }
        builder.close(b, &plan.out, plan.needed)?;
        if let Material::Contract {
            atoms,
            contributions,
            joins,
            join_needed,
        } = &plan.material
        {
            let count = atoms.len();
            let input = input_section(0)?;
            for (j, overlay) in atoms.iter().enumerate() {
                record_overlay_contribution(surface, &mut builder, b + 1 + j, overlay, input, &contributions[j])?;
            }
            for j in 0..count {
                let previous = if j == 0 { &plan.out } else { &joins[j - 1] };
                let index = b + 1 + count + j;
                {
                    let lane = builder.open(index, &lineage[index])?;
                    surface.record_re_entry(&lane, previous, &contributions[j], &joins[j])?;
                }
                builder.close(index, &joins[j], join_needed[j])?;
            }
            if count > 0 {
                tail = b + 2 * count;
            }
        }
        if plan.widens && site.seal {
            let index = tail + 1;
            let sealed = plan.joined();
            {
                let lane = builder.open(index, &lineage[index])?;
                surface.record_midpoint_seal(&lane, sealed, plan.needed)?;
            }
            builder.close_fused(index)?;
            tail = index;
        }
        if let Some(withdrawn) = &plan.withdrawn {
            let withdrawal = site
                .withdrawals
                .get(&operation.ordinal)
                .ok_or(NativeFullOperationError::Operation)?;
            let index = tail + 1;
            let shape = surface.shape_withdraw_sites(withdrawn.rows(), withdrawn.width(), plan.needed)?;
            {
                let lane = builder.open(index, &lineage[index])?;
                surface.record_withdraw_sites(&lane, plan.joined(), withdrawal.mask, withdrawal.offset, withdrawn)?;
            }
            builder.close(index, withdrawn, shape.needed)?;
        }
    }
    let reading = builder.finish()?.launch()?;
    if !reading.obstruction.is_empty() {
        return Err(NativeFullOperationError::ResidentObstruction {
            operation: operations[0].ordinal,
            flags: reading.obstruction.joined_flags(),
        });
    }
    let _ = census_before;
    let mut outcomes = Vec::with_capacity(planned.len());
    for (at, plan) in planned.into_iter().enumerate() {
        let op_slot = reading.slots.get(base[at]).ok_or(NativeFullOperationError::Operation)?;
        let last_slot = reading.slots.get(last[at]).ok_or(NativeFullOperationError::Operation)?;
        let projection = projection_of(op_slot);
        let bound_octaves = slot_bound(last_slot);
        let Planned {
            out,
            needed,
            material,
            withdrawn,
            ..
        } = plan;
        let section = match (withdrawn, material) {
            (Some(withdrawn), _) => withdrawn,
            (None, Material::Contract { mut joins, .. }) if !joins.is_empty() => joins.pop().expect("join"),
            (None, _) => out,
        };
        outcomes.push(SegmentOutcome {
            output: operations[at].output,
            carrier: ContemporaryCarrier {
                section,
                bound_octaves,
            },
            admitted_octaves: needed,
            projection,
        });
    }
    drop(tile);
    Ok((outcomes, reading))
}

impl<'chart> Planned<'chart> {
    /// The section a consumer reads: the last join of an overlaid contraction, else the output.
    fn joined(&self) -> &ResidentSection<'chart> {
        match &self.material {
            Material::Contract { joins, .. } if !joins.is_empty() => joins.last().expect("join"),
            _ => &self.out,
        }
    }

    fn out_or_withdrawn(&self) -> &ResidentSection<'chart> {
        match &self.withdrawn {
            Some(withdrawn) => withdrawn,
            None => self.joined(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn node(ordinal: u32, primitive: NativeOperationPrimitive) -> NativeOperatorNode {
        NativeOperatorNode {
            ordinal,
            layer: None,
            primitive,
            inputs: vec![],
            output: NativeCarrierOrdinal(ordinal),
            coefficients: vec![],
        }
    }

    #[test]
    fn a_segment_begins_at_every_use_of_the_slot_or_the_gather() {
        let operations = vec![
            node(0, NativeOperationPrimitive::Lookup { scale: NativeScaleConstraint::Rational { numerator: 1, denominator: 1 } }),
            node(1, NativeOperationPrimitive::Reshape),
            node(2, NativeOperationPrimitive::Contract),
            node(3, NativeOperationPrimitive::GeluTanh),
            node(4, NativeOperationPrimitive::Hadamard),
            node(5, NativeOperationPrimitive::RmsRebase { group: 4, epsilon: relational_geometry::Rat::from_integer(0.into()), has_gain: true }),
            node(6, NativeOperationPrimitive::Add),
            node(7, NativeOperationPrimitive::RmsRebase { group: 4, epsilon: relational_geometry::Rat::from_integer(0.into()), has_gain: false }),
        ];
        assert_eq!(segments(&operations), vec![(0, 2), (2, 5), (5, 8)]);
        assert_eq!(segments(&operations[3..]), vec![(0, 2), (2, 5)]);
    }
}
