//! Excitation and the cone by intervention: SKE2's owner.
//!
//! A cycle on an occurrence excites the resident realization.  The receiver is the selected face
//! at the terminal position; the excitation is the differential of that face's own normalized
//! exponential probability at the last row, returned through every reaction of the cycle by the
//! SKE1 instrument without depositing.  At the output of every contraction population the
//! differential is read per site (the output coordinate: one row of the cross-section, read at
//! every position) beside the forward's own output there: the support, the magnitude, and the
//! first-order contribution of withdrawing the site.
//!
//! The cone is founded by intervention, never by a magnitude, and jointly: the sites of the
//! excitation-founded quotient are every output coordinate of every contraction population at
//! once, and `IsCone` is a law over withdrawals of any population of them.  A site selection is
//! withdrawn — zeroed at each contraction's output at every position, the `withdraw` of the
//! quotient — and the cycle is enacted again from the earliest touched segment on the retained
//! checkpoints through the terminal boundary.  The cone is the smallest suffix of the sites
//! ordered by first-order contribution whose complement, withdrawn as one population, leaves the
//! face unchanged; every exclusion is a withdrawal the card returned unchanged, and the ordering
//! decides only what is tried.  Two controls close it: the complement withdrawn leaves the face,
//! the cone withdrawn changes it.  Beside each population's restriction of the cone a magnitude
//! ranking of the forward's output is exhibited so a threshold can be shown not to determine it.
//! Nothing here selects an answer: the face compared is the one the operator itself emitted.
//!
//! Formal owners composed: `HolonicExcitationFoundedQuotient.withdraw`, `.IsCone`,
//! `.LoadBearing`, and the control `Control.cone_false`/`cone_true` (equal magnitudes, different
//! cones).

use std::collections::BTreeMap;

use serde::Serialize;

use crate::resident_section::{ResidentSection, SeriesAperture};

use super::{
    NativeFullOperationError, NativeFullOperatorEcology, NativeFullOperatorSession,
    NativeOperationPrimitive, NativeOperatorNode, NativeOperatorResidence, NativeTensorOrdinal,
    operative_backward::ReturnDeed,
    operative_return::{ReturnMaterial, ReturnedDifferential, receiver_differential},
    operative_scalars::operation_bound,
    operative_segment::SegmentWithdrawal,
    operative_terminal::TiledCarrier,
};

/// The declared aperture of a dissection: only the certified exponential's series aperture.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct NativeDissectionAperture {
    pub series_terms: u32,
}

/// The receiver face at the terminal position: the selected coordinate under the application's
/// own rule (the greatest midpoint, the first of equals) and the fold digest of the exact row.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeReceiverFace {
    pub selected: u32,
    pub equal_population: usize,
    pub width: usize,
    pub exact_digest: String,
}

/// The excitation read at one contraction population, per site: whether the returned
/// differential is nonzero at any position (the support), the greatest |midpoint| of the
/// forward's own output over the positions in grain units (the magnitude), and the first-order
/// contribution of withdrawing the site, `|Σ_positions d · y|` in grain² units.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeSiteSupport {
    pub population: u32,
    pub operation: u32,
    pub layer: Option<u16>,
    pub sites: usize,
    pub support: Vec<bool>,
    pub support_population: usize,
    pub magnitudes: Vec<u64>,
    pub contributions: Vec<u128>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeSiteSupportSummary {
    pub population: u32,
    pub operation: u32,
    pub layer: Option<u16>,
    pub sites: usize,
    pub support_population: usize,
}

/// The standing of a dissection across one cycle: the excitation's supports and the face.
pub(super) struct DissectionStanding {
    pub(super) aperture: NativeDissectionAperture,
    pub(super) supports: BTreeMap<NativeTensorOrdinal, NativeSiteSupport>,
    pub(super) face: Option<NativeReceiverFace>,
}

impl DissectionStanding {
    pub(super) fn found(aperture: NativeDissectionAperture) -> Self {
        Self {
            aperture,
            supports: BTreeMap::new(),
            face: None,
        }
    }

    pub(super) fn clear(&mut self) {
        self.supports.clear();
        self.face = None;
    }
}

/// The testimony of one excitation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeExcitationTrace {
    pub face: NativeReceiverFace,
    pub operations_returned: usize,
    pub layers_replayed: usize,
    pub supports: Vec<NativeSiteSupportSummary>,
    pub elapsed_milliseconds: u128,
}

/// One site selection across contraction populations: for each population touched, the offset
/// of its sites in one flat mask.  Populations absent from `offsets` are not intervened on.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeSiteSelection {
    offsets: BTreeMap<NativeTensorOrdinal, (usize, usize)>,
    withdrawn: Vec<bool>,
}

impl NativeSiteSelection {
    /// A selection over the given populations with their site counts, nothing withdrawn yet.
    pub fn founded(sites: &BTreeMap<NativeTensorOrdinal, usize>) -> Self {
        let mut offsets = BTreeMap::new();
        let mut total = 0usize;
        for (population, count) in sites {
            offsets.insert(*population, (total, *count));
            total += count;
        }
        Self {
            offsets,
            withdrawn: vec![false; total],
        }
    }

    /// A selection over one population.
    pub fn single(population: NativeTensorOrdinal, withdrawn: &[bool]) -> Self {
        Self {
            offsets: BTreeMap::from([(population, (0, withdrawn.len()))]),
            withdrawn: withdrawn.to_vec(),
        }
    }

    pub fn withdraw(&mut self, population: NativeTensorOrdinal, site: usize) -> bool {
        match self.offsets.get(&population) {
            Some((offset, count)) if site < *count => {
                self.withdrawn[offset + site] = true;
                true
            }
            _ => false,
        }
    }

    pub fn withdrawn_population(&self) -> usize {
        self.withdrawn.iter().filter(|site| **site).count()
    }

    pub fn withdrawn_of(&self, population: NativeTensorOrdinal) -> Option<&[bool]> {
        self.offsets
            .get(&population)
            .map(|(offset, count)| &self.withdrawn[*offset..offset + count])
    }

    /// Withdraw every site another selection over the same populations withdraws.
    pub fn absorb(&mut self, other: &NativeSiteSelection) {
        for (population, (offset, count)) in &other.offsets {
            if let Some((own, own_count)) = self.offsets.get(population) {
                let span = (*count).min(*own_count);
                for site in 0..span {
                    if other.withdrawn[offset + site] {
                        self.withdrawn[own + site] = true;
                    }
                }
            }
        }
    }

    /// The selection withdrawing every site of these populations that `kept` does not keep.
    pub fn complement_of(sizes: &BTreeMap<NativeTensorOrdinal, usize>, kept: &BTreeMap<u32, Vec<bool>>) -> Self {
        let mut selection = Self::founded(sizes);
        for (population, count) in sizes {
            let keep = kept.get(&population.0);
            for site in 0..*count {
                if !keep.and_then(|k| k.get(site).copied()).unwrap_or(false) {
                    selection.withdraw(*population, site);
                }
            }
        }
        selection
    }

    fn touches(&self, population: NativeTensorOrdinal) -> bool {
        self.withdrawn_of(population)
            .is_some_and(|sites| sites.iter().any(|site| *site))
    }

    fn offset_of(&self, population: NativeTensorOrdinal) -> Option<usize> {
        self.offsets.get(&population).map(|(offset, _)| *offset)
    }
}

/// The face returned under one withdrawal.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeWithdrawnFace {
    pub populations_withdrawn: usize,
    pub withdrawn: usize,
    pub face: NativeReceiverFace,
    pub selected_unchanged: bool,
    pub exact_unchanged: bool,
    pub operations_enacted: usize,
    pub elapsed_milliseconds: u128,
}

/// The magnitude control: a threshold on the forward's own output magnitude does not determine
/// the cone when every threshold misclassifies at least one site.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeMagnitudeControl {
    pub cone_minimum: u64,
    pub cone_maximum: u64,
    pub outside_minimum: u64,
    pub outside_maximum: u64,
    pub outside_above_cone_minimum: usize,
    pub cone_below_outside_maximum: usize,
    pub least_misclassified_by_threshold: usize,
    pub threshold_determines_cone: bool,
}

/// The per-population support controls of the blueprint's first letter: the support of one
/// population withdrawn alone, and its complement withdrawn alone.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeConeVerdict {
    pub population: u32,
    pub operation: u32,
    pub layer: Option<u16>,
    pub sites: usize,
    pub support_population: usize,
    pub outside_withdrawn: NativeWithdrawnFace,
    pub inside_withdrawn: NativeWithdrawnFace,
    pub outside_unchanged: bool,
    pub inside_changed: bool,
    pub founded: bool,
    pub magnitude: NativeMagnitudeControl,
}

/// One probe of the cone search: the first `withdrawn` sites of the contribution order withdrawn
/// jointly.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeConeProbe {
    pub withdrawn: usize,
    pub face_selected: u32,
    pub selected_unchanged: bool,
    pub exact_unchanged: bool,
    pub elapsed_milliseconds: u128,
}

/// The cone restricted to one population, with its exact site support and magnitude control.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeConeRestriction {
    pub population: u32,
    pub operation: u32,
    pub layer: Option<u16>,
    pub sites: usize,
    pub cone_population: usize,
    #[serde(skip)]
    pub cone: Vec<bool>,
    pub magnitude: NativeMagnitudeControl,
}

/// The site at the cone's boundary: the last site the order admitted into the cone, whose
/// withdrawal together with the complement changes the face.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeConeBoundary {
    pub population: u32,
    pub site: u32,
    pub contribution: u128,
    pub magnitude: u64,
    pub alone: NativeWithdrawnFace,
}

/// The cone of one occurrence at the selected-face receiver, founded by joint intervention.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeConeReturn {
    pub face: NativeReceiverFace,
    pub sites: usize,
    pub cone_population: usize,
    pub complement_population: usize,
    /// Whether withdrawing every site changes the face at all: a face no site carries has an
    /// empty cone.
    pub carried: bool,
    pub probes: Vec<NativeConeProbe>,
    pub monotone: bool,
    pub complement_withdrawn: NativeWithdrawnFace,
    pub cone_withdrawn: NativeWithdrawnFace,
    pub boundary: Option<NativeConeBoundary>,
    pub restrictions: Vec<NativeConeRestriction>,
    pub elapsed_milliseconds: u128,
}

/// The face of the last row of a stitched emission under the application's own selection rule.
pub fn face_of_last_row(intervals: &[(i64, i64)], rows: usize, width: usize) -> Option<NativeReceiverFace> {
    if rows == 0 || width == 0 || intervals.len() != rows * width {
        return None;
    }
    let row = &intervals[(rows - 1) * width..];
    let mut fold: u64 = 0xcbf2_9ce4_8422_2325;
    let mut greatest = i128::MIN;
    let mut selected = 0u32;
    let mut equal = 0usize;
    for (at, (lo, hi)) in row.iter().enumerate() {
        for word in [*lo as u64, *hi as u64] {
            fold ^= word;
            fold = fold.wrapping_mul(0x0100_0000_01b3);
        }
        let value = midpoint(*lo, *hi);
        if value > greatest {
            greatest = value;
            selected = at as u32;
            equal = 1;
        } else if value == greatest {
            equal += 1;
        }
    }
    Some(NativeReceiverFace {
        selected,
        equal_population: equal,
        width,
        exact_digest: format!("{fold:016x}"),
    })
}

fn midpoint(lo: i64, hi: i64) -> i128 {
    i128::from(lo) + (i128::from(hi) - i128::from(lo)) / 2
}

/// Per site: the support, the greatest |midpoint| of the forward output over the rows, and the
/// first-order contribution `|Σ_rows d · y|`.  `forward` holds `forward_rows` rows; when it
/// holds one row it is read against the differential's last row alone.
fn read_sites(
    differential: &[(i64, i64)],
    rows: usize,
    width: usize,
    forward: &[(i64, i64)],
    forward_rows: usize,
) -> (Vec<bool>, Vec<u64>, Vec<u128>) {
    let mut support = vec![false; width];
    let mut magnitudes = vec![0u64; width];
    let mut contributions = vec![0i128; width];
    for row in 0..rows {
        let forward_row = if forward_rows == rows { row } else { forward_rows - 1 };
        let reads_forward = forward_rows == rows || row + 1 == rows;
        for site in 0..width {
            let (lo, hi) = differential[row * width + site];
            if lo != 0 || hi != 0 {
                support[site] = true;
            }
            if reads_forward {
                let (y_lo, y_hi) = forward[forward_row * width + site];
                let y = midpoint(y_lo, y_hi);
                let magnitude = u64::try_from(y.unsigned_abs()).unwrap_or(u64::MAX);
                if magnitude > magnitudes[site] {
                    magnitudes[site] = magnitude;
                }
                contributions[site] = contributions[site].saturating_add(midpoint(lo, hi).saturating_mul(y));
            }
        }
    }
    let contributions = contributions
        .into_iter()
        .map(|contribution| contribution.unsigned_abs())
        .collect();
    (support, magnitudes, contributions)
}

/// The magnitude control over one cone: the least number of sites any threshold on the
/// magnitude misclassifies against the cone.
pub fn magnitude_control(cone: &[bool], magnitudes: &[u64]) -> NativeMagnitudeControl {
    let mut cone_minimum = u64::MAX;
    let mut cone_maximum = 0u64;
    let mut outside_minimum = u64::MAX;
    let mut outside_maximum = 0u64;
    let mut inside = 0usize;
    for (site, in_cone) in cone.iter().enumerate() {
        let magnitude = magnitudes[site];
        if *in_cone {
            inside += 1;
            cone_minimum = cone_minimum.min(magnitude);
            cone_maximum = cone_maximum.max(magnitude);
        } else {
            outside_minimum = outside_minimum.min(magnitude);
            outside_maximum = outside_maximum.max(magnitude);
        }
    }
    let outside_above_cone_minimum = cone
        .iter()
        .zip(magnitudes)
        .filter(|(in_cone, magnitude)| !**in_cone && inside > 0 && **magnitude > cone_minimum)
        .count();
    let cone_below_outside_maximum = cone
        .iter()
        .zip(magnitudes)
        .filter(|(in_cone, magnitude)| **in_cone && inside < cone.len() && **magnitude < outside_maximum)
        .count();
    // Sweep every threshold from above: predicting "cone" for magnitude >= t.
    let mut order: Vec<usize> = (0..cone.len()).collect();
    order.sort_by(|a, b| magnitudes[*b].cmp(&magnitudes[*a]));
    let mut misclassified = inside;
    let mut least = misclassified;
    let mut at = 0usize;
    while at < order.len() {
        let magnitude = magnitudes[order[at]];
        let mut end = at;
        while end < order.len() && magnitudes[order[end]] == magnitude {
            if cone[order[end]] {
                misclassified -= 1;
            } else {
                misclassified += 1;
            }
            end += 1;
        }
        least = least.min(misclassified);
        at = end;
    }
    NativeMagnitudeControl {
        cone_minimum: if inside > 0 { cone_minimum } else { 0 },
        cone_maximum,
        outside_minimum: if inside < cone.len() { outside_minimum } else { 0 },
        outside_maximum,
        outside_above_cone_minimum,
        cone_below_outside_maximum,
        least_misclassified_by_threshold: least,
        threshold_determines_cone: least == 0,
    }
}

impl<'residence, 'chart> NativeFullOperatorSession<'residence, 'chart> {
    /// Found the ecology for dissection: the terminal carriers are retained for excitation and no
    /// return deposits.
    pub fn found_for_dissection(
        ecology: &'residence NativeFullOperatorEcology,
        residence: &'residence mut NativeOperatorResidence<'chart>,
        aperture: NativeDissectionAperture,
    ) -> Result<Self, NativeFullOperationError> {
        let mut session = Self::found(ecology, residence)?;
        session.dissection = Some(DissectionStanding::found(aperture));
        Ok(session)
    }

    pub fn dissection_aperture(&self) -> Option<NativeDissectionAperture> {
        self.dissection.as_ref().map(|standing| standing.aperture)
    }

    /// The excited face of the last cycle, once `excite` has read it.
    pub fn excited_face(&self) -> Option<&NativeReceiverFace> {
        self.dissection.as_ref().and_then(|standing| standing.face.as_ref())
    }

    pub fn site_support(&self, population: NativeTensorOrdinal) -> Option<&NativeSiteSupport> {
        self.dissection
            .as_ref()
            .and_then(|standing| standing.supports.get(&population))
    }

    /// Every contraction population in graph order with its operation and layer.
    pub fn contraction_populations(&self) -> Vec<(NativeTensorOrdinal, u32, Option<u16>)> {
        self.ecology
            .operations
            .iter()
            .filter(|operation| matches!(operation.primitive, NativeOperationPrimitive::Contract))
            .filter_map(|operation| {
                operation
                    .coefficients
                    .first()
                    .map(|population| (*population, operation.ordinal, operation.layer))
            })
            .collect()
    }

    /// The last row of a tiled carrier, stitched.
    pub(super) fn tiled_last_row(&self, carrier: &TiledCarrier<'chart>) -> Result<Vec<(i64, i64)>, NativeFullOperationError> {
        let surface = self.residence.surface();
        let mut row = Vec::with_capacity(carrier.width);
        for section in &carrier.sections {
            let tile = surface.read_out(section)?;
            let width = section.width();
            row.extend_from_slice(&tile[(carrier.rows - 1) * width..]);
        }
        Ok(row)
    }

    /// Excite the completed cycle at its own selected face: the differential of that face's
    /// normalized exponential probability at the last row returns through every reaction without
    /// depositing, and the excitation is read per site at every contraction population.
    pub fn excite(&mut self) -> Result<NativeExcitationTrace, NativeFullOperationError> {
        let started = std::time::Instant::now();
        let aperture = self
            .dissection
            .as_ref()
            .ok_or(NativeFullOperationError::Occurrence)?
            .aperture;
        if !self.cycle_complete {
            return Err(NativeFullOperationError::Occurrence);
        }
        let (rows, width, face) = {
            let emission = self.terminal_carrier.as_ref().ok_or(NativeFullOperationError::Occurrence)?;
            let last_row = self.tiled_last_row(emission)?;
            let face = face_of_last_row(&last_row, 1, emission.width)
                .ok_or(NativeFullOperationError::Operation)?;
            (emission.rows, emission.width, face)
        };
        let tied_output = self
            .terminal_contracted
            .clone()
            .ok_or(NativeFullOperationError::Occurrence)?;
        let differential = {
            let (Some(emission), Some(reacted), Some(presented)) = (
                self.terminal_carrier.as_ref(),
                self.terminal_reacted.as_ref(),
                self.terminal_presented.as_ref(),
            ) else {
                return Err(NativeFullOperationError::Occurrence);
            };
            let next = vec![face.selected; rows];
            let surface = self.residence.surface();
            let returned = receiver_differential(
                surface,
                ReturnMaterial {
                    emission: &emission.sections,
                    reacted: &reacted.sections,
                    presented: &presented.section,
                    presented_octaves: presented.bound_octaves,
                    rows: emission.rows,
                    width: emission.width,
                    grain: emission.grain,
                },
                &next,
                SeriesAperture(aperture.series_terms),
            )?;
            // The receiver is the face at the terminal position alone: every earlier row's
            // differential is withdrawn.
            if rows > 1 {
                let shape = surface.shape_withdraw_rows(rows, width, returned.octaves, 0, rows - 1)?;
                let out = surface.fresh_section(rows, width, returned.section.grain())?;
                let mut builder = surface.begin_passage(&[vec![]])?;
                {
                    let lane = builder.open(0, &[])?;
                    surface.record_withdraw_rows(&lane, &returned.section, 0, rows - 1, &out)?;
                }
                builder.close(0, &out, shape.needed)?;
                let reading = builder.finish()?.launch()?;
                let octaves = operation_bound(u32::MAX, &reading)?;
                ReturnedDifferential {
                    section: out,
                    octaves,
                }
            } else {
                returned
            }
        };
        if let Some(standing) = self.dissection.as_mut() {
            standing.clear();
            standing.face = Some(face.clone());
        }
        let trace = self.adjoint_return(differential, ReturnDeed::Dissect(tied_output))?;
        let supports = self
            .dissection
            .as_ref()
            .map(|standing| {
                standing
                    .supports
                    .values()
                    .map(|support| NativeSiteSupportSummary {
                        population: support.population,
                        operation: support.operation,
                        layer: support.layer,
                        sites: support.sites,
                        support_population: support.support_population,
                    })
                    .collect()
            })
            .unwrap_or_default();
        Ok(NativeExcitationTrace {
            face,
            operations_returned: trace.operations_returned,
            layers_replayed: trace.layers_replayed,
            supports,
            elapsed_milliseconds: started.elapsed().as_millis(),
        })
    }

    /// Read the excitation at one contraction's output per site beside the forward's own output.
    /// Called by the return in the dissection deed; `tied_output` stands in for the tied
    /// population, whose output the terminal branch keeps apart from the carriers.
    pub(super) fn record_site_support(
        &mut self,
        population: NativeTensorOrdinal,
        operation: &NativeOperatorNode,
        dy: &ResidentSection<'chart>,
        tied_output: Option<&[(i64, i64)]>,
    ) -> Result<(), NativeFullOperationError> {
        let surface = self.residence.surface();
        let intervals = surface.read_out(dy)?;
        let (rows, width) = (dy.rows(), dy.width());
        let (support, magnitudes, contributions) = match tied_output {
            Some(output) => read_sites(&intervals, rows, width, output, 1),
            None => {
                let output = self
                    .carriers
                    .get(&operation.output)
                    .ok_or(NativeFullOperationError::Carrier)?;
                let forward = surface.read_out(&output.section)?;
                read_sites(&intervals, rows, width, &forward, output.section.rows())
            }
        };
        if magnitudes.len() != width {
            return Err(NativeFullOperationError::Adjoint(format!(
                "the forward output of operation {} does not carry the differential's {} sites",
                operation.ordinal, width
            )));
        }
        let support_population = support.iter().filter(|site| **site).count();
        let standing = self
            .dissection
            .as_mut()
            .ok_or(NativeFullOperationError::Occurrence)?;
        standing.supports.insert(
            population,
            NativeSiteSupport {
                population: population.0,
                operation: operation.ordinal,
                layer: operation.layer,
                sites: width,
                support,
                support_population,
                magnitudes,
                contributions,
            },
        );
        Ok(())
    }

    /// The face under one joint withdrawal: the selected sites of every touched contraction
    /// population are zeroed at its output at every position, and the cycle is enacted again
    /// from the earliest touched segment on the retained checkpoints through the terminal
    /// boundary.  The session's own carriers, checkpoints, and terminal face are untouched.
    pub fn face_under_withdrawals(
        &mut self,
        selection: &NativeSiteSelection,
    ) -> Result<NativeWithdrawnFace, NativeFullOperationError> {
        let started = std::time::Instant::now();
        let original = self
            .dissection
            .as_ref()
            .and_then(|standing| standing.face.clone())
            .ok_or(NativeFullOperationError::Occurrence)?;
        if !self.cycle_complete {
            return Err(NativeFullOperationError::Occurrence);
        }
        let rows = self
            .previous_context
            .clone()
            .ok_or(NativeFullOperationError::Occurrence)?;
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
        // Every contraction touched, by index; the earliest decides where the replay starts.
        let mut targets: BTreeMap<usize, NativeTensorOrdinal> = BTreeMap::new();
        let mut populations_withdrawn = 0usize;
        for (index, operation) in self.ecology.operations.iter().enumerate() {
            if !matches!(operation.primitive, NativeOperationPrimitive::Contract) {
                continue;
            }
            let Some(population) = operation.coefficients.first().copied() else {
                continue;
            };
            let sites = self
                .ecology
                .coefficient_populations
                .get(population.0 as usize)
                .and_then(|descriptor| descriptor.shape.first().copied())
                .ok_or(NativeFullOperationError::Operation)?;
            if let Some(withdrawn) = selection.withdrawn_of(population) {
                if withdrawn.len() != sites {
                    return Err(NativeFullOperationError::Operation);
                }
                if selection.touches(population) {
                    targets.insert(index, population);
                    populations_withdrawn += 1;
                }
            }
        }
        let mask = self.residence.surface().mount_site_mask(&selection.withdrawn)?;
        let earliest = targets.keys().next().copied().unwrap_or(0);
        let start = if earliest >= terminal_start {
            terminal_start
        } else {
            match self.ecology.operations[earliest].layer {
                Some(layer) => self
                    .ecology
                    .operations
                    .iter()
                    .position(|operation| operation.layer == Some(layer))
                    .ok_or(NativeFullOperationError::Operation)?,
                None if earliest < first_layer_operation => 0,
                None => self
                    .ecology
                    .operations
                    .iter()
                    .enumerate()
                    .position(|(index, operation)| {
                        index >= first_layer_operation && operation.layer.is_none()
                    })
                    .ok_or(NativeFullOperationError::Operation)?,
            }
        };
        self.carriers.clear();
        // The withdrawals, keyed by the ordinal of the contraction whose output they intervene on,
        // recorded inside the segments: no section crosses to the host for them.
        let mut withdrawals: BTreeMap<u32, SegmentWithdrawal<'_, 'chart>> = BTreeMap::new();
        for (index, population) in &targets {
            if *index >= terminal_start {
                continue;
            }
            if let Some(offset) = selection.offset_of(*population) {
                withdrawals.insert(
                    self.ecology.operations[*index].ordinal,
                    SegmentWithdrawal { mask: &mask, offset },
                );
            }
        }
        // A counterfactual: the session's checkpoints are not overwritten by withdrawn carriers.
        let steps = self.enact_run(start, terminal_start, &rows, &withdrawals, false, false)?;
        drop(withdrawals);
        let mut enacted = steps.len();
        let boundary = self.ecology.operations[terminal_start..].to_vec();
        // When nothing before the boundary is enacted, the tied contraction reads the carrier the
        // cycle presented, which the successor holds apart from the checkpoints: lend it.
        let tied_input = boundary[0].inputs[0];
        let lent = if start == terminal_start {
            match self.terminal_presented.take() {
                Some(presented) => {
                    self.carriers.insert(tied_input, presented);
                    true
                }
                None => false,
            }
        } else {
            false
        };
        let tied_offset = targets
            .get(&terminal_start)
            .and_then(|population| selection.offset_of(*population));
        let tied_withdrawal = tied_offset.map(|offset| SegmentWithdrawal { mask: &mask, offset });
        let outcome = self.terminal_face(&boundary, tied_withdrawal.as_ref());
        drop(tied_withdrawal);
        if lent {
            self.terminal_presented = self.carriers.remove(&tied_input);
        }
        self.carriers.clear();
        drop(mask);
        let face = outcome?;
        enacted += 5;
        Ok(NativeWithdrawnFace {
            populations_withdrawn,
            withdrawn: selection.withdrawn_population(),
            selected_unchanged: face.selected == original.selected,
            exact_unchanged: face.exact_digest == original.exact_digest,
            face,
            operations_enacted: enacted,
            elapsed_milliseconds: started.elapsed().as_millis(),
        })
    }

    /// The face under one population's withdrawal alone.
    pub fn face_under_withdrawal(
        &mut self,
        population: NativeTensorOrdinal,
        withdrawn: &[bool],
    ) -> Result<NativeWithdrawnFace, NativeFullOperationError> {
        self.face_under_withdrawals(&NativeSiteSelection::single(population, withdrawn))
    }

    /// The blueprint's first letter, kept as the control that refuted it: one population's
    /// support withdrawn alone, and its complement withdrawn alone.
    pub fn cone_controls(
        &mut self,
        population: NativeTensorOrdinal,
    ) -> Result<NativeConeVerdict, NativeFullOperationError> {
        let support = self
            .site_support(population)
            .cloned()
            .ok_or(NativeFullOperationError::Operation)?;
        let complement: Vec<bool> = support.support.iter().map(|site| !site).collect();
        let outside_withdrawn = self.face_under_withdrawal(population, &complement)?;
        let inside_withdrawn = self.face_under_withdrawal(population, &support.support)?;
        let magnitude = magnitude_control(&support.support, &support.magnitudes);
        let outside_unchanged = outside_withdrawn.selected_unchanged;
        let inside_changed = !inside_withdrawn.selected_unchanged;
        Ok(NativeConeVerdict {
            population: population.0,
            operation: support.operation,
            layer: support.layer,
            sites: support.sites,
            support_population: support.support_population,
            outside_withdrawn,
            inside_withdrawn,
            outside_unchanged,
            inside_changed,
            founded: outside_unchanged && inside_changed,
            magnitude,
        })
    }

    /// Read the completed cycle's face into the dissection standing without a return: what a
    /// probe under a withdrawal compares against.  The supports are cleared.
    pub fn read_face(&mut self) -> Result<NativeReceiverFace, NativeFullOperationError> {
        if !self.cycle_complete {
            return Err(NativeFullOperationError::Occurrence);
        }
        let face = {
            let emission = self.terminal_carrier.as_ref().ok_or(NativeFullOperationError::Occurrence)?;
            let last_row = self.tiled_last_row(emission)?;
            face_of_last_row(&last_row, 1, emission.width).ok_or(NativeFullOperationError::Operation)?
        };
        let standing = self.dissection.as_mut().ok_or(NativeFullOperationError::Occurrence)?;
        standing.clear();
        standing.face = Some(face.clone());
        Ok(face)
    }

    /// The site counts of every contraction population the excitation read.
    pub fn site_sizes(&self) -> BTreeMap<NativeTensorOrdinal, usize> {
        self.dissection
            .as_ref()
            .map(|standing| {
                standing
                    .supports
                    .iter()
                    .map(|(population, support)| (*population, support.sites))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// The first-order contribution of every site the excitation read, per population.
    pub fn site_contributions(&self) -> BTreeMap<NativeTensorOrdinal, Vec<u128>> {
        self.dissection
            .as_ref()
            .map(|standing| {
                standing
                    .supports
                    .iter()
                    .map(|(population, support)| (*population, support.contributions.clone()))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// The cone by joint intervention along the excitation's own order: every site of every
    /// contraction population ordered by its first-order contribution.
    pub fn cone_by_intervention(&mut self) -> Result<NativeConeReturn, NativeFullOperationError> {
        let (sizes, mut order) = {
            let standing = self
                .dissection
                .as_ref()
                .ok_or(NativeFullOperationError::Occurrence)?;
            let mut sizes: BTreeMap<NativeTensorOrdinal, usize> = BTreeMap::new();
            let mut order: Vec<(u128, u32, u32)> = Vec::new();
            for (population, support) in &standing.supports {
                sizes.insert(*population, support.sites);
                for (site, contribution) in support.contributions.iter().enumerate() {
                    order.push((*contribution, population.0, site as u32));
                }
            }
            (sizes, order)
        };
        order.sort_unstable();
        let order: Vec<(NativeTensorOrdinal, u32)> = order
            .into_iter()
            .map(|(_, population, site)| (NativeTensorOrdinal(population), site))
            .collect();
        self.cone_along_order(&order, &sizes, None)
    }

    /// The cone by joint intervention along a declared order of sites, with a fixed population
    /// withdrawn in every probe.  The search finds the largest prefix of the order whose joint
    /// withdrawal (with the fixed population) leaves the selected face unchanged; the cone is
    /// the remaining suffix.  The complement withdrawn and the cone withdrawn close it; the
    /// boundary site is withdrawn alone; the restriction to every population carries its exact
    /// sites and magnitude control (magnitudes are those of the standing when the excitation was
    /// read, zero when only the face was read).
    pub fn cone_along_order(
        &mut self,
        order: &[(NativeTensorOrdinal, u32)],
        sizes: &BTreeMap<NativeTensorOrdinal, usize>,
        fixed: Option<&NativeSiteSelection>,
    ) -> Result<NativeConeReturn, NativeFullOperationError> {
        let started = std::time::Instant::now();
        let face = self
            .excited_face()
            .cloned()
            .ok_or(NativeFullOperationError::Occurrence)?;
        let total = order.len();
        let selection_of = |from: usize, to: usize| {
            let mut selection = NativeSiteSelection::founded(sizes);
            if let Some(fixed) = fixed {
                selection.absorb(fixed);
            }
            for (population, site) in &order[from..to] {
                selection.withdraw(*population, *site as usize);
            }
            selection
        };
        let mut probes: Vec<NativeConeProbe> = Vec::new();
        let mut probe = |this: &mut Self, withdrawn: usize| -> Result<bool, NativeFullOperationError> {
            let returned = this.face_under_withdrawals(&selection_of(0, withdrawn))?;
            probes.push(NativeConeProbe {
                withdrawn,
                face_selected: returned.face.selected,
                selected_unchanged: returned.selected_unchanged,
                exact_unchanged: returned.exact_unchanged,
                elapsed_milliseconds: returned.elapsed_milliseconds,
            });
            Ok(returned.selected_unchanged)
        };
        let carried = !probe(self, total)?;
        let mut lo = 0usize;
        let mut hi = total;
        if carried {
            while hi - lo > 1 {
                let mid = lo + (hi - lo) / 2;
                if probe(self, mid)? {
                    lo = mid;
                } else {
                    hi = mid;
                }
            }
        } else {
            lo = total;
        }
        let monotone = probes.iter().all(|left| {
            probes
                .iter()
                .all(|right| left.withdrawn >= right.withdrawn || left.selected_unchanged || !right.selected_unchanged)
        });
        let complement_withdrawn = self.face_under_withdrawals(&selection_of(0, lo))?;
        let cone_only = {
            let mut selection = NativeSiteSelection::founded(sizes);
            for (population, site) in &order[lo..total] {
                selection.withdraw(*population, *site as usize);
            }
            selection
        };
        let cone_withdrawn = self.face_under_withdrawals(&cone_only)?;
        let boundary = if carried && lo < total {
            let (population, site) = order[lo];
            let (contribution, magnitude) = self
                .site_support(population)
                .map(|support| {
                    (
                        support.contributions.get(site as usize).copied().unwrap_or(0),
                        support.magnitudes.get(site as usize).copied().unwrap_or(0),
                    )
                })
                .unwrap_or((0, 0));
            let mut alone = NativeSiteSelection::founded(sizes);
            alone.withdraw(population, site as usize);
            let alone = self.face_under_withdrawals(&alone)?;
            Some(NativeConeBoundary {
                population: population.0,
                site,
                contribution,
                magnitude,
                alone,
            })
        } else {
            None
        };
        let mut restrictions = Vec::with_capacity(sizes.len());
        for (population, sites) in sizes {
            let cone: Vec<bool> = cone_only
                .withdrawn_of(*population)
                .map(<[bool]>::to_vec)
                .unwrap_or_else(|| vec![false; *sites]);
            let (operation, layer, magnitudes) = self
                .site_support(*population)
                .map(|support| (support.operation, support.layer, support.magnitudes.clone()))
                .unwrap_or((u32::MAX, None, vec![0u64; *sites]));
            restrictions.push(NativeConeRestriction {
                population: population.0,
                operation,
                layer,
                sites: *sites,
                cone_population: cone.iter().filter(|site| **site).count(),
                magnitude: magnitude_control(&cone, &magnitudes),
                cone,
            });
        }
        Ok(NativeConeReturn {
            face,
            sites: total,
            cone_population: total - lo,
            complement_population: lo,
            carried,
            probes,
            monotone,
            complement_withdrawn,
            cone_withdrawn,
            boundary,
            restrictions,
            elapsed_milliseconds: started.elapsed().as_millis(),
        })
    }

    /// The terminal boundary of a counterfactual, tile by tile in one passage each: the tied
    /// contraction (withdrawn inside the passage when the tied population is touched), the
    /// soft-cap reactions, the emission, and the face of its last row, read once.
    fn terminal_face(
        &mut self,
        boundary: &[NativeOperatorNode],
        tied_withdrawal: Option<&SegmentWithdrawal<'_, 'chart>>,
    ) -> Result<NativeReceiverFace, NativeFullOperationError> {
        let run = self.enact_terminal(boundary, tied_withdrawal, [false, false, false, false, true])?;
        let emitted = run
            .carriers
            .last()
            .and_then(Option::as_ref)
            .ok_or(NativeFullOperationError::Operation)?;
        let last_row = self.tiled_last_row(emitted)?;
        face_of_last_row(&last_row, 1, emitted.width).ok_or(NativeFullOperationError::Operation)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_face_is_the_greatest_midpoint_first_of_equals() {
        let face = face_of_last_row(&[(0, 0), (9, 9), (1, 1), (4, 6), (5, 5), (2, 2)], 2, 3).unwrap();
        assert_eq!(face.selected, 0);
        assert_eq!(face.equal_population, 2);
        assert_eq!(face.width, 3);
    }

    #[test]
    fn a_threshold_fails_when_a_larger_magnitude_lies_outside_the_cone() {
        let control = magnitude_control(&[true, false, true, false], &[5, 9, 3, 1]);
        assert_eq!(control.outside_above_cone_minimum, 1);
        assert_eq!(control.cone_below_outside_maximum, 2);
        assert_eq!(control.least_misclassified_by_threshold, 1);
        assert!(!control.threshold_determines_cone);
        let separable = magnitude_control(&[true, false, true, false], &[5, 2, 3, 1]);
        assert_eq!(separable.least_misclassified_by_threshold, 0);
        assert!(separable.threshold_determines_cone);
    }

    #[test]
    fn the_sites_read_support_magnitude_and_first_order_contribution() {
        let differential = [(0, 0), (2, 2), (0, 0), (-3, -3), (0, 0), (0, 0)];
        let forward = [(5, 5), (1, 1), (7, 7), (2, 2), (-4, -4), (9, 9)];
        let (support, magnitudes, contributions) = read_sites(&differential, 2, 3, &forward, 2);
        assert_eq!(support, vec![true, true, false]);
        assert_eq!(magnitudes, vec![5, 4, 9]);
        assert_eq!(contributions, vec![6, 2, 0]);
        // One forward row reads against the differential's last row alone.
        let (_, magnitudes, contributions) = read_sites(&differential, 2, 3, &[(1, 1), (1, 1), (1, 1)], 1);
        assert_eq!(magnitudes, vec![1, 1, 1]);
        assert_eq!(contributions, vec![3, 0, 0]);
    }

    #[test]
    fn a_selection_withdraws_by_population_offset() {
        let sizes = BTreeMap::from([(NativeTensorOrdinal(3), 2usize), (NativeTensorOrdinal(7), 3usize)]);
        let mut selection = NativeSiteSelection::founded(&sizes);
        assert!(selection.withdraw(NativeTensorOrdinal(7), 1));
        assert!(!selection.withdraw(NativeTensorOrdinal(7), 3));
        assert!(!selection.withdraw(NativeTensorOrdinal(9), 0));
        assert_eq!(selection.withdrawn_of(NativeTensorOrdinal(3)), Some(&[false, false][..]));
        assert_eq!(selection.withdrawn_of(NativeTensorOrdinal(7)), Some(&[false, true, false][..]));
        assert!(!selection.touches(NativeTensorOrdinal(3)));
        assert!(selection.touches(NativeTensorOrdinal(7)));
        assert_eq!(selection.offset_of(NativeTensorOrdinal(7)), Some(2));
        assert_eq!(selection.withdrawn_population(), 1);
    }
}
