//! Exact ownership of a receiving map with independently charted operand blocks.
//!
//! The joined physical map is a cache, never an aggregate normal law. Its phase
//! statistic belongs to the full normalized comparison, including cross-block terms.
//! Its feature is [source/sigma_source, context/sigma_context]; its map is the
//! concatenation of the internal maps. Each block ridge is consequently internal.
use super::receiving_blocks::{ReceivingLayout, ReceivingOperandChart};
use super::*;

const RECEIVING_CHART_HEADER: &str = "receiving-chart passage-relative-read-and-target-v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceivingBlock {
    chart: Option<ReceivingOperandChart>,
    law: NormalLaw,
}

impl ReceivingBlock {
    pub fn chart(&self) -> Option<&ReceivingOperandChart> {
        self.chart.as_ref()
    }
    pub fn law(&self) -> &NormalLaw {
        &self.law
    }
    pub fn width(&self) -> usize {
        self.law.map.columns()
    }

    /// Convert a direction (not only the current map) back into physical units.
    pub fn physical_direction(
        &self,
        direction: &ExactRatMatrix,
    ) -> Result<ExactRatMatrix, HnnError> {
        if direction.rows() != self.law.map.rows() || direction.columns() != self.width() {
            return Err(HnnError::Unadmitted {
                reason: "a receiving block direction has its law's shape",
            });
        }
        match &self.chart {
            Some(chart) => chart.physical_map(direction),
            None if direction.entries().iter().all(Zero::is_zero) => Ok(direction.clone()),
            None => Err(HnnError::Unadmitted {
                reason: "an unfounded receiving block cannot publish a nonzero direction",
            }),
        }
    }

    pub(super) fn prepared_physical_direction(
        &self,
        prepared: &PreparedStep,
    ) -> Result<ExactRatMatrix, HnnError> {
        self.physical_direction(&rows_matrix(&prepared.unit.scaled_rows(&Rat::one())))
    }

    fn pristine_law(
        rows: usize,
        width: usize,
        prior: u32,
        carrier: crate::hnn::receiving::ReceivingCarrier,
    ) -> Result<NormalLaw, HnnError> {
        let mut law = NormalLaw::with_receiving_prior(ExactRatMatrix::zero(rows, width)?, prior);
        law.carrier = carrier;
        // Independent conditional block laws must never absorb conditional phase targets.
        law.phase = None;
        Ok(law)
    }

    fn validate(&self) -> Result<(), HnnError> {
        if self.width() == 0
            || self.law.map.rows() == 0
            || self.law.map.rows() % 2 != 0
            || self.law.phase.is_some()
            || self.law.symmetry.is_some()
            || self.law.receiving_prior.is_none()
            || match self.law.epoch_law() {
                Some(epoch)=>epoch.map.rows!=self.law.map.rows() || epoch.map.columns!=self.width()
                    || epoch.gram.rows!=self.width() || epoch.gram.columns!=self.width()
                    || epoch.news.rows!=self.law.map.rows() || epoch.news.columns!=self.width(),
                None=>self.law.gram.len()!=self.width() || self.law.gram.iter().any(|row|row.len()!=self.width()),
            }
            || self
                .law
                .map_carry
                .0
                .keys()
                .any(|&index| index >= self.law.map.entries().len())
            || self
                .law
                .gram_carry
                .0
                .keys()
                .any(|&index| index / self.width().max(1) >= self.width())
        {
            return Err(HnnError::Unadmitted {
                reason: "a receiving block has a positive realified shape, its own prior, and no conditional phase statistic",
            });
        }
        if let Some(chart) = &self.chart {
            if chart.width() != self.width() {
                return Err(HnnError::Unadmitted {
                    reason: "a receiving operand chart has its block's width",
                });
            }
        } else if self.law
            != Self::pristine_law(
                self.law.map.rows(),
                self.width(),
                self.law.receiving_prior().unwrap(),
                self.law.carrier,
            )?
        {
            return Err(HnnError::Unadmitted {
                reason: "an unfounded receiving block keeps its pristine zero law",
            });
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ReceivingMaterial {
    Single(NormalLaw),
    ArrivalContext {
        source_width: usize,
        return_policy: crate::hnn::receiving::RetainedReturnPolicy,
        blocks: [ReceivingBlock; 2],
        published: ExactRatMatrix,
        shared_phase: PhaseStatistics,
    },
}

impl ReceivingMaterial {
    pub(super) fn laws(&self) -> Vec<&NormalLaw> {
        match self {
            Self::Single(law) => vec![law],
            Self::ArrivalContext { blocks, .. } => blocks.iter().map(|block| &block.law).collect(),
        }
    }

    /// Scoped internal mutation: callers must rebuild the physical publication after
    /// changing maps, and must preserve the frozen chart and shared phase objective.
    pub(super) fn laws_mut(&mut self) -> Vec<&mut NormalLaw> {
        match self {
            Self::Single(law) => vec![law],
            Self::ArrivalContext { blocks, .. } => {
                blocks.iter_mut().map(|block| &mut block.law).collect()
            }
        }
    }

    pub(super) fn on_lattice(&self, lattice: &Lattice) -> bool {
        self.laws().into_iter().all(|law| law.on_lattice(lattice))
    }

    pub(super) fn chart_coordinate_storage(&self) -> ChartCoordinateStorage {
        let mut storage = ChartCoordinateStorage::default();
        for law in self.laws() {
            storage.add(&law.chart_coordinate_storage());
        }
        storage
    }

    /// Canonical blank for material identity. Each declared founding prior, the
    /// layout and carrier survive; observed statistics and operand scales do not.
    pub(super) fn founding(&self) -> Self {
        let blank = |law: &NormalLaw| {
            let mut blank = NormalLaw::with_receiving_prior(
                law.map.scaled(&Rat::zero()),
                law.receiving_prior().unwrap_or(0),
            );
            blank.carrier = law.carrier;
            blank
        };
        match self {
            Self::Single(law) => Self::Single(blank(law)),
            Self::ArrivalContext {
                source_width,
                blocks,
                published,
                ..
            } => {
                let blocks = std::array::from_fn(|i| {
                    let mut law = blank(&blocks[i].law);
                    law.phase = None;
                    ReceivingBlock { chart: None, law }
                });
                Self::ArrivalContext {
                    source_width: *source_width,
                    return_policy: self.return_policy(),
                    blocks,
                    published: published.scaled(&Rat::zero()),
                    shared_phase: PhaseStatistics::founded(
                        published.rows() / 2,
                        published.columns(),
                    ),
                }
            }
        }
    }

    fn concatenate(
        left: &ExactRatMatrix,
        right: &ExactRatMatrix,
    ) -> Result<ExactRatMatrix, HnnError> {
        if left.rows() != right.rows() {
            return Err(HnnError::Unadmitted {
                reason: "receiving physical blocks have equal row counts",
            });
        }
        let columns = left
            .columns()
            .checked_add(right.columns())
            .ok_or(HnnError::CountOverflow)?;
        let rows = left
            .to_rows()
            .into_iter()
            .zip(right.to_rows())
            .map(|(mut a, b)| {
                a.extend(b);
                a
            })
            .collect();
        Ok(ExactRatMatrix::shaped(left.rows(), columns, rows)?)
    }

    /// Carried map residual in physical coordinates, not receipt-index coordinates.
    pub(super) fn map_remainder(&self) -> Result<ExactRatMatrix, HnnError> {
        match self {
            Self::Single(law) => Ok(law.map_remainder()),
            Self::ArrivalContext { blocks, .. } => Self::concatenate(
                &blocks[0].physical_direction(&blocks[0].law.map_remainder())?,
                &blocks[1].physical_direction(&blocks[1].law.map_remainder())?,
            ),
        }
    }

    /// Quantize each internal carry on the internal lattice FIRST, then convert
    /// the resulting direction to physical units. Rounding physical coefficients
    /// on this lattice would change the admitted precision event.
    pub(super) fn promoted_remainder(&self, finer: &Lattice) -> Result<ExactRatMatrix, HnnError> {
        let promote = |law: &NormalLaw| -> Result<ExactRatMatrix, HnnError> {
            flat_matrix(
                law.map.rows(),
                law.map.columns(),
                law.map_remainder()
                    .entries()
                    .iter()
                    .map(|value| {
                        let (quotient, _) = finer.div_rem(value);
                        Rat::from_integer(quotient) * finer.unit()
                    })
                    .collect(),
            )
        };
        match self {
            Self::Single(law) => promote(law),
            Self::ArrivalContext { blocks, .. } => Self::concatenate(
                &blocks[0].physical_direction(&promote(&blocks[0].law)?)?,
                &blocks[1].physical_direction(&promote(&blocks[1].law)?)?,
            ),
        }
    }

    /// Receipts use full joined INTERNAL row-major indices. The Gram occupies
    /// its two diagonal blocks; cross-block Gram entries are not law carriers.
    pub(super) fn carried_remainders(&self) -> Vec<(Carrier, usize, Rat)> {
        let mut result = Vec::new();
        for (block_index, law) in self.laws().into_iter().enumerate() {
            let width = law.map.columns();
            for (array, carry) in [
                (Carrier::Map, &law.map_carry),
                (Carrier::Gram, &law.gram_carry),
            ] {
                for (&index, value) in &carry.0 {
                    let index = match self {
                        Self::Single(_) => index,
                        Self::ArrivalContext { source_width, .. } => {
                            let offset = block_index * source_width;
                            let (row, column) = (index / width, index % width);
                            let row = if array == Carrier::Gram {
                                row + offset
                            } else {
                                row
                            };
                            row * (2 * source_width) + column + offset
                        }
                    };
                    result.push((array, index, value.clone()));
                }
            }
        }
        result
    }

    /// Add one indexed internal receipt to its map/Gram entry, for the exact
    /// carried trajectory. Does not add to the carry a second time. This reading
    /// operation is not an admitted learning step or a solved-chart recertification.
    #[cfg(test)]
    pub(super) fn add_remainder(
        &mut self,
        array: Carrier,
        index: usize,
        value: &Rat,
    ) -> Result<(), HnnError> {
        if !matches!(array, Carrier::Map | Carrier::Gram) {
            return Err(HnnError::Unadmitted {
                reason: "receiving remainders address only maps and Grams",
            });
        }
        let (law, local) = match self {
            Self::Single(law) => (law, index),
            Self::ArrivalContext {
                source_width,
                blocks,
                ..
            } => {
                let width = source_width.checked_mul(2).ok_or(HnnError::CountOverflow)?;
                if width == 0 {
                    return Err(HnnError::Unadmitted {
                        reason: "a receiving remainder has positive joined width",
                    });
                }
                let (row, column) = (index / width, index % width);
                let block_index = column / *source_width;
                let offset = block_index * *source_width;
                let local_row = if array == Carrier::Gram {
                    if row / *source_width != block_index {
                        return Err(HnnError::Unadmitted {
                            reason: "a receiving Gram remainder belongs to a diagonal operand block",
                        });
                    }
                    row - offset
                } else {
                    row
                };
                let law = &mut blocks[block_index].law;
                let rows = if array == Carrier::Gram {
                    *source_width
                } else {
                    law.map.rows()
                };
                if local_row >= rows {
                    return Err(HnnError::Unadmitted {
                        reason: "a receiving remainder index stays within its block",
                    });
                }
                (law, local_row * *source_width + column - offset)
            }
        };
        if array == Carrier::Map {
            let mut entries = law.map.entries().to_vec();
            let expected = entries.len();
            let entry = entries.get_mut(local).ok_or(HnnError::Shape {
                what: "a receiving map remainder index",
                expected,
                found: local,
            })?;
            *entry += value;
            law.map = flat_matrix(law.map.rows(), law.map.columns(), entries)?;
        } else {
            let width = law.gram.len();
            if width == 0 || local / width >= width {
                return Err(HnnError::Unadmitted {
                    reason: "a receiving Gram remainder index stays within its block",
                });
            }
            law.gram[local / width][local % width] += value;
        }
        // Gram changes are diagnostic only; rebuilding the physical map does not
        // claim that the old solved chart certifies that modified Gram.
        self.rebuild_published()
    }

    #[cfg(test)]
    pub(super) fn clear_carries(&mut self) -> Result<(), HnnError> {
        for law in self.laws_mut() {
            law.map_carry = Carry::default();
            law.gram_carry = Carry::default();
        }
        self.rebuild_published()
    }

    /// F1 receiving read and target-phase coordinates are versioned together.
    /// The normal-law payload is unchanged, but an old untagged receiving material
    /// is not compatible with this chart. None/source-law encodings are unchanged.
    pub(super) fn write_optional(s: &mut String, key: &str, material: Option<&Self>) {
        if material.is_some() {
            *s += RECEIVING_CHART_HEADER;
            s.push('\n');
        }
        match material {
            None => write_optional_law(s, key, None),
            Some(Self::Single(law)) => write_optional_law(s, key, Some(law)),
            Some(Self::ArrivalContext {
                source_width,
                blocks,
                shared_phase,
                ..
            }) => {
                let carrier = match blocks[0].law.carrier {
                    crate::hnn::receiving::ReceivingCarrier::Anchor => "anchor",
                    crate::hnn::receiving::ReceivingCarrier::SourceObserver => "source-observer",
                };
                let tag = if material.unwrap().return_policy() == crate::hnn::receiving::RetainedReturnPolicy::FamilyLocalRetainedReturnV1 { "arrival-context-family-local-v1" } else { "arrival-context-v1" };
                *s += &format!("{key} {tag} {source_width} {carrier}\n");
                for (index, block) in blocks.iter().enumerate() {
                    let scale = block
                        .chart
                        .as_ref()
                        .map_or_else(|| "none".to_owned(), |chart| chart.scale().to_string());
                    *s += &format!("operand-chart {index} {scale}\n");
                    if block.law.epoch_law().is_some() {
                        // The canonical normal payload owns its map. As with a Single
                        // law, an empty envelope must not serialize its derived view.
                        *s += &format!("receiving-block {index} 0 0\n");
                    } else {
                        *s += &format!(
                            "receiving-block {index} {} {}\n",
                            block.law.map.rows(),
                            block.width()
                        );
                        write_rows(s, &block.law.map);
                    }
                    write_law(s, &block.law);
                }
                write_phase(s, shared_phase);
                *s += "end-arrival-context-v1\n";
            }
        }
    }

    /// Read a present material only in the explicit passage-relative F1 chart.
    /// Untagged earlier receiving maps/phase history are refused, even with a valid
    /// outer checksum. Archival inspection requires the corresponding older codec.
    /// The block order, dimensions, chart scales and shared phase shape are checked;
    /// neither a missing block nor a missing shared statistic can be fabricated.
    pub(super) fn read_optional(
        lines: &mut std::str::Lines<'_>,
        key: &str,
        what: &'static str,
        budget: &mut epoch::CheckpointReadBudget,
    ) -> Result<Option<Self>, HnnError> {
        if lines.clone().next() == Some(format!("{key} none").as_str()) {
            return read_optional_law(lines, key, what, budget).map(|law| law.map(Self::Single));
        }
        if next(lines, "the receiving read and target phase chart")? != RECEIVING_CHART_HEADER {
            return refuse(
                "the receiving read and target phase chart (requires passage-relative-read-and-target-v1)",
            );
        }
        let line = lines
            .clone()
            .next()
            .ok_or(HnnError::ContinuingState { what })?;
        let words = head(line, key, what)?;
        if !matches!(words.first().map(String::as_str),Some("arrival-context-v1"|"arrival-context-family-local-v1")) {
            return read_optional_law(lines, key, what, budget).map(|law| law.map(Self::Single));
        }
        let [_, width, carrier] = words.as_slice() else {
            return refuse("the versioned receiving material header");
        };
        let return_policy = if words[0] == "arrival-context-family-local-v1" { crate::hnn::receiving::RetainedReturnPolicy::FamilyLocalRetainedReturnV1 } else { crate::hnn::receiving::RetainedReturnPolicy::PopulationMixtureSectionV1 };
        let source_width = number(Some(width), "the receiving source width")?;
        if source_width == 0 || source_width.checked_mul(2).is_none() {
            return refuse("the receiving source width");
        }
        let carrier = match carrier.as_str() {
            "anchor" => crate::hnn::receiving::ReceivingCarrier::Anchor,
            "source-observer" => crate::hnn::receiving::ReceivingCarrier::SourceObserver,
            _ => return refuse("the receiving carrier identity"),
        };
        lines.next();
        let mut read_block = |index: usize| -> Result<ReceivingBlock, HnnError> {
            let chart_head = head(
                next(lines, "a receiving operand chart")?,
                "operand-chart",
                "a receiving operand chart",
            )?;
            let [ordinal, scale] = chart_head.as_slice() else {
                return refuse("a receiving operand chart");
            };
            if number(Some(ordinal), "a receiving operand ordinal")? != index {
                return refuse("the receiving operand order");
            }
            let chart = if scale == "none" {
                None
            } else {
                let scale = scale
                    .parse::<Rat>()
                    .map_err(|_| HnnError::ContinuingState {
                        what: "a receiving operand scale",
                    })?;
                Some(
                    ReceivingOperandChart::from_parts(source_width, scale).map_err(|_| {
                        HnnError::ContinuingState {
                            what: "a receiving operand scale",
                        }
                    })?,
                )
            };
            let shape = head(
                next(lines, "a receiving block map")?,
                "receiving-block",
                "a receiving block map",
            )?;
            let [ordinal, rows, columns] = shape.as_slice() else {
                return refuse("a receiving block map shape");
            };
            let rows_count = number(Some(rows), "the receiving block rows")?;
            let columns_count = number(Some(columns), "the receiving block columns")?;
            let canonical_envelope = (rows_count, columns_count) == (0, 0);
            if number(Some(ordinal), "a receiving block ordinal")? != index
                || (!canonical_envelope
                    && (columns_count != source_width || rows_count == 0 || rows_count % 2 != 0))
            {
                return refuse("a receiving block's order or shape");
            }
            let map = read_rows(lines, &shape[1..], "a receiving block map")?;
            // The generic canonical parser applies its full checkpoint budget and
            // map/Gram/news shape checks. Legacy payloads still preflight their
            // Gram width before that parser allocates it.
            let law_head = lines.clone().next().ok_or(HnnError::ContinuingState {
                    what: "a receiving block Gram",
                })?;
            if canonical_envelope != law_head.starts_with("epoch-law ") {
                return refuse("a receiving block's canonical map envelope");
            }
            if !canonical_envelope {
                let gram_head = head(law_head, "gram", "a receiving block Gram")?;
                if gram_head.len() != 1
                    || number(gram_head.first(), "a receiving block Gram")? != source_width
                {
                    return refuse("a receiving block Gram width");
                }
            }
            let mut law = read_law(lines, map, budget)?;
            law.carrier = carrier;
            let block = ReceivingBlock { chart, law };
            if block.width() != source_width {
                return refuse("a receiving block's restored width");
            }
            block.validate().map_err(|_| HnnError::ContinuingState {
                what: "a receiving block's material invariants",
            })?;
            Ok(block)
        };
        let blocks = [read_block(0)?, read_block(1)?];
        let published = Self::joined_map(&blocks).map_err(|_| HnnError::ContinuingState {
            what: "the joined receiving physical map",
        })?;
        let shared_phase = read_phase(lines, &published)?.ok_or(HnnError::ContinuingState {
            what: "the joined receiving shared phase statistic",
        })?;
        if next(lines, "the joined receiving end marker")? != "end-arrival-context-v1" {
            return refuse("the joined receiving end marker");
        }
        let material = Self::ArrivalContext {
            source_width,
            return_policy,
            blocks,
            published,
            shared_phase,
        };
        material.validate().map_err(|_| HnnError::ContinuingState {
            what: "the joined receiving material invariants",
        })?;
        Ok(Some(material))
    }

    /// Split only a pristine zero receiving law; no existing evidence is reset.
    /// Widths count real matrix columns, and both are explicit at this boundary.
    pub(super) fn arrival_context(
        law: NormalLaw,
        source_width: usize,
        context_width: usize,
    ) -> Result<Self, HnnError> {
        let width = source_width
            .checked_add(context_width)
            .ok_or(HnnError::CountOverflow)?;
        if source_width == 0
            || context_width != source_width
            || law.map.columns() != width
            || law.map.rows() == 0
            || law.map.rows() % 2 != 0
        {
            return Err(HnnError::Unadmitted {
                reason: "a joined receiving law has equal explicit positive source and context widths and realified rows",
            });
        }
        let prior = law.receiving_prior().ok_or(HnnError::Unadmitted {
            reason: "a joined receiving law is founded from a receiving prior",
        })?;
        let mut pristine =
            NormalLaw::with_receiving_prior(ExactRatMatrix::zero(law.map.rows(), width)?, prior);
        pristine.carrier = law.carrier;
        if law != pristine {
            return Err(HnnError::Unadmitted {
                reason: "receiving blocks can only be declared on a pristine zero receiving law",
            });
        }
        let block = |n| -> Result<ReceivingBlock, HnnError> {
            Ok(ReceivingBlock {
                chart: None,
                law: ReceivingBlock::pristine_law(law.map.rows(), n, prior, law.carrier)?,
            })
        };
        let result = Self::ArrivalContext {
            source_width,
            return_policy: crate::hnn::receiving::RetainedReturnPolicy::PopulationMixtureSectionV1,
            blocks: [block(source_width)?, block(context_width)?],
            shared_phase: PhaseStatistics::founded(law.map.rows() / 2, width),
            published: law.map,
        };
        result.validate()?;
        Ok(result)
    }

    pub(super) fn return_policy(&self) -> crate::hnn::receiving::RetainedReturnPolicy {
        match self { Self::Single(_) => crate::hnn::receiving::RetainedReturnPolicy::PopulationMixtureSectionV1,
            Self::ArrivalContext { return_policy, .. } => *return_policy }
    }
    pub(super) fn bind_family_local_return(&mut self) -> Result<(), HnnError> {
        if self != &self.founding() || self.return_policy() != crate::hnn::receiving::RetainedReturnPolicy::PopulationMixtureSectionV1 {
            return Err(HnnError::Unadmitted { reason: "family-local return is declared only on fresh receiving material" });
        }
        match self { Self::ArrivalContext { return_policy, .. } => *return_policy=crate::hnn::receiving::RetainedReturnPolicy::FamilyLocalRetainedReturnV1,
            _ => return Err(HnnError::Unadmitted { reason: "family-local return requires explicit arrival/context material" }) }
        Ok(())
    }

    pub(super) fn map(&self) -> &ExactRatMatrix {
        match self {
            Self::Single(law) => law.map(),
            Self::ArrivalContext { published, .. } => published,
        }
    }
    pub(super) fn layout(&self) -> ReceivingLayout {
        match self {
            Self::Single(_) => ReceivingLayout::Single,
            Self::ArrivalContext { source_width, .. } => ReceivingLayout::ArrivalContext {
                source_width: *source_width,
            },
        }
    }
    pub(super) fn carrier(&self) -> crate::hnn::receiving::ReceivingCarrier {
        match self {
            Self::Single(law) => law.carrier(),
            Self::ArrivalContext { blocks, .. } => blocks[0].law.carrier(),
        }
    }
    pub(super) fn single(&self) -> Option<&NormalLaw> {
        match self {
            Self::Single(law) => Some(law),
            _ => None,
        }
    }
    pub(super) fn single_mut(&mut self) -> Option<&mut NormalLaw> {
        match self {
            Self::Single(law) => Some(law),
            _ => None,
        }
    }
    pub(super) fn carrier_bits(&self) -> CarrierBits {
        match self {
            Self::Single(law) => law.carrier_bits(),
            Self::ArrivalContext {
                blocks,
                published,
                shared_phase,
                ..
            } => {
                let mut count = CarrierBits::default();
                count.entries += u64::from(self.return_policy()==crate::hnn::receiving::RetainedReturnPolicy::FamilyLocalRetainedReturnV1);
                for block in blocks {
                    count.add(block.law.carrier_bits());
                    count.entries += block.chart.as_ref().map_or(0, |chart| bits(chart.scale()));
                }
                // The physical publication is retained too; do not hide its storage.
                count.entries +=
                    published.entries().iter().map(bits).sum::<u64>() + shared_phase.bits();
                count
            }
        }
    }

    pub(super) fn blocks(&self) -> Option<&[ReceivingBlock; 2]> {
        match self {
            Self::ArrivalContext { blocks, .. } => Some(blocks),
            _ => None,
        }
    }
    pub(super) fn phase_statistics(&self) -> Option<&PhaseStatistics> {
        match self {
            Self::Single(law) => law.phase_statistics(),
            Self::ArrivalContext { shared_phase, .. } => Some(shared_phase),
        }
    }

    fn joined_map(blocks: &[ReceivingBlock; 2]) -> Result<ExactRatMatrix, HnnError> {
        for block in blocks {
            block.validate()?;
        }
        if blocks[0].law.map.rows() != blocks[1].law.map.rows()
            || blocks[0].law.carrier != blocks[1].law.carrier
        {
            return Err(HnnError::Unadmitted {
                reason: "receiving blocks share their output rows and carrier identity",
            });
        }
        let left = blocks[0].physical_direction(blocks[0].law.map())?;
        let right = blocks[1].physical_direction(blocks[1].law.map())?;
        let rows = left
            .to_rows()
            .into_iter()
            .zip(right.to_rows())
            .map(|(mut a, b)| {
                a.extend(b);
                a
            })
            .collect();
        Ok(ExactRatMatrix::new(rows)?)
    }

    /// Validate cache equality exactly; never silently repair a malformed owner.
    pub(super) fn validate(&self) -> Result<(), HnnError> {
        if let Self::ArrivalContext {
            source_width,
            blocks,
            published,
            shared_phase,
            ..
        } = self
        {
            if *source_width != blocks[0].width()
                || blocks[1].width() != *source_width
                || shared_phase.features() != published.columns()
                || shared_phase.classes().checked_mul(2) != Some(published.rows())
                || Self::joined_map(blocks)? != *published
            {
                return Err(HnnError::Unadmitted {
                    reason: "a joined receiving publication and shared phase statistic have exactly their blocks' physical shape and map",
                });
            }
        }
        Ok(())
    }

    /// Rebuild only the publication, without touching any law or shared statistic.
    pub(super) fn rebuild_published(&mut self) -> Result<(), HnnError> {
        if let Self::ArrivalContext {
            blocks, published, ..
        } = self
        {
            *published = Self::joined_map(blocks)?;
        }
        self.validate()
    }

    /// First nonzero operand founds each chart once. A zero block stays pristine.
    /// Failure leaves the owner unchanged.
    pub(super) fn found_operand_charts(&mut self, feature: &[Rat]) -> Result<(), HnnError> {
        if feature.len() != self.map().columns() {
            return Err(HnnError::Shape {
                what: "a full receiving operand",
                expected: self.map().columns(),
                found: feature.len(),
            });
        }
        self.validate()?;
        let mut next = self.clone();
        if let Self::ArrivalContext {
            source_width,
            blocks,
            ..
        } = &mut next
        {
            let (source, context) = feature.split_at(*source_width);
            for (block, operand) in blocks.iter_mut().zip([source, context]) {
                if block.chart.is_none() {
                    block.chart = ReceivingOperandChart::from_feature(operand)?;
                }
            }
        }
        next.rebuild_published()?;
        *self = next;
        Ok(())
    }

    /// Slice physical operands, retaining the same full-output comparison covector.
    /// Call founding first; a nonzero operand cannot pass through an unfounded block.
    pub(super) fn block_samples(
        &self,
        index: usize,
        samples: &[Sample],
    ) -> Result<Vec<Sample>, HnnError> {
        self.validate()?;
        let Self::ArrivalContext {
            source_width,
            blocks,
            ..
        } = self
        else {
            return Err(HnnError::Unadmitted {
                reason: "block samples require joined receiving material",
            });
        };
        let block = blocks.get(index).ok_or(HnnError::Unadmitted {
            reason: "a joined receiving material has exactly two blocks",
        })?;
        let start = if index == 0 { 0 } else { *source_width };
        samples.iter().map(|sample| {
            if sample.feature.len() != self.map().columns() || sample.covector.len() != self.map().rows() || sample.weight.is_negative() {
                return Err(HnnError::Unadmitted { reason: "a receiving block sample has the full physical shape and nonnegative weight" });
            }
            let operand = &sample.feature[start..start + block.width()];
            let feature = match &block.chart {
                Some(chart) => chart.feature(operand)?,
                None if operand.iter().all(Zero::is_zero) => operand.to_vec(),
                None => return Err(HnnError::Unadmitted { reason: "a nonzero receiving operand must found its block before slicing" }),
            };
            Ok(Sample { feature, covector: sample.covector.clone(), weight: sample.weight.clone(), masses: sample.masses.clone() })
        }).collect()
    }

    /// Replace jointly certified block successors and derive their physical publication.
    /// This method provides no certificate: the caller owns the joined acceptance.
    pub(super) fn with_block_laws(&self, laws: [NormalLaw; 2]) -> Result<Self, HnnError> {
        self.validate()?;
        let mut next = self.clone();
        let Self::ArrivalContext { blocks, .. } = &mut next else {
            return Err(HnnError::Unadmitted {
                reason: "block successors require joined receiving material",
            });
        };
        for (block, law) in blocks.iter_mut().zip(laws) {
            if law.map.rows() != block.law.map.rows()
                || law.map.columns() != block.width()
                || law.carrier != block.law.carrier
            {
                return Err(HnnError::Unadmitted {
                    reason: "a receiving block successor preserves its shape and carrier",
                });
            }
            block.law = law;
        }
        next.rebuild_published()?;
        Ok(next)
    }

    /// Absorb at the full producing normalized map, once, before any block moves.
    /// Cross-block Gram entries and the unconditional lifted targets are retained.
    pub(super) fn absorb_full_phase(&mut self, samples: &[Sample]) -> Result<(), HnnError> {
        self.validate()?;
        for sample in samples {
            if sample.feature.len() != self.map().columns()
                || sample.covector.len() != self.map().rows()
                || sample.weight.is_negative()
            {
                return Err(HnnError::Unadmitted {
                    reason: "a full receiving phase sample has the physical shape and nonnegative weight",
                });
            }
        }
        let (map, normalized);
        let samples: &[Sample] = if let Self::ArrivalContext { blocks, .. } = &*self {
            let left = self.block_samples(0, samples)?;
            let right = self.block_samples(1, samples)?;
            normalized = left
                .into_iter()
                .zip(right)
                .map(|(mut a, b)| {
                    a.feature.extend(b.feature);
                    a
                })
                .collect::<Vec<_>>();
            let rows = blocks[0]
                .law
                .map
                .to_rows()
                .into_iter()
                .zip(blocks[1].law.map.to_rows())
                .map(|(mut a, b)| {
                    a.extend(b);
                    a
                })
                .collect();
            map = ExactRatMatrix::new(rows)?;
            &normalized
        } else {
            map = self.map().clone();
            samples
        };
        let phase = match self {
            Self::Single(law) => law.phase.as_mut(),
            Self::ArrivalContext { shared_phase, .. } => Some(shared_phase),
        };
        if let Some(phase) = phase {
            let mut next = phase.clone();
            absorb_phase(&mut next, &map, samples)?;
            *phase = next;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::integer;

    fn owner() -> ReceivingMaterial {
        let mut law = NormalLaw::with_receiving_prior(ExactRatMatrix::zero(2, 4).unwrap(), 1);
        law.carrier = crate::hnn::receiving::ReceivingCarrier::SourceObserver;
        ReceivingMaterial::arrival_context(law, 2, 2).unwrap()
    }

    #[test]
    fn receiving_material_precision_rounds_internal_carries_before_uncharting() {
        let mut material = owner();
        material
            .found_operand_charts(&[integer(2), integer(2), integer(8), integer(8)])
            .unwrap();
        let retained = Rat::new(3.into(), 16.into());
        material.laws_mut()[1]
            .map_carry
            .0
            .insert(1, retained.clone());
        let finer = Lattice::new(3);
        let (quotient, _) = finer.div_rem(&retained);
        let expected = Rat::from_integer(quotient) * finer.unit() / integer(8);
        assert!(!expected.is_zero());
        assert_eq!(
            material.map_remainder().unwrap().get(0, 3),
            Ok(&(retained / integer(8)))
        );
        assert_eq!(
            material.promoted_remainder(&finer).unwrap().get(0, 3),
            Ok(&expected)
        );
        assert!(material.on_lattice(&finer));
        let mut storage = ChartCoordinateStorage::default();
        for law in material.laws() {
            storage.add(&law.chart_coordinate_storage());
        }
        assert_eq!(material.chart_coordinate_storage(), storage);
    }

    #[test]
    fn receiving_material_receipts_use_joined_internal_indices_and_checked_inverse() {
        let mut material = owner();
        material
            .found_operand_charts(&[integer(2), integer(2), integer(8), integer(8)])
            .unwrap();
        {
            let mut laws = material.laws_mut();
            laws[0].map_carry.0.insert(3, integer(1));
            laws[1].map_carry.0.insert(1, integer(2));
            laws[0].gram_carry.0.insert(2, integer(3));
            laws[1].gram_carry.0.insert(1, integer(4));
        }
        let carried = material.carried_remainders();
        assert!(carried.contains(&(Carrier::Map, 5, integer(1))));
        assert!(carried.contains(&(Carrier::Map, 3, integer(2))));
        assert!(carried.contains(&(Carrier::Gram, 4, integer(3))));
        assert!(carried.contains(&(Carrier::Gram, 11, integer(4))));
        assert!(
            material
                .add_remainder(Carrier::Gram, 2, &integer(1))
                .is_err()
        );
        assert!(
            material
                .add_remainder(Carrier::Map, 8, &integer(1))
                .is_err()
        );
        for (array, index, value) in carried {
            material.add_remainder(array, index, &value).unwrap();
        }
        assert_eq!(material.map().get(1, 1), Ok(&Rat::new(1.into(), 2.into())));
        assert_eq!(material.map().get(0, 3), Ok(&Rat::new(1.into(), 4.into())));
        assert_eq!(material.laws()[0].gram[1][0], integer(3));
        assert_eq!(material.laws()[1].gram[0][1], integer(4));
        material.clear_carries().unwrap();
        assert!(material.carried_remainders().is_empty());
        let blank = material.founding();
        assert_eq!(blank, owner());
        blank.validate().unwrap();
    }

    #[test]
    fn receiving_material_single_codec_versions_the_read_and_target_chart() {
        let law = NormalLaw::with_receiving_prior(ExactRatMatrix::zero(2, 4).unwrap(), 1);
        let material = ReceivingMaterial::Single(law.clone());
        let (mut legacy, mut encoded) = (String::new(), String::new());
        write_optional_law(&mut legacy, "receiving", Some(&law));
        ReceivingMaterial::write_optional(&mut encoded, "receiving", Some(&material));
        assert_eq!(encoded, format!("{RECEIVING_CHART_HEADER}\n{legacy}"));
        assert!(
            ReceivingMaterial::read_optional(
                &mut legacy.lines(),
                "receiving",
                "test receiving",
                &mut epoch::CheckpointReadBudget::new(1 << 20)
            )
            .is_err()
        );
        assert_eq!(
            ReceivingMaterial::read_optional(
                &mut encoded.lines(),
                "receiving",
                "test receiving",
                &mut epoch::CheckpointReadBudget::new(1 << 20)
            )
            .unwrap(),
            Some(material)
        );
        legacy.clear();
        encoded.clear();
        write_optional_law(&mut legacy, "receiving", None);
        ReceivingMaterial::write_optional(&mut encoded, "receiving", None);
        assert_eq!(encoded, legacy);
        assert_eq!(
            ReceivingMaterial::read_optional(
                &mut encoded.lines(),
                "receiving",
                "test receiving",
                &mut epoch::CheckpointReadBudget::new(1 << 20)
            )
            .unwrap(),
            None
        );
    }

    #[test]
    fn receiving_material_joined_codec_preserves_frozen_charts_and_shared_phase() {
        let mut material = owner();
        material
            .found_operand_charts(&[integer(2), integer(2), integer(8), integer(8)])
            .unwrap();
        let mut laws = (*material.blocks().unwrap()).clone().map(|b| b.law);
        laws[0].map = rows_matrix(&[vec![integer(2), integer(0)], vec![integer(0), integer(2)]]);
        laws[1].map = rows_matrix(&[vec![integer(8), integer(0)], vec![integer(0), integer(8)]]);
        material = material.with_block_laws(laws).unwrap();
        material
            .absorb_full_phase(&[Sample {
                feature: vec![integer(2), integer(4), integer(8), integer(16)],
                covector: vec![integer(0), integer(1)],
                weight: integer(1),
                masses: Some(vec![integer(1)]),
            }])
            .unwrap();
        let mut encoded = String::new();
        ReceivingMaterial::write_optional(&mut encoded, "receiving", Some(&material));
        encoded += "next-owner\n";
        let mut lines = encoded.lines();
        let restored = ReceivingMaterial::read_optional(
            &mut lines,
            "receiving",
            "test receiving",
            &mut epoch::CheckpointReadBudget::new(1 << 20),
        )
        .unwrap()
        .unwrap();
        assert_eq!(restored, material);
        assert_eq!(lines.next(), Some("next-owner"));
        for malformed in [
            encoded.replacen("arrival-context-v1", "arrival-context-v2", 1),
            encoded.replacen("operand-chart 0 2", "operand-chart 0 3", 1),
            encoded.replacen("receiving-block 1 2 2", "receiving-block 1 2 3", 1),
            encoded.replacen("source-observer", "unknown-carrier", 1),
            encoded.replacen("end-arrival-context-v1", "end-arrival-context-v2", 1),
        ] {
            assert!(
                ReceivingMaterial::read_optional(
                    &mut malformed.lines(),
                    "receiving",
                    "test receiving",
                    &mut epoch::CheckpointReadBudget::new(1 << 20)
                )
                .is_err()
            );
        }
    }

    #[test]
    fn receiving_material_joined_codec_keeps_zero_blocks_unfounded() {
        let mut material = owner();
        material
            .found_operand_charts(&[integer(2), integer(2), integer(0), integer(0)])
            .unwrap();
        let mut encoded = String::new();
        ReceivingMaterial::write_optional(&mut encoded, "receiving", Some(&material));
        assert!(encoded.contains("operand-chart 1 none\n"));
        assert_eq!(
            ReceivingMaterial::read_optional(
                &mut encoded.lines(),
                "receiving",
                "test receiving",
                &mut epoch::CheckpointReadBudget::new(1 << 20)
            )
            .unwrap(),
            Some(material)
        );
    }

    #[test]
    fn receiving_material_founds_only_nonzero_blocks_once_and_keeps_carrier() {
        let mut material = owner();
        let tiny = Rat::new(1.into(), 1024.into());
        material
            .found_operand_charts(&[tiny.clone(), tiny.clone(), Rat::zero(), Rat::zero()])
            .unwrap();
        let blocks = material.blocks().unwrap();
        assert_eq!(blocks[0].chart().unwrap().scale(), &tiny);
        assert!(blocks[1].chart().is_none());
        assert!(blocks.iter().all(|b| b.law().phase_statistics().is_none()));
        assert_eq!(
            material.carrier(),
            crate::hnn::receiving::ReceivingCarrier::SourceObserver
        );
        material
            .found_operand_charts(&[integer(128), Rat::zero(), integer(4), integer(4)])
            .unwrap();
        assert_eq!(
            material.blocks().unwrap()[0].chart().unwrap().scale(),
            &tiny
        );
        assert_eq!(
            material.blocks().unwrap()[1].chart().unwrap().scale(),
            &integer(4)
        );
        material.validate().unwrap();
    }

    #[test]
    fn receiving_material_rejects_nonpristine_and_bad_widths() {
        let nonzero = NormalLaw::with_receiving_prior(
            rows_matrix(&[vec![integer(1), integer(0)], vec![integer(0), integer(0)]]),
            0,
        );
        assert!(ReceivingMaterial::arrival_context(nonzero, 1, 1).is_err());
        let zero = NormalLaw::with_receiving_prior(ExactRatMatrix::zero(2, 3).unwrap(), 0);
        assert!(ReceivingMaterial::arrival_context(zero.clone(), 1, 1).is_err());
        assert!(ReceivingMaterial::arrival_context(zero, 0, 3).is_err());
        let mut learned = NormalLaw::with_receiving_prior(ExactRatMatrix::zero(2, 2).unwrap(), 0);
        learned.gram[0][0] += integer(1);
        assert!(ReceivingMaterial::arrival_context(learned, 1, 1).is_err());
    }

    #[test]
    fn receiving_material_publication_and_samples_preserve_full_logits() {
        let mut material = owner();
        material
            .found_operand_charts(&[integer(2), integer(2), integer(8), integer(8)])
            .unwrap();
        let mut laws = (*material.blocks().unwrap()).clone().map(|b| b.law);
        laws[0].map = rows_matrix(&[vec![integer(2), integer(4)], vec![integer(6), integer(8)]]);
        laws[1].map = rows_matrix(&[vec![integer(16), integer(0)], vec![integer(24), integer(0)]]);
        let material = material.with_block_laws(laws).unwrap();
        assert_eq!(
            material.map(),
            &rows_matrix(&[
                vec![integer(1), integer(2), integer(2), integer(0)],
                vec![integer(3), integer(4), integer(3), integer(0)]
            ])
        );
        let sample = Sample {
            feature: vec![integer(5), integer(7), integer(11), integer(0)],
            covector: vec![integer(0), integer(1)],
            weight: integer(1),
            masses: Some(vec![integer(1)]),
        };
        let a = material.block_samples(0, &[sample.clone()]).unwrap();
        let b = material.block_samples(1, &[sample.clone()]).unwrap();
        let blocks = material.blocks().unwrap();
        let a = blocks[0].law.map.apply(&a[0].feature).unwrap();
        let b = blocks[1].law.map.apply(&b[0].feature).unwrap();
        assert_eq!(
            material.map().apply(&sample.feature).unwrap(),
            a.iter().zip(b).map(|(a, b)| a + b).collect::<Vec<_>>()
        );
    }

    #[test]
    fn receiving_material_shared_phase_keeps_cross_block_terms_and_full_target() {
        let mut material = owner();
        material
            .found_operand_charts(&[integer(2), integer(2), integer(8), integer(8)])
            .unwrap();
        let mut laws = (*material.blocks().unwrap()).clone().map(|b| b.law);
        laws[0].map = rows_matrix(&[vec![integer(0), integer(0)], vec![integer(2), integer(0)]]);
        laws[1].map = rows_matrix(&[vec![integer(0), integer(0)], vec![integer(8), integer(0)]]);
        material = material.with_block_laws(laws).unwrap();
        let sample = Sample {
            feature: vec![integer(2), integer(3), integer(5), integer(0)],
            covector: vec![integer(0), integer(1)],
            weight: integer(1),
            masses: Some(vec![integer(1)]),
        };
        let mut expected = PhaseStatistics::founded(1, 4);
        // Full phase output is 2+5=7; doubled target is 7+4=11.
        expected
            .absorb(
                &integer(1),
                &[
                    integer(1),
                    Rat::new(3.into(), 2.into()),
                    Rat::new(5.into(), 8.into()),
                    integer(0),
                ],
                &[integer(1)],
                &[integer(11)],
            )
            .unwrap();
        material.absorb_full_phase(&[sample]).unwrap();
        assert_eq!(material.phase_statistics(), Some(&expected));
        assert_eq!(
            material.phase_statistics().unwrap().gram(0)[0][2],
            Rat::new(5.into(), 8.into())
        );
        assert!(
            material
                .blocks()
                .unwrap()
                .iter()
                .all(|b| b.law.phase.is_none())
        );
    }
    #[test]
    fn family_local_native_material_tag_roundtrip_and_fresh_only() {
        use crate::hnn::receiving::RetainedReturnPolicy;
        let law=NormalLaw::with_receiving_prior(ExactRatMatrix::zero(4,4).unwrap(),0);
        let mut material=ReceivingMaterial::arrival_context(law,2,2).unwrap();
        material.bind_family_local_return().unwrap();
        assert_eq!(material.return_policy(),RetainedReturnPolicy::FamilyLocalRetainedReturnV1);
        assert!(material.bind_family_local_return().is_err());
        let mut text=String::new();ReceivingMaterial::write_optional(&mut text,"receiving",Some(&material));
        assert!(text.contains("arrival-context-family-local-v1"));
        let mut budget=epoch::CheckpointReadBudget::new(1<<30);
        let restored=ReceivingMaterial::read_optional(&mut text.lines(),"receiving","family local test",&mut budget).unwrap().unwrap();
        assert_eq!(restored,material);
    }

}
