//! Transient, exact prefix counts for one field-clocked passage.
//!
//! The input-selected clock is established by exact translation prefixes, preserving the actual
//! source phases, ticks, carry and held-pair addresses. Counts then have no cross-cell arithmetic
//! dependency: each source-ring/phase/class slot has its own sparse prefix lane and is materialized
//! independently. The scan is never serialized or retained by `SourceMoment`.

use super::*;
use rayon::prelude::*;
use std::collections::BTreeMap;

#[derive(Clone, Debug)]
struct CellAddress {
    class: usize,
    phases: Vec<usize>,
    cumulative_ticks: Vec<u64>,
    earlier: Vec<Option<usize>>,
    lift_after: Vec<BigInt>,
    carry_out: bool,
}

#[derive(Clone, Debug, Default)]
struct RingLanes {
    first: BTreeMap<usize, Vec<usize>>,
    offset: Vec<BTreeMap<usize, Vec<usize>>>,
}

/// A transient prefix scan of source counts. Prefix `i` means the opening plus the first `i`
/// admitted cells; the consumed prefix ends at the first actual joint-clock carry-out, if any.
#[derive(Clone, Debug)]
pub(crate) struct EpochMomentScan {
    opening: SourceMoment,
    clock_opening: Vec<BigInt>,
    events: Vec<CellAddress>,
    lanes: Vec<RingLanes>,
    has_advances: bool,
}

impl SourceMoment {
    /// Establish the field's true clock/address passage, then build grouped exact count prefixes.
    /// The first aeon carry closes the scan exactly as it closes [`SourceMoment::ingest`].
    pub(crate) fn scan_epoch(
        &self,
        field: &Field,
        current: &Current,
        encoded: &Encoded,
    ) -> Result<EpochMomentScan, HnnError> {
        self.scan_epoch_partitioned(field, current, encoded, rayon::current_num_threads())
    }

    /// Explicit lane partition for exact host/oracle checks; it changes scheduling only.
    fn scan_epoch_partitioned(
        &self,
        field: &Field,
        current: &Current,
        encoded: &Encoded,
        partitions: usize,
    ) -> Result<EpochMomentScan, HnnError> {
        field.admit(encoded)?;
        if partitions == 0 {
            return Err(HnnError::Unadmitted {
                reason: "an input prefix needs a nonzero lane partition",
            });
        }
        if self.rings.iter().any(|ring| ring.leaky.is_some()) {
            return Err(HnnError::Unadmitted {
                reason: "the lossless epoch count scan does not admit leaky source counts",
            });
        }

        let mut clock = current.clone();
        let mut recent = self.window();
        let mut cumulative_ticks = self.rings.iter().map(|ring| ring.ticks).collect::<Vec<_>>();
        let mut events = Vec::new();
        // A tile is one declared cell-clock period, not a source-length retained cut.
        // If no carry occurs, the next tile opens on the previous tile's full lift.
        let tile_cells = usize::try_from(field.cell_clock_period())
            .unwrap_or(usize::MAX)
            .max(1);
        let mut tile = Vec::new();
        for (at, class) in encoded.classes_read().enumerate() {
            let next_cells = u64::try_from(events.len())
                .map_err(|_| HnnError::CountOverflow)?
                .checked_add(1)
                .ok_or(HnnError::CountOverflow)?;
            self.cells
                .checked_add(next_cells)
                .ok_or(HnnError::CountOverflow)?;
            self.clock_cells
                .checked_add(next_cells)
                .ok_or(HnnError::CountOverflow)?;
            if at % tile_cells == 0 {
                let end = at.saturating_add(tile_cells).min(encoded.len());
                tile = field.scan_input_selected(clock.lift(), encoded, at..end, partitions)?;
            }
            let (lift, step) = &tile[at % tile_cells];
            field.check_occurrence_square(clock.lift(), lift, encoded, at)?;
            clock = Current::at(field, lift.clone())?;
            let mut phases = Vec::with_capacity(self.rings.len());
            for (index, ring) in self.rings.iter().enumerate() {
                let phase = usize::try_from(clock.phase(field, ring.ring)?)
                    .map_err(|_| HnnError::CountOverflow)?;
                let ticks = *step.ticks.get(ring.ring).ok_or(HnnError::RingOutside {
                    ring: ring.ring,
                    rings: step.ticks.len(),
                })?;
                cumulative_ticks[index] = cumulative_ticks[index]
                    .checked_add(ticks)
                    .ok_or(HnnError::CountOverflow)?;
                phases.push(phase);
            }
            let earlier = self
                .offsets
                .iter()
                .map(|&offset| {
                    offset
                        .checked_sub(1)
                        .and_then(|i| recent.get(i).copied().flatten())
                })
                .collect();
            recent.insert(0, Some(class));
            recent.truncate(self.offsets.iter().copied().max().unwrap_or(0));
            events.push(CellAddress {
                class,
                phases,
                cumulative_ticks: cumulative_ticks.clone(),
                earlier,
                lift_after: clock.lift().to_vec(),
                carry_out: step.carry_out,
            });
            if step.carry_out {
                break;
            }
        }

        let mut lanes = Vec::with_capacity(self.rings.len());
        for ring_index in 0..self.rings.len() {
            let mut first = events
                .par_iter()
                .enumerate()
                .map(|(at, event)| {
                    let slot = event.phases[ring_index] * self.alphabet + event.class;
                    (slot, at)
                })
                .collect::<Vec<_>>();
            first.par_sort_unstable_by_key(|&(slot, at)| (slot, at));
            let first = slot_events(first);

            let offset = self
                .offsets
                .iter()
                .enumerate()
                .map(|(offset_index, _)| {
                    let mut entries = events
                        .par_iter()
                        .enumerate()
                        .filter_map(|(at, event)| {
                            event.earlier[offset_index].map(|earlier| {
                                let slot = event.phases[ring_index] * self.alphabet * self.alphabet
                                    + event.class * self.alphabet
                                    + earlier;
                                (slot, at)
                            })
                        })
                        .collect::<Vec<_>>();
                    entries.par_sort_unstable_by_key(|&(slot, at)| (slot, at));
                    slot_events(entries)
                })
                .collect();
            lanes.push(RingLanes { first, offset });
        }

        Ok(EpochMomentScan {
            opening: self.clone(),
            clock_opening: current.lift().to_vec(),
            events,
            lanes,
            has_advances: encoded.has_advances(),
        })
    }
}

impl EpochMomentScan {
    /// Number of cells actually consumed before the caller's request ended or the field carried.
    pub(crate) fn consumed(&self) -> usize {
        self.events.len()
    }

    /// Whether the consumed prefix reached the field's joint-clock carry-out.
    pub(crate) fn carry_out(&self) -> bool {
        self.events.last().is_some_and(|event| event.carry_out)
    }

    /// Exact source moment after the first `prefix` cells. Prefixes beyond the consumed interval
    /// are refused, including cells after a joint-clock carry-out.
    pub(crate) fn moment_at(&self, prefix: usize) -> Result<SourceMoment, HnnError> {
        if prefix > self.events.len() {
            return Err(HnnError::Unadmitted {
                reason: "the requested moment prefix lies beyond the admitted carry boundary",
            });
        }
        let mut moment = self.opening.clone();
        for (ring_index, counts) in moment.rings.iter_mut().enumerate() {
            apply_lane_prefix(&mut counts.first, &self.lanes[ring_index].first, prefix)?;
            for offset_index in 0..counts.offset.len() {
                apply_lane_prefix(
                    &mut counts.offset[offset_index],
                    &self.lanes[ring_index].offset[offset_index],
                    prefix,
                )?;
            }
            if prefix != 0 {
                let last = &self.events[prefix - 1];
                counts.end = last.phases[ring_index] as u64;
                counts.ticks = last.cumulative_ticks[ring_index];
            }
        }
        for event in self.events.iter().take(prefix) {
            if !moment.window.is_empty() {
                moment.window[moment.cursor] = Some(event.class);
                moment.cursor = (moment.cursor + 1) % moment.window.len();
            }
        }
        let prefix = u64::try_from(prefix).map_err(|_| HnnError::CountOverflow)?;
        moment.cells = moment
            .cells
            .checked_add(prefix)
            .ok_or(HnnError::CountOverflow)?;
        moment.clock_cells = moment
            .clock_cells
            .checked_add(prefix)
            .ok_or(HnnError::CountOverflow)?;
        moment.located |= prefix != 0 && self.has_advances;
        // These caches are derived from counts and ports. A materialized prefix starts with no
        // cached face, so no face bound to the opening counts can be mistaken for this prefix.
        moment.pair_faces = ResidentPairFaces::default();
        moment.marginal_faces = ResidentMarginalFaces::default();
        Ok(moment)
    }

    /// The current lift after the first `prefix` events; this is address state, not a per-cell
    /// moment or constitutive snapshot.
    pub(crate) fn current_at(&self, field: &Field, prefix: usize) -> Result<Current, HnnError> {
        if prefix > self.events.len() {
            return Err(HnnError::Unadmitted {
                reason: "the requested clock prefix lies beyond the admitted carry boundary",
            });
        }
        let lift = if prefix == 0 {
            self.clock_opening.clone()
        } else {
            self.events[prefix - 1].lift_after.clone()
        };
        Current::at(field, lift)
    }

    /// The exact source moment after all consumed cells.
    pub(crate) fn post_moment(&self) -> Result<SourceMoment, HnnError> {
        self.moment_at(self.consumed())
    }

    /// The field clock after all consumed cells.
    pub(crate) fn post_current(&self, field: &Field) -> Result<Current, HnnError> {
        self.current_at(field, self.consumed())
    }
}

fn slot_events(entries: Vec<(usize, usize)>) -> BTreeMap<usize, Vec<usize>> {
    let mut slots: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for (slot, at) in entries {
        slots.entry(slot).or_default().push(at);
    }
    slots
}

fn apply_lane_prefix(
    counts: &mut [u64],
    lanes: &BTreeMap<usize, Vec<usize>>,
    prefix: usize,
) -> Result<(), HnnError> {
    counts
        .par_iter_mut()
        .enumerate()
        .try_for_each(|(slot, count)| {
            if let Some(events) = lanes.get(&slot) {
                let added = events.partition_point(|&at| at < prefix);
                let added = u64::try_from(added).map_err(|_| HnnError::CountOverflow)?;
                *count = count.checked_add(added).ok_or(HnnError::CountOverflow)?;
            }
            Ok(())
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::tests::learning::{chain, chain_declaration};

    fn encoded(field: &Field, word: &[usize]) -> Encoded {
        Encoded::identity(
            &crate::holarchy::terrain::KnownTruth::declared(field.alphabet(), vec![word.to_vec()]),
            field,
        )
        .unwrap()
        .remove(0)
    }

    fn assert_partitioned_prefixes(
        field: &Field,
        opening: &SourceMoment,
        current: &Current,
        cells: &Encoded,
    ) {
        let mut oracle_current = current.clone();
        let mut oracle_moment = opening.clone();
        let admitted = oracle_moment
            .ingest(field, &mut oracle_current, cells)
            .unwrap();
        for partitions in [1, 2, 7, 64] {
            let scanned = opening
                .scan_epoch_partitioned(field, current, cells, partitions)
                .unwrap();
            assert_eq!(scanned.consumed(), admitted.cells);
            assert_eq!(scanned.carry_out(), admitted.carry_out);
            let mut serial_current = current.clone();
            let mut serial_moment = opening.clone();
            for prefix in 0..=admitted.cells {
                if prefix != 0 {
                    serial_moment
                        .ingest(
                            field,
                            &mut serial_current,
                            &cells.part(prefix - 1..prefix).unwrap(),
                        )
                        .unwrap();
                }
                assert_eq!(scanned.current_at(field, prefix).unwrap(), serial_current);
                let actual = scanned.moment_at(prefix).unwrap();
                assert_eq!(actual, serial_moment);
                let mut actual_bits = String::new();
                let mut serial_bits = String::new();
                actual.write(&mut actual_bits);
                serial_moment.write(&mut serial_bits);
                assert_eq!(
                    actual_bits, serial_bits,
                    "partition {partitions}, prefix {prefix}"
                );
            }
            assert_eq!(scanned.post_current(field).unwrap(), oracle_current);
            assert_eq!(scanned.post_moment().unwrap(), oracle_moment);
            assert!(scanned.moment_at(admitted.cells + 1).is_err());
        }
    }

    #[test]
    fn input_prefix_partitions_match_actual_ingest_pair_buffer_and_carry() {
        let field = chain();
        let mut current = Current::at_rest(&field);
        let mut moment = SourceMoment::open(&field, &current);
        moment
            .ingest(&field, &mut current, &encoded(&field, &[1, 0, 1]))
            .unwrap();
        assert_partitioned_prefixes(&field, &moment, &current, &encoded(&field, &vec![0; 97]));
        assert_partitioned_prefixes(&field, &moment, &current, &encoded(&field, &[]));
        assert!(
            moment
                .scan_epoch_partitioned(&field, &current, &encoded(&field, &[0]), 0)
                .is_err()
        );
        let mut overflow = moment.clone();
        overflow.cells = u64::MAX;
        assert!(matches!(
            overflow.scan_epoch_partitioned(&field, &current, &encoded(&field, &[0]), 7),
            Err(HnnError::CountOverflow)
        ));
    }

    fn bank() -> Field {
        use crate::hnn::field::FieldDeclaration;
        let mut declaration = FieldDeclaration::campaign_one(1 << 17);
        declaration.rings.truncate(3);
        for (ring, period) in declaration.rings.iter_mut().zip([33, 7, 11]) {
            ring.period = period;
            ring.placements = (0..period)
                .map(|node| FieldDeclaration::quarter_turn(node, period))
                .collect();
            ring.reflector = (0..period)
                .map(|node| ((period - node) % period) as usize)
                .collect();
            ring.lock = if period == 11 { vec![] } else { vec![0, 2] };
        }
        declaration.alphabet = 4;
        declaration.contacts.truncate(2);
        declaration.loops.clear();
        declaration.receivers[0].aperture = 1;
        declaration.receivers[0].depth = 2;
        declaration.lattice.clear();
        Field::declare(declaration.by_lattice_rule()).unwrap()
    }

    #[test]
    fn input_prefix_partitions_keep_33_7_11_widths_large_winding_and_rekey() {
        use num_traits::One;
        let field = bank();
        assert_eq!(
            field.rings().iter().map(|r| r.width()).collect::<Vec<_>>(),
            [66, 14, 22]
        );
        let winding = BigInt::one() << 200usize;
        let lift = field
            .rings()
            .iter()
            .map(|r| &winding * r.period())
            .collect();
        let mut current = Current::at(&field, lift).unwrap();
        current.rekey(&field, 0, 31).unwrap();
        let moment = SourceMoment::open(&field, &current);
        let cells = (0..97).map(|at| at % 4).collect::<Vec<_>>();
        assert_partitioned_prefixes(&field, &moment, &current, &encoded(&field, &cells));
        let wrong = Current::at_rest(&field);
        assert!(
            field
                .scan_input_selected(&[], &encoded(&field, &[0]), 0..1, 7)
                .is_err()
        );
        assert!(
            field
                .scan_input_selected(wrong.lift(), &encoded(&field, &[0]), 0..2, 7)
                .is_err()
        );
    }

    #[test]
    fn input_prefix_partitions_match_located_squares_and_reject_wrong_opening() {
        use crate::hnn::tests::moment::{at_helix, helix_field, partial_span};
        let field = helix_field();
        let (cells, key) = partial_span(&field);
        let current = at_helix(&field, key);
        let moment = SourceMoment::open(&field, &current);
        assert_partitioned_prefixes(&field, &moment, &current, &cells);
        let wrong = at_helix(&field, (key + 1) % 30);
        let other = SourceMoment::open(&field, &wrong);
        for partitions in [1, 2, 7, 64] {
            assert!(
                other
                    .scan_epoch_partitioned(&field, &wrong, &cells, partitions)
                    .is_err()
            );
        }
    }

    #[test]
    fn input_prefix_partitions_match_observed_actual_port() {
        use crate::hnn::constitution::Constitution;
        use crate::hnn::encoding::observed::PairedObservation;
        use crate::hnn::paired::{PairedCarrier, PairingDeclaration};
        use crate::ratio::{integer, linear::ExactRatMatrix};
        let field = bank();
        let pairing = PairingDeclaration::Family {
            table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
        };
        let width = field.ring(0).width();
        let free = ExactRatMatrix::shaped(
            width,
            4,
            (0..width)
                .map(|r| {
                    (0..4)
                        .map(|c| integer(i64::from((r == 2 && c == 0) || (r == 4 && c == 2))))
                        .collect()
                })
                .collect(),
        )
        .unwrap();
        let port = PairedCarrier::complete_port(&field, 0, &pairing, &free).unwrap();
        let carrier = PairedCarrier::admit(&field, 0, &pairing, &port).unwrap();
        let material = Constitution::initial(&field, 1 << 40)
            .unwrap()
            .with_symmetric_source(0, port, carrier.symmetry())
            .unwrap();
        let boundary = PairedObservation::admit(&field, &material, &pairing).unwrap();
        let cells = boundary
            .encode(&(0..97).map(|at| at % 4).collect::<Vec<_>>())
            .unwrap();
        let current = Current::at_rest(&field);
        let moment = SourceMoment::open(&field, &current);
        assert_partitioned_prefixes(&field, &moment, &current, &cells);
    }

    #[test]
    fn every_prefix_matches_ingest_across_the_opening_pair_buffer_and_carry() {
        let field = chain();
        let mut current = Current::at_rest(&field);
        let mut opening = SourceMoment::open(&field, &current);
        let prelude = [1, 0, 1];
        opening
            .ingest(&field, &mut current, &encoded(&field, &prelude))
            .unwrap();

        let word = vec![0; 64];
        let encoded_epoch = encoded(&field, &word);
        let scan = opening
            .scan_epoch(&field, &current, &encoded_epoch)
            .unwrap();
        let mut oracle = current.clone();
        let mut oracle_moment = opening.clone();
        let admitted = oracle_moment
            .ingest(&field, &mut oracle, &encoded_epoch)
            .unwrap();
        assert!(admitted.carry_out);
        assert_eq!(scan.consumed(), admitted.cells);
        assert_eq!(scan.carry_out(), admitted.carry_out);

        for prefix in 0..=scan.consumed() {
            let mut oracle_current = current.clone();
            let mut prefix_moment = opening.clone();
            prefix_moment
                .ingest(
                    &field,
                    &mut oracle_current,
                    &encoded(&field, &word[..prefix]),
                )
                .unwrap();
            assert_eq!(scan.current_at(&field, prefix).unwrap(), oracle_current);
            let scanned = scan.moment_at(prefix).unwrap();
            assert_eq!(scanned, prefix_moment);
            let mut scanned_text = String::new();
            scanned.write(&mut scanned_text);
            let mut oracle_text = String::new();
            prefix_moment.write(&mut oracle_text);
            assert_eq!(scanned_text, oracle_text);
        }
        assert_eq!(scan.post_current(&field).unwrap(), oracle);
        assert_eq!(scan.post_moment().unwrap(), oracle_moment);
        assert!(scan.moment_at(scan.consumed() + 1).is_err());
    }

    #[test]
    fn another_fields_encoding_is_refused_before_a_scan_is_published() {
        let field = chain();
        let mut declaration = chain_declaration(1 << 16);
        declaration.sources = vec![1];
        declaration.alphabet = 2;
        declaration.offsets.clear();
        let other = Field::declare(declaration.by_lattice_rule()).unwrap();
        let current = Current::at_rest(&field);
        let moment = SourceMoment::open(&field, &current);
        assert!(
            moment
                .scan_epoch(&field, &current, &encoded(&other, &[0, 1]))
                .is_err()
        );
    }
}
