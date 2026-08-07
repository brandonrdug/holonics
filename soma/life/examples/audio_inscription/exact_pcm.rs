use std::path::Path;

use body::incidence::{
    EventCell, EventCellId, EventComplex, EventPort, IncidenceHand, OrientedIncidence,
};
use body::num::Cog;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PcmWave {
    pub(crate) sample_rate: u32,
    pub(crate) samples: Vec<i16>,
}

impl PcmWave {
    pub(crate) fn read(path: &Path) -> Result<Self, String> {
        let mut reader = hound::WavReader::open(path)
            .map_err(|error| format!("{} opens as WAV: {error}", path.display()))?;
        let spec = reader.spec();
        if spec.channels != 1
            || spec.bits_per_sample != 16
            || spec.sample_format != hound::SampleFormat::Int
        {
            return Err(format!(
                "{} is not mono signed 16-bit PCM (channels={} bits={} format={:?})",
                path.display(),
                spec.channels,
                spec.bits_per_sample,
                spec.sample_format
            ));
        }
        let samples = reader
            .samples::<i16>()
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| format!("{} samples decode exactly: {error}", path.display()))?;
        if samples.is_empty() {
            return Err(format!("{} contains no PCM samples", path.display()));
        }
        Ok(Self {
            sample_rate: spec.sample_rate,
            samples,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ButterflySheet {
    pub(crate) rank: u32,
    pub(crate) sums: Vec<i64>,
    pub(crate) differences: Vec<i64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DirectedButterflyAtlas {
    samples: Vec<i64>,
    pub(crate) sheets: Vec<ButterflySheet>,
}

impl DirectedButterflyAtlas {
    fn new(samples: impl IntoIterator<Item = i16>) -> Result<Self, String> {
        let samples: Vec<i64> = samples.into_iter().map(i64::from).collect();
        if samples.is_empty() {
            return Err("an acoustic atlas needs at least one sample".to_owned());
        }
        let mut sheets = Vec::new();
        let mut current = samples.clone();
        let mut rank = 1u32;
        while current.len() >= 2 {
            let mut sums = Vec::with_capacity(current.len() / 2);
            let mut differences = Vec::with_capacity(current.len() / 2);
            for pair in current.chunks_exact(2) {
                sums.push(
                    pair[0]
                        .checked_add(pair[1])
                        .ok_or_else(|| "butterfly sum exceeded i64".to_owned())?,
                );
                differences.push(
                    pair[1]
                        .checked_sub(pair[0])
                        .ok_or_else(|| "butterfly difference exceeded i64".to_owned())?,
                );
            }
            sheets.push(ButterflySheet {
                rank,
                sums: sums.clone(),
                differences,
            });
            current = sums;
            rank = rank
                .checked_add(1)
                .ok_or_else(|| "butterfly rank exceeded u32".to_owned())?;
        }
        Ok(Self { samples, sheets })
    }

    pub(crate) fn sheet(&self, rank: u32) -> Option<&ButterflySheet> {
        rank.checked_sub(1)
            .and_then(|at| self.sheets.get(at as usize))
    }

    pub(crate) fn reconstruct(&self) -> Result<Vec<i16>, String> {
        let mut reconstructed = Vec::with_capacity(self.samples.len());
        let mut start = 0usize;
        while start < self.samples.len() {
            let remaining = self.samples.len() - start;
            let rank = (usize::BITS - 1 - remaining.leading_zeros()) as u32;
            let sum = if rank == 0 {
                self.samples[start]
            } else {
                let block = start >> rank;
                *self
                    .sheet(rank)
                    .and_then(|sheet| sheet.sums.get(block))
                    .ok_or_else(|| format!("missing rank-{rank} root at sample {start}"))?
            };
            self.reconstruct_block(rank, start, sum, &mut reconstructed)?;
            start = start
                .checked_add(1usize << rank)
                .ok_or_else(|| "reconstruction extent exceeded usize".to_owned())?;
        }
        Ok(reconstructed)
    }

    fn reconstruct_block(
        &self,
        rank: u32,
        start: usize,
        sum: i64,
        output: &mut Vec<i16>,
    ) -> Result<(), String> {
        if rank == 0 {
            output.push(
                i16::try_from(sum)
                    .map_err(|_| format!("reconstructed sample {sum} is outside signed PCM"))?,
            );
            return Ok(());
        }
        let block = start >> rank;
        let difference = *self
            .sheet(rank)
            .and_then(|sheet| sheet.differences.get(block))
            .ok_or_else(|| format!("missing rank-{rank} difference at sample {start}"))?;
        let left_twice = sum
            .checked_sub(difference)
            .ok_or_else(|| "inverse left arm exceeded i64".to_owned())?;
        let right_twice = sum
            .checked_add(difference)
            .ok_or_else(|| "inverse right arm exceeded i64".to_owned())?;
        if (left_twice & 1) != 0 || (right_twice & 1) != 0 {
            return Err(format!(
                "rank-{rank} butterfly lost parity at sample {start}"
            ));
        }
        let half = 1usize << (rank - 1);
        self.reconstruct_block(rank - 1, start, left_twice / 2, output)?;
        self.reconstruct_block(rank - 1, start + half, right_twice / 2, output)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ButterflyAtlas {
    pub(crate) forward: DirectedButterflyAtlas,
    pub(crate) reverse: DirectedButterflyAtlas,
}

impl ButterflyAtlas {
    pub(crate) fn new(samples: &[i16]) -> Result<Self, String> {
        Ok(Self {
            forward: DirectedButterflyAtlas::new(samples.iter().copied())?,
            reverse: DirectedButterflyAtlas::new(samples.iter().rev().copied())?,
        })
    }

    pub(crate) fn reconstructs(&self, samples: &[i16]) -> Result<(bool, bool), String> {
        let forward = self.forward.reconstruct()? == samples;
        let mut reversed = self.reverse.reconstruct()?;
        reversed.reverse();
        Ok((forward, reversed == samples))
    }
}

/// One exact ordered scalar sheet. Zero is a lawful waveform constituent, so this source chart
/// constructs the event complex directly instead of forcing it through nonzero `RelationAtom`.
pub(crate) struct ExactPathChart {
    cells: Vec<EventCell>,
    incidences: Vec<OrientedIncidence>,
    ports: Vec<EventPort>,
}

impl ExactPathChart {
    pub(crate) fn new(values: &[i64]) -> Result<Self, String> {
        if values.is_empty() {
            return Err("an exact path chart cannot be empty".to_owned());
        }
        let edges = values.len() - 1;
        let mut cells = Vec::with_capacity(values.len() + edges);
        let mut incidences = Vec::with_capacity(edges * 2);
        let mut ports = Vec::with_capacity(edges.max(1) + 1);

        for (at, value) in values.iter().copied().enumerate() {
            cells.push(EventCell::new(
                EventCellId::new(at as u64),
                0,
                0,
                Cog::lit(value),
            ));
        }
        for at in 0..edges {
            let edge = EventCellId::new((values.len() + at) as u64);
            cells.push(EventCell::new(
                edge,
                0,
                1,
                Cog::lit(values[at + 1]).sub(Cog::lit(values[at])),
            ));
            incidences.push(OrientedIncidence::boundary(
                EventCellId::new(at as u64),
                edge,
                IncidenceHand::Against,
                0,
            ));
            incidences.push(OrientedIncidence::boundary(
                EventCellId::new((at + 1) as u64),
                edge,
                IncidenceHand::With,
                1,
            ));
        }
        ports.push(EventPort::ingress(
            EventCellId::new(0),
            IncidenceHand::With,
            0,
        ));
        if edges == 0 {
            ports.push(EventPort::exposed(
                EventCellId::new(0),
                IncidenceHand::With,
                0,
            ));
        } else {
            for at in 0..edges {
                ports.push(EventPort::exposed(
                    EventCellId::new((values.len() + at) as u64),
                    IncidenceHand::With,
                    at as u32,
                ));
            }
        }
        EventComplex::new(&cells, &incidences, &ports)
            .map_err(|error| format!("exact path complex validates: {error:?}"))?;
        Ok(Self {
            cells,
            incidences,
            ports,
        })
    }

    pub(crate) fn exposed(&self) -> usize {
        self.ports.len() - 1
    }

    pub(crate) fn cells(&self) -> usize {
        self.cells.len()
    }

    pub(crate) fn incidences(&self) -> usize {
        self.incidences.len()
    }

    pub(crate) fn complex(&self) -> EventComplex<'_> {
        EventComplex::new(&self.cells, &self.incidences, &self.ports)
            .expect("an immutable exact path retains its validated incidence")
    }
}
