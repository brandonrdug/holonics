//! Same-law retained-section certificate on the actual material ray. Transient only.
use super::deposit::{EpochReceivingCertificate, EpochReceivingRecord, upper_grid_numerator};
use super::*;
use crate::hnn::receiving::{RetainedSectionOrigin, RetainedSectionSourceReading};
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum EpochReceivingLaw {
    CoarseOdometerV1,
    RetainedFibreV1(RetainedStationBinding),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RetainedStationBinding {
    origin: Arc<RetainedSectionOrigin>,
    commit: u64,
    station: usize,
    source_cells: u64,
    anchor: Vec<BigInt>,
    map: ExactRatMatrix,
    sample: Sample,
    positive: Vec<Rat>,
    foil: Vec<Rat>,
    phase: Vec<Rat>,
}
impl EpochReceivingLaw {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn retained(
        origin: Arc<RetainedSectionOrigin>,
        receiver: usize,
        commit: u64,
        station: usize,
        source_cells: u64,
        anchor: Vec<BigInt>,
        map: &ExactRatMatrix,
        sample: &Sample,
        positive: &[Rat],
        foil: &[Rat],
        phase: &[Rat],
    ) -> Result<Self, HnnError> {
        if origin.ring != receiver {
            return Err(refused("retained return's actual receiver"));
        }
        let bound = RetainedStationBinding {
            origin,
            commit,
            station,
            source_cells,
            anchor,
            map: map.clone(),
            sample: sample.clone(),
            positive: positive.to_vec(),
            foil: foil.to_vec(),
            phase: phase.to_vec(),
        };
        bound.admit(sample, positive, foil, phase)?;
        Ok(Self::RetainedFibreV1(bound))
    }
    pub(crate) fn admit_owner(
        &self,
        receiver: usize,
        commit: u64,
        map: &ExactRatMatrix,
    ) -> Result<(), HnnError> {
        if let Self::RetainedFibreV1(b) = self {
            if b.origin.ring != receiver || b.commit != commit || &b.map != map {
                return Err(refused(
                    "retained receiving witness keeps actual receiver/commit/map",
                ));
            }
        }
        Ok(())
    }
}
impl RetainedStationBinding {
    fn admit(
        &self,
        sample: &Sample,
        positive: &[Rat],
        foil: &[Rat],
        phase: &[Rat],
    ) -> Result<(), HnnError> {
        let station = self
            .origin
            .stations
            .get(self.station)
            .ok_or_else(|| refused("retained station in its section"))?;
        let n = station.gradient.len();
        if sample != &self.sample
            || sample.weight != Rat::one()
            || positive != self.positive
            || foil != self.foil
            || phase != self.phase
            || sample.covector.len() != 2 * n
            || positive.len() != 2 * n
            || foil.len() != 2 * n
            || phase.len() != 2 * n
            || station.component_error.len() != n
            || station.packed_foil.len() != n
            || self.origin.targets.get(self.station) != Some(&station.target)
            || station.gradient.iter().cloned().sum::<Rat>() != Rat::zero()
            || sample.masses.as_ref() != Some(&station.normalized_representative)
            || station.component_error.iter().any(Signed::is_negative)
        {
            return Err(refused(
                "retained certificate binds actual unit-weight sample, source and error shape",
            ));
        }
        for c in 0..n {
            let e = if c == station.target {
                Rat::one()
            } else {
                Rat::zero()
            };
            if positive[2 * c] != e
                || !positive[2 * c + 1].is_zero()
                || foil[2 * c] != station.packed_foil[c]
                || !foil[2 * c + 1].is_zero()
                || !phase[2 * c].is_zero()
                || sample.covector[2 * c] != -station.gradient[c].clone()
                || sample.covector[2 * c + 1] != phase[2 * c + 1]
            {
                return Err(refused(
                    "retained packed class return and exact original phase are the actual sample",
                ));
            }
        }
        Ok(())
    }
}

/// None means the literal historical coarse branch. Mixed laws never fall back.
pub(super) fn certificate(
    samples: &[Sample],
    parts: &[EpochReceivingRecord],
    direction: &[Vec<Rat>],
    bits: u32,
) -> Result<Option<EpochReceivingCertificate>, HnnError> {
    if parts
        .iter()
        .all(|p| matches!(p.law, EpochReceivingLaw::CoarseOdometerV1))
    {
        return Ok(None);
    }
    if samples.len() != parts.len() || parts.is_empty() {
        return Err(refused("one retained receiving sample per station"));
    }
    let EpochReceivingLaw::RetainedFibreV1(first) = &parts[0].law else {
        return Err(refused("one receiving certificate law per section"));
    };
    if first.origin.stations.len() != parts.len() {
        return Err(refused(
            "the complete retained section supplies the certificate",
        ));
    }
    let denominator = BigInt::one() << bits.checked_mul(2).ok_or_else(extent)? as usize;
    let mut alignment = Rat::zero();
    let mut error = BigInt::zero();
    let mut curvature = BigInt::zero();
    let mut oscillation = Rat::zero();
    for (at, (sample, part)) in samples.iter().zip(parts).enumerate() {
        let EpochReceivingLaw::RetainedFibreV1(b) = &part.law else {
            return Err(refused("mixed retained/coarse receiving certificate"));
        };
        if !Arc::ptr_eq(&first.origin, &b.origin)
            || b.station != at
            || b.commit != first.commit
            || b.map != first.map
            || b.source_cells
                != first
                    .source_cells
                    .checked_add(at as u64)
                    .ok_or_else(extent)?
            || part.feature != sample.feature
            || direction.len() != sample.covector.len()
            || direction
                .iter()
                .any(|row| row.len() != sample.feature.len())
        {
            return Err(refused(
                "retained section keeps one producer, station order, actual feature and material ray",
            ));
        }
        b.admit(sample, &part.positive, &part.foil, &part.phase)?;
        let delta: Vec<Rat> = direction
            .iter()
            .map(|row| row.iter().zip(&sample.feature).map(|(p, f)| p * f).sum())
            .collect();
        let real: Vec<_> = delta.iter().step_by(2).collect();
        let eps = &b.origin.stations[at].component_error;
        let local_error = (0..real.len())
            .map(|s| {
                eps.iter()
                    .zip(&real)
                    .map(|(e, d)| e * (*d - real[s]).abs())
                    .sum::<Rat>()
            })
            .min()
            .ok_or_else(|| refused("retained actual ray has a class"))?;
        alignment += &sample.weight
            * sample
                .covector
                .iter()
                .zip(&delta)
                .map(|(g, d)| g * d)
                .sum::<Rat>();
        error += upper_grid_numerator(&(sample.weight.abs() * local_error), &denominator);
        let osc = real.iter().max().ok_or_else(extent)?.to_owned().clone()
            - real.iter().min().ok_or_else(extent)?.to_owned().clone();
        let phase_norm: Rat = delta.iter().skip(1).step_by(2).map(|x| x * x).sum();
        let bracket = sample.weight.abs()
            * (Rat::new(7.into(), 40.into()) * &osc * &osc
                + phase_norm / Rat::from_integer(4.into()));
        curvature += upper_grid_numerator(&bracket, &denominator);
        oscillation = oscillation.max(osc);
    }
    Ok(Some(EpochReceivingCertificate {
        moves: Rat::new(curvature * 2, denominator.clone()),
        oscillation,
        alignment,
        odometer: Rat::zero(),
        partition: Rat::zero(),
        return_error: Rat::new(error, denominator),
    }))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EpochReceivingStationReading {
    pub sample: Sample,
    pub positive: Vec<Rat>,
    pub foil: Vec<Rat>,
    pub phase: Vec<Rat>,
    pub station: Option<usize>,
    pub source_cells: Option<u64>,
    pub anchor: Option<Vec<BigInt>>,
}
/// Exact failed-proposal operands for exterior local evidence only; never checkpoint retention.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EpochReceivingRayPacket {
    pub law: &'static str,
    pub commit: Option<u64>,
    pub original_map: Option<ExactRatMatrix>,
    pub actual_ray: ExactRatMatrix,
    pub stations: Vec<EpochReceivingStationReading>,
    pub retained_source: Option<RetainedSectionSourceReading>,
    /// Preflight includes every numeric field and all vector/record metadata below.
    /// This is an operand extent, not a claim about allocator or encoded byte size.
    pub operand_integer_bits: u64,
    pub operand_structural_items: u64,
}
#[derive(Default)]
struct PacketExtent {
    bits: u64,
    items: u64,
}
impl PacketExtent {
    fn add(&mut self, bits: u64, items: u64) -> Option<()> {
        self.bits = self.bits.checked_add(bits)?;
        self.items = self.items.checked_add(items)?;
        (self.bits <= 16 * 1024 * 1024 && self.items <= 262144).then_some(())
    }
    fn items(&mut self, count: usize) -> Option<()> {
        // All primitive scalar metadata (including lengths/indices) is charged
        // at 128 bits per structural item, regardless of the actual value.
        let count = u64::try_from(count).ok()?;
        self.add(count.checked_mul(128)?, count)
    }
    fn integer(&mut self, value: &BigInt) -> Option<()> {
        self.add(value.bits().checked_add(1)?, 1)
    }
    fn rat(&mut self, value: &Rat) -> Option<()> {
        self.integer(value.numer())?;
        self.integer(value.denom())?;
        self.items(1)
    }
    fn rats(&mut self, values: &[Rat]) -> Option<()> {
        self.items(1)?;
        for value in values {
            self.rat(value)?;
        }
        Some(())
    }
    fn interval(&mut self, value: &crate::ratio::algebraic::ExactInterval) -> Option<()> {
        self.items(1)?;
        self.rat(&value.lower)?;
        self.rat(&value.upper)
    }
}

pub(super) fn failure_packet(
    samples: &[Sample],
    parts: &[EpochReceivingRecord],
    direction: &[Vec<Rat>],
) -> Option<EpochReceivingRayPacket> {
    if samples.len() != parts.len()
        || samples.len() > 4096
        || direction.is_empty()
        || direction.len().checked_mul(direction[0].len())? > 65536
        || direction.iter().any(|row| row.len() != direction[0].len())
    {
        return None;
    }
    let first = parts.first()?;
    // Preflight by reference BEFORE any map/source/sample clone. Independent numeric
    // and structural caps also bound zero-heavy vectors; an unavailable diagnostic
    // never changes the operative native refusal.
    let mut extent = PacketExtent::default();
    extent.items(16)?;
    for row in direction {
        extent.rats(row)?;
    }
    for (sample, part) in samples.iter().zip(parts) {
        extent.items(16)?;
        extent.rat(&sample.weight)?;
        extent.rats(&sample.feature)?;
        extent.rats(&sample.covector)?;
        if let Some(masses) = &sample.masses {
            extent.rats(masses)?;
        }
        extent.rats(&part.positive)?;
        extent.rats(&part.foil)?;
        extent.rats(&part.phase)?;
        if let EpochReceivingLaw::RetainedFibreV1(b) = &part.law {
            extent.items(8)?;
            for x in &b.anchor {
                extent.integer(x)?;
            }
        }
    }
    if let EpochReceivingLaw::RetainedFibreV1(b) = &first.law {
        extent.rats(b.map.entries())?;
        let o = &b.origin;
        let (bits, items) = o.population.diagnostic_extent()?;
        extent.add(bits, items)?;
        extent.items(16)?;
        for wave in &o.combined.logits {
            extent.rats(wave)?;
        }
        for tree in &o.trees {
            extent.items(8)?;
            extent.rats(&tree.probabilities)?;
            for x in &tree.exponents {
                extent.integer(x)?;
            }
        }
        extent.items(o.targets.len())?;
        extent.interval(&o.rho)?;
        extent.interval(&o.beta)?;
        for station in &o.stations {
            extent.items(8)?;
            extent.rats(&station.normalized_representative)?;
            extent.rats(&station.packed_foil)?;
            extent.rats(&station.gradient)?;
            extent.rats(&station.component_error)?;
            for interval in &station.component_bounds {
                extent.interval(interval)?;
            }
        }
    }
    let (law, commit, map, source) = match &first.law {
        EpochReceivingLaw::CoarseOdometerV1 => ("coarse-grain-v1", None, None, None),
        EpochReceivingLaw::RetainedFibreV1(b) => (
            "retained-fibre-v1",
            Some(b.commit),
            Some(b.map.clone()),
            Some(b.origin.reading()),
        ),
    };
    let stations = samples
        .iter()
        .zip(parts)
        .map(|(sample, p)| {
            let (station, cells, anchor) = match &p.law {
                EpochReceivingLaw::CoarseOdometerV1 => (None, None, None),
                EpochReceivingLaw::RetainedFibreV1(b) => (
                    Some(b.station),
                    Some(b.source_cells),
                    Some(b.anchor.clone()),
                ),
            };
            EpochReceivingStationReading {
                sample: sample.clone(),
                positive: p.positive.clone(),
                foil: p.foil.clone(),
                phase: p.phase.clone(),
                station,
                source_cells: cells,
                anchor,
            }
        })
        .collect();
    Some(EpochReceivingRayPacket {
        law,
        commit,
        original_map: map,
        actual_ray: ExactRatMatrix::new(direction.to_vec()).ok()?,
        stations,
        retained_source: source,
        operand_integer_bits: extent.bits,
        operand_structural_items: extent.items,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compression::landmark::context::LandmarkFace;
    use crate::hnn::ratio::Faces;
    use crate::hnn::receiving::{ReceivingRead, RetainedSectionReturn};
    use crate::ratio::rat;
    use crate::receiver::population::port::PortReading;

    fn actual_return(
        count: usize,
    ) -> (
        RetainedSectionReturn,
        crate::receiver::population::PortPopulation,
        Faces,
        Vec<LandmarkFace>,
        Vec<usize>,
    ) {
        let population = crate::hnn::receiving::receiving_population();
        let text = "population 2 0\n63 -6 63 -6 -\n1 -6 1 -6 -\n";
        let reading = PortReading::read(&mut text.lines()).unwrap();
        let population = population.with_reading(&reading).unwrap();
        let tree = LandmarkFace {
            grain: 4,
            probabilities: vec![rat(1, 2); 2],
            exponents: vec![(-1).into(), (-1).into()],
        };
        let trees = vec![tree; count];
        let reads: Vec<_> = trees
            .iter()
            .map(|tree| ReceivingRead::combined(vec![Rat::zero(); 4], tree, 4).unwrap())
            .collect();
        let faces = Faces::of_reads(&reads, 4).unwrap();
        let targets = vec![0; count];
        let returned = RetainedSectionReturn::at(&population, 0, &faces, &trees, &targets).unwrap();
        (returned, population, faces, trees, targets)
    }
    fn records(
        returned: &RetainedSectionReturn,
        population: &crate::receiver::population::PortPopulation,
        faces: &Faces,
        trees: &[LandmarkFace],
        targets: &[usize],
    ) -> (Vec<Sample>, Vec<EpochReceivingRecord>) {
        let origin = returned
            .certificate_origin(population, 0, faces, trees, targets)
            .unwrap();
        let map = ExactRatMatrix::zero(4, 1).unwrap();
        let mut samples = Vec::new();
        let mut parts = Vec::new();
        for (at, station) in returned.stations.iter().enumerate() {
            let positive = vec![Rat::one(), Rat::zero(), Rat::zero(), Rat::zero()];
            let foil = vec![
                station.packed_foil[0].clone(),
                Rat::zero(),
                station.packed_foil[1].clone(),
                Rat::zero(),
            ];
            let phase = vec![Rat::zero(); 4];
            let sample = Sample {
                weight: Rat::one(),
                feature: vec![Rat::one()],
                covector: vec![
                    -station.gradient[0].clone(),
                    Rat::zero(),
                    -station.gradient[1].clone(),
                    Rat::zero(),
                ],
                masses: Some(station.normalized_representative.clone()),
            };
            let law = EpochReceivingLaw::retained(
                Arc::clone(&origin),
                0,
                7,
                at,
                at as u64,
                vec![BigInt::from(at)],
                &map,
                &sample,
                &positive,
                &foil,
                &phase,
            )
            .unwrap();
            parts.push(EpochReceivingRecord {
                law,
                feature: sample.feature.clone(),
                positive,
                foil,
                phase,
            });
            samples.push(sample);
        }
        (samples, parts)
    }
    #[test]
    fn retained_ray_uses_true_error_instead_of_coarse_surcharge() {
        let (r, p, f, t, y) = actual_return(1);
        assert_eq!(
            r.beta,
            crate::ratio::algebraic::ExactInterval::point(rat(1, 64))
        );
        assert!(r.stations[0].component_error.iter().all(Zero::is_zero));
        let (s, mut parts) = records(&r, &p, &f, &t, &y);
        let direction = vec![
            vec![rat(1, 1)],
            vec![Rat::zero()],
            vec![rat(-1, 1)],
            vec![Rat::zero()],
        ];
        let exact = certificate(&s, &parts, &direction, 8).unwrap().unwrap();
        assert_eq!(exact.alignment - exact.return_error, rat(1, 64));
        assert!(exact.moves >= rat(7, 5));
        assert!(exact.moves < rat(7, 5) + rat(2, 65536));
        let delta =
            EpochArray::new(4, 1, 0, vec![1.into(), 0.into(), (-1).into(), 0.into()]).unwrap();
        assert!(
            super::super::deposit::actual_epoch_face(
                LinearLocus::Receiving(0),
                &delta,
                &s,
                &parts,
                8,
                Rat::one(),
                &mut None
            )
            .is_ok()
        );
        parts[0].law = EpochReceivingLaw::CoarseOdometerV1;
        let coarse =
            super::super::deposit::receiving_epoch_certificate(&s, &parts, &direction, 8).unwrap();
        assert_eq!(
            coarse.alignment - coarse.odometer - coarse.partition.max(Rat::zero()),
            rat(-3, 64)
        );
        assert!(coarse.return_error.is_zero());
        println!(
            "RETAINED_RAY_FALSE_SURCHARGE_WITNESS true=1/64 old=-3/64 eps=0; no failed dataset candidate replayed"
        );
    }
    #[test]
    fn retained_ray_nonascending_actual_projection_still_refuses_and_records_operands() {
        let (r, p, f, t, y) = actual_return(1);
        let (s, parts) = records(&r, &p, &f, &t, &y);
        assert!(r.norm_squared > r.error_pairing);
        let delta =
            EpochArray::new(4, 1, 0, vec![(-1).into(), 0.into(), 1.into(), 0.into()]).unwrap();
        let mut evidence = None;
        assert!(
            super::super::deposit::actual_epoch_face(
                LinearLocus::Receiving(0),
                &delta,
                &s,
                &parts,
                8,
                Rat::one(),
                &mut evidence
            )
            .is_err()
        );
        let e = evidence.unwrap();
        assert_eq!(e.condition, EpochStageCondition::ActualRayAlignment);
        let packet = e
            .readings
            .iter()
            .find_map(|r| match &r.value {
                EpochStageValue::ReceivingRay(p) => Some(p),
                _ => None,
            })
            .unwrap();
        assert_eq!(packet.stations[0].sample, s[0]);
        assert_eq!(packet.commit, Some(7));
        assert_eq!(packet.retained_source.as_ref().unwrap().beta, r.beta);
        assert_eq!(
            packet.actual_ray,
            ExactRatMatrix::new(delta.to_rows()).unwrap()
        );
        assert!(!e.seal_formed && !e.finite_probe_executed);
        let text = format!("{e:?}");
        assert!(text.contains("component_error"));
        assert!(text.contains("source_cells: Some(0)"));
        println!("RETAINED_ACTUAL_RAY_REFUSAL_PACKET {text}");
    }
    #[test]
    fn retained_ray_identity_error_shape_phase_and_common_shift_controls() {
        let (r, p, f, t, y) = actual_return(2);
        let (s, parts) = records(&r, &p, &f, &t, &y);
        let direction = vec![
            vec![rat(5, 1)],
            vec![Rat::zero()],
            vec![rat(5, 1)],
            vec![Rat::zero()],
        ];
        let face = certificate(&s, &parts, &direction, 8).unwrap().unwrap();
        assert!(face.alignment.is_zero() && face.return_error.is_zero() && face.moves.is_zero());
        let mut bad = parts.clone();
        bad[1].feature[0] += Rat::one();
        assert!(certificate(&s, &bad, &direction, 8).is_err());
        let mut bad = parts.clone();
        bad[1].law = EpochReceivingLaw::CoarseOdometerV1;
        assert!(certificate(&s, &bad, &direction, 8).is_err());
        let (r2, p2, f2, t2, y2) = actual_return(2);
        let (_, other) = records(&r2, &p2, &f2, &t2, &y2);
        let mut bad = parts.clone();
        bad[1].law = other[1].law.clone();
        assert!(certificate(&s, &bad, &direction, 8).is_err());
        let mut bad = parts.clone();
        bad[0].phase[1] = Rat::one();
        assert!(certificate(&s, &bad, &direction, 8).is_err());
        let mut samples = s.clone();
        samples[0].weight = rat(-1, 1);
        assert!(certificate(&samples, &parts, &direction, 8).is_err());
        let mut changed = r.clone();
        changed.stations[0].component_error.clear();
        assert!(changed.certificate_origin(&p, 0, &f, &t, &y).is_err());
        assert!(
            parts[0]
                .law
                .admit_owner(0, 8, &ExactRatMatrix::zero(4, 1).unwrap())
                .is_err()
        );
    }
    #[test]
    fn retained_ray_nonzero_true_component_error_is_centered_and_rounded_up() {
        let (_, p, _, t, y) = actual_return(1);
        let read = ReceivingRead::combined(
            vec![rat(1, 3), Rat::zero(), rat(-1, 5), Rat::zero()],
            &t[0],
            4,
        )
        .unwrap();
        let f = Faces::of_reads(&[read], 4).unwrap();
        let r = RetainedSectionReturn::at(&p, 0, &f, &t, &y).unwrap();
        assert!(
            r.stations[0]
                .component_error
                .iter()
                .any(Signed::is_positive)
        );
        let (s, parts) = records(&r, &p, &f, &t, &y);
        let direction = vec![
            vec![rat(1, 1)],
            vec![Rat::zero()],
            vec![rat(-1, 1)],
            vec![Rat::zero()],
        ];
        let face = certificate(&s, &parts, &direction, 64).unwrap().unwrap();
        let eps = &r.stations[0].component_error;
        let raw = (rat(2, 1) * &eps[0]).min(rat(2, 1) * &eps[1]);
        assert!(
            face.return_error >= raw
                && face.return_error < raw + Rat::new(1.into(), BigInt::one() << 128)
        );
        let shifted = vec![
            vec![rat(8, 1)],
            vec![Rat::zero()],
            vec![rat(6, 1)],
            vec![Rat::zero()],
        ];
        let other = certificate(&s, &parts, &shifted, 64).unwrap().unwrap();
        assert_eq!(face.return_error, other.return_error);
        assert_eq!(face.alignment, other.alignment);
        assert_eq!(face.moves, other.moves);
    }
    #[test]
    fn retained_ray_full_packet_preflight_and_later_curvature_evidence() {
        let (r, p, f, t, y) = actual_return(1);
        let (samples, parts) = records(&r, &p, &f, &t, &y);
        let direction = vec![
            vec![rat(1, 1)],
            vec![Rat::zero()],
            vec![rat(-1, 1)],
            vec![Rat::zero()],
        ];
        let packet = failure_packet(&samples, &parts, &direction).unwrap();
        assert!(packet.operand_integer_bits > 0 && packet.operand_structural_items > 0);
        // Hidden source/error/map/anchor operands all participate in reference-only
        // preflight. No large diagnostic clone or formatting is needed to refuse.
        let huge = Rat::from_integer(BigInt::one() << (16 * 1024 * 1024));
        for field in 0..4 {
            let mut bad = parts.clone();
            let EpochReceivingLaw::RetainedFibreV1(binding) = &mut bad[0].law else {
                unreachable!()
            };
            match field {
                0 => Arc::make_mut(&mut binding.origin).beta.lower = huge.clone(),
                1 => {
                    Arc::make_mut(&mut binding.origin).stations[0].component_error[0] = huge.clone()
                }
                2 => binding.anchor[0] = huge.numer().clone(),
                _ => binding.map = ExactRatMatrix::new(vec![vec![huge.clone()]; 4]).unwrap(),
            }
            assert!(
                failure_packet(&samples, &bad, &direction).is_none(),
                "field {field}"
            );
        }
        let mut evidence = EpochStageRefusal::at(
            "actual_certificate",
            EpochStageCondition::ActualRayCurvature,
            "eta * curvature <= alignment",
            Some(Locus::ReceivingMap(0)),
            Some(Family::Map),
        );
        super::super::deposit::attach_receiving_ray_packet(
            &mut evidence,
            &samples,
            &parts,
            &direction,
            8,
        );
        assert_eq!(evidence.condition, EpochStageCondition::ActualRayCurvature);
        assert_eq!(evidence.phase, "actual_certificate");
        assert!(
            evidence
                .readings
                .iter()
                .any(|r| matches!(r.value, EpochStageValue::ReceivingRay(_)))
        );
        assert!(
            evidence
                .readings
                .iter()
                .any(|r| r.name == "actual_nominal_alignment"
                    && r.value == EpochStageValue::Ratio(rat(1, 64)))
        );
        assert!(
            evidence
                .readings
                .iter()
                .any(|r| r.name == "actual_receiving_curvature_moves")
        );
        let count = evidence.readings.len();
        super::super::deposit::attach_receiving_ray_packet(
            &mut evidence,
            &samples,
            &parts,
            &direction,
            8,
        );
        assert_eq!(evidence.readings.len(), count);
        let mut refused = EpochStageRefusal::at(
            "actual_certificate",
            EpochStageCondition::ActualRayCurvature,
            "original operative refusal",
            Some(Locus::ReceivingMap(0)),
            Some(Family::Map),
        );
        super::super::deposit::attach_receiving_ray_packet(
            &mut refused,
            &samples,
            &[],
            &direction,
            8,
        );
        assert_eq!(refused.required, "original operative refusal");
        assert!(matches!(
            refused.readings[0].value,
            EpochStageValue::Unavailable(_)
        ));
    }
}
