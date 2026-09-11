use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{
    blob, expect, point_bytes, point_section, read_blob, read_point,
};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::Rat;
use std::io::{Read, Write};
const MAGIC_V1: &[u8] = b"HOLONIC-WAVE-RELATION\x01";
const MAGIC_V2: &[u8] = b"HOLONIC-WAVE-RELATION\x02";
const MAGIC_V3: &[u8] = b"HOLONIC-WAVE-RELATION\x03";
const MAGIC_V4: &[u8] = b"HOLONIC-WAVE-RELATION\x04";
const END: &[u8] = b"HOLONIC-WAVE-RELATION-END\x01";
fn false_flag(value: &bool) -> bool {
    !*value
}
fn invalid(e: impl ToString) -> ConstitutiveFibreError {
    ConstitutiveFibreError::Rest(e.to_string())
}

fn validate_unit_real_sum(
    basis: &ResidentSectionRest,
    n: usize,
    q: usize,
) -> Result<(), ConstitutiveFibreError> {
    // The CUDA formation law checks the real current increment in each K row.
    // Recheck that same invariant from the detached exact material before remount.
    let target_current = q
        .checked_add(2 + 6 * n)
        .ok_or(ConstitutiveFibreError::Shape)?;
    let source_current = 2usize
        .checked_add(6 * n)
        .ok_or(ConstitutiveFibreError::Shape)?;
    for row in basis.intervals.chunks_exact(basis.width) {
        let mut sum_lo = BigInt::zero();
        let mut sum_hi = BigInt::zero();
        for i in 0..n {
            let (target_lo, target_hi) = row
                .get(target_current + 2 * i)
                .ok_or(ConstitutiveFibreError::Shape)?;
            let (source_lo, source_hi) = row
                .get(source_current + 2 * i)
                .ok_or(ConstitutiveFibreError::Shape)?;
            sum_lo += BigInt::from(*target_lo) - BigInt::from(*source_lo);
            sum_hi += BigInt::from(*target_hi) - BigInt::from(*source_hi);
        }
        if !sum_lo.is_zero() || !sum_hi.is_zero() {
            return Err(invalid(
                "unit-real-sum relation has a nonzero target real increment",
            ));
        }
    }

    // The two common-real-offset directions are lineality of the lifted chart.
    // Check membership against the complete detached relation with exact rationals;
    // the echelon rows span the complete declared linear relation.
    let mut previous = vec![Rat::zero(); 2 * q];
    let mut current = vec![Rat::zero(); 2 * q];
    for i in 0..n {
        previous[2 + 4 * n + 2 * i] = Rat::one();
        current[2 + 6 * n + 2 * i] = Rat::one();
        current[q + 2 + 4 * n + 2 * i] = Rat::one();
        current[q + 2 + 6 * n + 2 * i] = Rat::one();
    }
    if !row_span_contains(basis, &previous)? || !row_span_contains(basis, &current)? {
        return Err(invalid(
            "unit-real-sum relation omits a common-offset gauge direction",
        ));
    }
    Ok(())
}

fn row_span_contains(
    basis: &ResidentSectionRest,
    vector: &[Rat],
) -> Result<bool, ConstitutiveFibreError> {
    if basis.width != vector.len() || basis.rows == 0 {
        return Err(ConstitutiveFibreError::Shape);
    }
    let mut residual = vector.to_vec();
    for (pivot, row) in basis.intervals.chunks_exact(basis.width).enumerate() {
        if residual[pivot].is_zero() {
            continue;
        }
        if row[pivot].0 == 0 {
            return Ok(false);
        }
        let factor = &residual[pivot] / Rat::from_integer(row[pivot].0.into());
        for column in pivot..basis.width {
            if row[column].0 != 0 {
                residual[column] -= &factor * Rat::from_integer(row[column].0.into());
            }
        }
    }
    Ok(residual.into_iter().all(|value| value.is_zero()))
}
#[derive(Serialize, serde::Deserialize, Debug, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Header {
    roots: usize,
    conditions: usize,
    cut: u64,
    #[serde(default)]
    receiver: WaveSourceReceiver,
    #[serde(default, skip_serializing_if = "false_flag")]
    source: bool,
    #[serde(default, skip_serializing_if = "false_flag")]
    observation: bool,
}
#[derive(Debug, PartialEq, Eq)]
struct SourceContactRest {
    source: ResidentSectionRest,
    prediction: ConstitutiveReturnRest,
    arrival: ConstitutiveReturnRest,
    reaction: ResidentSectionRest,
}

fn validate_observation(
    basis: &ResidentSectionRest,
    observed: &ResidentSectionRest,
    n: usize,
) -> Result<(), ConstitutiveFibreError> {
    let q = n.checked_mul(8).and_then(|v| v.checked_add(2)).ok_or(ConstitutiveFibreError::Shape)?;
    let w = q.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
    point_section(basis, w, w)?;
    point_section(observed, 1, 2 * n + 1)?;
    if observed.intervals[2 * n].0 <= 0 {
        return Err(invalid("observed-next snapshot has a nonpositive denominator"));
    }
    for p in 0..q {
        let row = &basis.intervals[p * w..(p + 1) * w];
        if row[p].0 <= 0 || row[..p].iter().any(|v| v.0 != 0) {
            return Err(invalid("observed-next relation is not a total positive-pivot graph"));
        }
        for j in 0..2 + 4 * n {
            if row[q + j].0 != row[j].0 {
                return Err(invalid("observed-next relation changes lambda or anchor"));
            }
        }
        for j in 0..2 * n {
            if row[q + 2 + 4 * n + j].0 != row[2 + 6 * n + j].0 {
                return Err(invalid("observed-next relation loses its current join"));
            }
        }
    }
    // Check every row, including quadrature and anchor generators, against c'=v*lambda.real.
    let d = BigInt::from(observed.intervals[2 * n].0);
    for row in basis.intervals.chunks_exact(w) {
        for i in 0..2*n {
            if BigInt::from(row[q+2+6*n+i].0)*&d
                != BigInt::from(observed.intervals[i].0)*BigInt::from(row[0].0) {
                return Err(invalid("observed-next relation does not carry c'=v*lambda.real"));
            }
        }
    }

    Ok(())
}

fn validate_source_contact(
    source: &SourceContactRest,
    n: usize,
    receiver: WaveSourceReceiver,
    cut: u64,
    conditions: usize,
) -> Result<(), ConstitutiveFibreError> {
    let r = n.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
    let w = r.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
    point_section(&source.source, 1, 3 * r + 1)?;
    source.prediction.validate()?;
    let f = (3 * n)
        .checked_mul(conditions)
        .and_then(|v| {
            v.checked_add(3 * n)?
                .checked_add(conditions)?
                .checked_mul(2)
        })
        .ok_or(ConstitutiveFibreError::Shape)?;
    if source.prediction.source_width() != f
        || source.prediction.target_width() != r
        || source.prediction.occurrence() != cut
        || source.prediction.source_chart()
            != (ConstitutiveSourceChart::BilinearContact {
                source_complex: 3 * n,
                condition_complex: conditions,
            })
    {
        return Err(invalid("source prediction does not carry its local chart"));
    }
    source.arrival.validate()?;
    if source.arrival.source_width() != 2
        || source.arrival.target_width() != w
        || source.arrival.source_chart() != ConstitutiveSourceChart::Linear
        || source.arrival.occurrence() != cut
        || source.arrival.outside_domain() != source.prediction.outside_domain()
        || source.arrival.field_source() != source.prediction.field_source()
    {
        return Err(invalid("source contact arrival has the wrong linear chart"));
    }
    point_section(&source.reaction, 1, 5 * w + 2)?;
    let a = &source.source.intervals;
    let h = &source.reaction.intervals;
    let sd = BigInt::from(a[3 * r].0);
    let hd = BigInt::from(h[5 * w].0);
    if sd <= BigInt::zero()
        || hd <= BigInt::zero()
        || h[5 * w + 1].0 != i64::from(source.arrival.outside_domain())
    {
        return Err(invalid("source reaction is not admitted"));
    }
    for i in 0..r {
        if BigInt::from(a[i].0) != BigInt::from(a[r + i].0) - BigInt::from(a[2 * r + i].0)
            || BigInt::from(a[2 * r + i].0) * &hd != BigInt::from(h[i].0) * &sd
            || BigInt::from(a[r + i].0) * &hd != BigInt::from(h[r + i].0) * &sd
        {
            return Err(invalid("source reaction loses its actual offered joint"));
        }
    }
    if receiver == WaveSourceReceiver::UnitRealSum {
        source.prediction.validate_zero_real_sum()?;
        for start in [r, 2 * r] {
            let sum: BigInt = (0..n).map(|i| BigInt::from(a[start + 2 * i].0)).sum();
            if sum != sd {
                return Err(invalid(
                    "source reaction is outside its unit-real-sum chart",
                ));
            }
        }
    }
    Ok(())
}
#[derive(Debug, PartialEq, Eq)]
pub struct NormalWaveRelationRest {
    header: Header,
    basis: ResidentSectionRest,
    fixed: ResidentSectionRest,
    source: Option<SourceContactRest>,
    observation: Option<ResidentSectionRest>,
}
impl NormalWaveRelationRest {
    pub(crate) fn is_conditional(&self)->bool { !self.header.source && !self.header.observation }
    pub(crate) fn condition_components(&self)->usize { 2*self.header.conditions }
    pub fn roots(&self) -> usize {
        self.header.roots
    }
    pub fn relation_cut(&self) -> u64 {
        self.header.cut
    }
    pub fn source_receiver(&self) -> WaveSourceReceiver {
        self.header.receiver
    }
    pub fn validate(&self) -> Result<(), ConstitutiveFibreError> {
        let n = self.header.roots;
        let k = self.header.conditions;
        let q = n
            .checked_mul(8)
            .and_then(|v| v.checked_add(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let w = q.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
        let hw = k
            .checked_mul(2)
            .and_then(|v| v.checked_add(1))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if n == 0 || k == 0 || w > u32::MAX as usize {
            return Err(ConstitutiveFibreError::Shape);
        }
        if (self.header.source && self.header.observation)
            || (self.header.observation && self.observation.is_none())
            || (!self.header.observation && self.observation.is_some())
        {
            return Err(invalid("wave relation source and observation are mutually exclusive"));
        }
        point_section(&self.basis, w, w)?;
        point_section(&self.fixed, 1, hw)?;
        if self.fixed.intervals[hw - 1].0 <= 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        for p in 0..w {
            let row = &self.basis.intervals[p * w..(p + 1) * w];
            if row[p].0 < 0
                || row[..p].iter().any(|v| v.0 != 0)
                || (row[p].0 == 0 && row.iter().any(|v| v.0 != 0))
            {
                return Err(invalid(
                    "derived wave relation is not positive-pivot echelon material",
                ));
            }
            // The declared chart preserves lambda and anchor and joins the actual c as next p.
            for j in 0..2 + 4 * n {
                if row[q + j].0 != row[j].0 {
                    return Err(invalid("wave relation changes the retained anchor"));
                }
            }
            if !self.header.source && !self.header.observation {
                for j in 0..2 * n {
                    if row[q + 2 + 4 * n + j].0 != row[2 + 6 * n + j].0 {
                        return Err(invalid("wave relation loses its current join"));
                    }
                }
            } else if (p < q && row[p].0 <= 0) || (p >= q && row.iter().any(|v| v.0 != 0)) {
                return Err(invalid("source passage is not a total functional graph"));
            }
        }
        if !self.header.source && !self.header.observation && self.header.receiver == WaveSourceReceiver::UnitRealSum {
            validate_unit_real_sum(&self.basis, n, q)?;
        }
        if self.header.source {
            validate_source_contact(
                self.source.as_ref().ok_or(ConstitutiveFibreError::Shape)?,
                n,
                self.header.receiver,
                self.header.cut,
                self.header.conditions,
            )?;
        } else if self.source.is_some() {
            return Err(invalid("wave relation source evidence is not declared"));
        }
        if let Some(observed) = &self.observation {
            validate_observation(&self.basis, observed, n)?;
        }
        Ok(())
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        self.validate()?;
        out.write_all(if self.observation.is_some() {
            MAGIC_V4
        } else if self.source.is_some() {
            MAGIC_V3
        } else {
            MAGIC_V2
        })
        .map_err(invalid)?;
        blob(out, &serde_json::to_vec(&self.header).map_err(invalid)?)?;
        blob(out, &point_bytes(&self.basis)?)?;
        blob(out, &point_bytes(&self.fixed)?)?;
        if let Some(source) = &self.source {
            blob(out, &point_bytes(&source.source)?)?;
            blob(
                out,
                &serde_json::to_vec(&source.prediction).map_err(invalid)?,
            )?;
            blob(out, &serde_json::to_vec(&source.arrival).map_err(invalid)?)?;
            blob(out, &point_bytes(&source.reaction)?)?;
        }
        if let Some(observed) = &self.observation {
            blob(out, &point_bytes(observed)?)?;
        }
        out.write_all(END).map_err(invalid)
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut input = input.take(octets);
        let mut magic = vec![0u8; MAGIC_V1.len()];
        input.read_exact(&mut magic).map_err(invalid)?;
        if magic != MAGIC_V1 && magic != MAGIC_V2 && magic != MAGIC_V3 && magic != MAGIC_V4 {
            return Err(invalid("wave relation magic is absent"));
        }
        let header: Header = serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        if magic == MAGIC_V1 && (header.receiver != WaveSourceReceiver::Direct || header.source) {
            return Err(invalid(
                "legacy wave relation declares an unknown receiver chart",
            ));
        }
        let basis = read_point(&read_blob(&mut input)?)?;
        let fixed = read_point(&read_blob(&mut input)?)?;
        let source = if magic == MAGIC_V3 {
            if !header.source {
                return Err(invalid("v3 wave relation omits its source evidence"));
            }
            Some(SourceContactRest {
                source: read_point(&read_blob(&mut input)?)?,
                prediction: serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?,
                arrival: serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?,
                reaction: read_point(&read_blob(&mut input)?)?,
            })
        } else {
            if header.source {
                return Err(invalid("source evidence requires wave relation wire v3"));
            }
            None
        };
        let observation = if magic == MAGIC_V4 {
            if !header.observation || header.source {
                return Err(invalid("v4 wave relation has invalid observation declaration"));
            }
            Some(read_point(&read_blob(&mut input)?)?)
        } else {
            if header.observation { return Err(invalid("observation requires wave relation wire v4")); }
            None
        };
        expect(&mut input, END)?;
        let mut extra = [0u8; 1];
        if input.read(&mut extra).map_err(invalid)? != 0 {
            return Err(invalid("trailing wave relation data"));
        }
        let rest = Self {
            header,
            basis,
            fixed,
            source,
            observation,
        };
        rest.validate()?;
        Ok(rest)
    }
    pub fn remount<'c>(
        self,
        s: &'c ResidentSurface<'c>,
    ) -> Result<ResidentWaveRelation<'c>, ConstitutiveFibreError> {
        self.validate()?;
        let source = if let Some(source) = self.source {
            let snapshot = s.mount_section_rest(&source.source)?;
            let contact = super::source::prepare_source_contact(
                s,
                self.header.roots,
                self.header.receiver,
                ResidentConstitutiveCurrent::rational(&snapshot)?,
                source.prediction.remount(s)?,
                None,
            )?;
            if contact.arrival.rest()? != source.arrival
                || s.detach_section(&contact.reaction, 64)? != source.reaction
            {
                return Err(invalid(
                    "source reaction does not follow its complete prediction",
                ));
            }
            let basis = super::source::source_basis(s, self.header.roots, &contact.reaction)?;
            if s.detach_section(&basis, 64)? != self.basis {
                return Err(invalid("source map does not follow its actual reaction"));
            }
            Some((basis, contact))
        } else {
            None
        };
        let observation = if let Some(observed) = self.observation {
            let snapshot = s.mount_section_rest(&observed)?;
            let (basis, normalized) = super::observation::observation_basis(s, self.header.roots, ResidentConstitutiveCurrent::rational(&snapshot)?)?;
            if s.detach_section(&basis, 64)? != self.basis
                || s.detach_section(&normalized, 64)? != observed {
                return Err(invalid("observed-next map does not follow its normalized snapshot"));
            }
            Some((basis, snapshot))
        } else { None };
        let (basis, source, observation) = match (source, observation) {
            (Some((basis, source)), None) => (basis, Some(source), None),
            (None, Some((basis, snapshot))) => (basis, None, Some(snapshot)),
            (None, None) => (s.mount_section_rest(&self.basis)?, None, None),
            (Some(_), Some(_)) => return Err(invalid("wave relation source and observation are mutually exclusive")),
        };
        let mut relation = ResidentWaveRelation::new(
            s,
            basis,
            s.mount_section_rest(&self.fixed)?,
            self.header.roots,
            self.header.conditions,
            self.header.cut,
            Rc::new(()),
            self.header.receiver,
        );
        relation.source = source;
        if let Some(snapshot) = observation {
            relation.observation = Some(snapshot);
        }
        Ok(relation)
    }
}
impl ResidentWaveRelation<'_> {
    pub fn rest(&self) -> Result<NormalWaveRelationRest, ConstitutiveFibreError> {
        let rest = NormalWaveRelationRest {
            header: Header {
                roots: self.roots,
                conditions: self.condition_complex,
                cut: self.relation_cut,
                receiver: self.receiver,
                source: self.source.is_some(),
                observation: self.observation.is_some(),
            },
            basis: self.surface.detach_section(&self.basis, 64)?,
            fixed: self.surface.detach_section(&self.fixed, 64)?,
            source: self
                .source
                .as_ref()
                .map(
                    |source| -> Result<SourceContactRest, ConstitutiveFibreError> {
                        Ok(SourceContactRest {
                            source: self.surface.detach_section(&source.source, 64)?,
                            prediction: source.prediction.rest()?,
                            arrival: source.arrival.rest()?,
                            reaction: self.surface.detach_section(&source.reaction, 64)?,
                        })
                    },
                )
                .transpose()?,
            observation: self
                .observation
                .as_ref()
                .map(|v| self.surface.detach_section(v, 64))
                .transpose()?,
        };
        rest.validate()?;
        Ok(rest)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn specimen() -> NormalWaveRelationRest {
        let q = 10;
        let w = 2 * q;
        let mut rows = vec![(0, 0); w * w];
        for i in 0..q {
            rows[i * w + i] = (1, 1);
            if i < 6 {
                rows[i * w + q + i] = (1, 1);
            }
            if i >= 8 {
                rows[i * w + q + i - 2] = (1, 1);
                rows[i * w + q + i] = (1, 1);
            }
        }
        NormalWaveRelationRest {
            header: Header {
                roots: 1,
                conditions: 1,
                cut: 0,
                receiver: WaveSourceReceiver::UnitRealSum,
                source: false,
                observation: false,
            },
            source: None,
            observation: None,
            basis: ResidentSectionRest::found(w, w, ResidentGrain(0), 64, rows).unwrap(),
            fixed: ResidentSectionRest::found(
                1,
                3,
                ResidentGrain(0),
                64,
                vec![(1, 1), (0, 0), (1, 1)],
            )
            .unwrap(),
        }
    }
    fn observation_specimen() -> NormalWaveRelationRest {
        let mut rest = specimen();
        rest.header.observation = true;
        rest.observation = Some(ResidentSectionRest::found(1,3,ResidentGrain(0),64,
            vec![(3,3),(4,4),(1,1)]).unwrap());
        for row in rest.basis.intervals.chunks_exact_mut(20) {row[18]=(0,0);row[19]=(0,0);}
        rest.basis.intervals[18]=(3,3);rest.basis.intervals[19]=(4,4);
        rest
    }
    #[test]
    fn observation_rest_checks_all_rows_and_round_trips_its_payload() {
        let rest=observation_specimen();rest.validate().unwrap();
        let mut bytes=Vec::new();rest.write(&mut bytes).unwrap();
        assert_eq!(NormalWaveRelationRest::read(&mut bytes.as_slice(),bytes.len() as u64).unwrap(),rest);
        let mut wrong=observation_specimen();wrong.basis.intervals[20+18]=(1,1);
        assert!(wrong.validate().is_err());
        let mut wrong=observation_specimen();wrong.header.source=true;assert!(wrong.validate().is_err());
        let mut wrong=observation_specimen();wrong.basis.intervals[6*20+6]=(0,0);assert!(wrong.validate().is_err());
    }
    #[test]
    fn receiver_rest_checks_complete_gauge_and_increment() {
        let rest = specimen();
        rest.validate().unwrap();
        let mut bytes = Vec::new();
        rest.write(&mut bytes).unwrap();
        assert_eq!(
            NormalWaveRelationRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap(),
            rest
        );
        let mut wrong = specimen();
        wrong.basis.intervals[8 * 20 + 18] = (2, 2);
        assert!(wrong.validate().is_err());
        let mut absent = specimen();
        absent.basis.intervals[6 * 20 + 6] = (0, 0);
        assert!(absent.validate().is_err());
    }
    #[test]
    fn legacy_wave_relation_has_only_the_direct_receiver() {
        let rest = specimen();
        for receiver in [None, Some(WaveSourceReceiver::UnitRealSum)] {
            let mut bytes = Vec::new();
            bytes.extend_from_slice(MAGIC_V1);
            let mut header = serde_json::json!({"roots":1,"conditions":1,"cut":0});
            if let Some(receiver) = receiver {
                header["receiver"] = serde_json::to_value(receiver).unwrap();
            }
            blob(&mut bytes, &serde_json::to_vec(&header).unwrap()).unwrap();
            blob(&mut bytes, &point_bytes(&rest.basis).unwrap()).unwrap();
            blob(&mut bytes, &point_bytes(&rest.fixed).unwrap()).unwrap();
            bytes.extend_from_slice(END);
            let decoded = NormalWaveRelationRest::read(&mut bytes.as_slice(), bytes.len() as u64);
            if receiver.is_none() {
                assert_eq!(
                    decoded.unwrap().source_receiver(),
                    WaveSourceReceiver::Direct
                );
            } else {
                assert!(decoded.is_err());
            }
        }
    }
    #[test]
    #[ignore = "requires CUDA; rest must recover complete source reactions, not only matching endpoints"]
    fn source_rest_rejects_changed_returned_normal() {
        use crate::embedding_fiber::ResidentReadout;
        let ro = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&ro).unwrap();
        let point = |v: &[i64]| {
            surface
                .mount_section_rest(
                    &ResidentSectionRest::found(
                        1,
                        v.len(),
                        ResidentGrain(0),
                        64,
                        v.iter().map(|v| (*v, *v)).collect(),
                    )
                    .unwrap(),
                )
                .unwrap()
        };
        let mut local =
            ResidentConstitutiveFibre::found_bilinear_contact(&surface, 3, 1, 1).unwrap();
        let source = point(&[0, 0, 1, 0, 1, 0]);
        let h = point(&[1, 0]);
        let eta = point(&[0, 0]);
        local
            .advance_bilinear_contact(
                ResidentConstitutiveCurrent::integers(&source).unwrap(),
                ResidentConstitutiveCurrent::integers(&h).unwrap(),
                Some(ResidentConstitutiveCurrent::integers(&eta).unwrap()),
            )
            .unwrap();
        let relation = local
            .read_wave_relation(ResidentConstitutiveCurrent::integers(&h).unwrap(), 1)
            .unwrap();
        let map = relation
            .read_source_contact(
                &local,
                ResidentConstitutiveCurrent::integers(&source).unwrap(),
            )
            .unwrap();
        let mut rest = map.rest().unwrap();
        let wire = rest.source.as_mut().unwrap();
        wire.reaction.intervals[12] = (2, 2);
        rest.validate().unwrap();
        assert!(rest.remount(&surface).is_err());
    }
}
