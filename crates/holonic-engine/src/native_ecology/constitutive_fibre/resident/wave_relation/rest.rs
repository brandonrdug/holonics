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
const END: &[u8] = b"HOLONIC-WAVE-RELATION-END\x01";
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
}
#[derive(Debug, PartialEq, Eq)]
pub struct NormalWaveRelationRest {
    header: Header,
    basis: ResidentSectionRest,
    fixed: ResidentSectionRest,
}
impl NormalWaveRelationRest {
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
            for j in 0..2 * n {
                if row[q + 2 + 4 * n + j].0 != row[2 + 6 * n + j].0 {
                    return Err(invalid("wave relation loses its current join"));
                }
            }
        }
        if self.header.receiver == WaveSourceReceiver::UnitRealSum {
            validate_unit_real_sum(&self.basis, n, q)?;
        }
        Ok(())
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        self.validate()?;
        out.write_all(MAGIC_V2).map_err(invalid)?;
        blob(out, &serde_json::to_vec(&self.header).map_err(invalid)?)?;
        blob(out, &point_bytes(&self.basis)?)?;
        blob(out, &point_bytes(&self.fixed)?)?;
        out.write_all(END).map_err(invalid)
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut input = input.take(octets);
        let mut magic = vec![0u8; MAGIC_V1.len()];
        input.read_exact(&mut magic).map_err(invalid)?;
        if magic != MAGIC_V1 && magic != MAGIC_V2 {
            return Err(invalid("wave relation magic is absent"));
        }
        let header: Header = serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        if magic == MAGIC_V1 && header.receiver != WaveSourceReceiver::Direct {
            return Err(invalid(
                "legacy wave relation declares an unknown receiver chart",
            ));
        }
        let basis = read_point(&read_blob(&mut input)?)?;
        let fixed = read_point(&read_blob(&mut input)?)?;
        expect(&mut input, END)?;
        let mut extra = [0u8; 1];
        if input.read(&mut extra).map_err(invalid)? != 0 {
            return Err(invalid("trailing wave relation data"));
        }
        let rest = Self {
            header,
            basis,
            fixed,
        };
        rest.validate()?;
        Ok(rest)
    }
    pub fn remount<'c>(
        self,
        s: &'c ResidentSurface<'c>,
    ) -> Result<ResidentWaveRelation<'c>, ConstitutiveFibreError> {
        self.validate()?;
        Ok(ResidentWaveRelation::new(
            s,
            s.mount_section_rest(&self.basis)?,
            s.mount_section_rest(&self.fixed)?,
            self.header.roots,
            self.header.conditions,
            self.header.cut,
            Rc::new(()),
            self.header.receiver,
        ))
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
            },
            basis: self.surface.detach_section(&self.basis, 64)?,
            fixed: self.surface.detach_section(&self.fixed, 64)?,
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
            },
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
}
