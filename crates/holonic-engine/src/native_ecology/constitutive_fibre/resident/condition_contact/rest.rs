//! Current standing, not the previous contact report or an observation history.
use super::*;
use std::io::{Read, Write};

#[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ConditionCurrentRest {
    schema: String,
    source_chart: ConstitutiveSourceChart,
    metric: ConditionContactMetric,
    contacts: u64,
    /// Exact current numerators followed by their original common denominator.
    words: Vec<i64>,
}
impl ConditionCurrentRest {
    pub fn source_chart(&self) -> ConstitutiveSourceChart {
        self.source_chart
    }
    pub fn contacts(&self) -> u64 {
        self.contacts
    }
    pub fn width(&self) -> usize {
        self.words.len().saturating_sub(1)
    }
    pub fn current_words(&self) -> &[i64] {
        &self.words
    }
    pub fn validate(&self) -> Result<(), ConstitutiveFibreError> {
        let c = self.width();
        if self.schema != "holonics.condition-current.v1"
            || c == 0
            || c % 2 != 0
            || c.checked_mul(5)
                .and_then(|n| n.checked_add(2))
                .is_none_or(|n| n > u32::MAX as usize)
            || self.words.last().is_none_or(|d| *d <= 0)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let ConstitutiveSourceChart::BilinearContact {
            source_complex,
            condition_complex,
        } = self.source_chart
        else {
            return Err(ConstitutiveFibreError::Shape);
        };
        if source_complex == 0 || condition_complex.checked_mul(2) != Some(c) {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(())
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        self.validate()?;
        serde_json::to_writer(out, self).map_err(|e| ConstitutiveFibreError::Rest(e.to_string()))
    }
    pub fn read(input: &mut impl Read) -> Result<Self, ConstitutiveFibreError> {
        let value: Self = serde_json::from_reader(input)
            .map_err(|e| ConstitutiveFibreError::Rest(e.to_string()))?;
        value.validate()?;
        Ok(value)
    }
    pub fn remount<'c>(
        self,
        surface: &'c ResidentSurface<'c>,
    ) -> Result<ResidentConditionCurrent<'c>, ConstitutiveFibreError> {
        self.validate()?;
        let c = self.width();
        // Only actual current is restored. The unused predecessor/normal slots are a stationary
        // mount frame, not a claim to reconstruct the last contact's historical receipt.
        let mut values = vec![(0, 0); 5 * c + 2];
        for i in 0..c {
            values[i] = (self.words[i], self.words[i]);
            values[c + i] = values[i];
        }
        values[5 * c] = (self.words[c], self.words[c]);
        let section = surface.mount_section_rest(
            &ResidentSectionRest::found(1, values.len(), ResidentGrain(0), 64, values)
                .map_err(|_| ConstitutiveFibreError::Shape)?,
        )?;
        Ok(ResidentConditionCurrent {
            surface,
            section: Rc::new(section),
            source_chart: self.source_chart,
            metric: self.metric,
            width: c,
            contacts: self.contacts,
        })
    }
}
impl ResidentConditionCurrent<'_> {
    pub fn rest(&self) -> Result<ConditionCurrentRest, ConstitutiveFibreError> {
        let data = self.surface.read_out(&self.section)?;
        let c = self.width;
        if data.iter().any(|(a, b)| a != b) || data[5 * c].0 <= 0 {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let mut words = data[c..2 * c].iter().map(|p| p.0).collect::<Vec<_>>();
        words.push(data[5 * c].0);
        let value = ConditionCurrentRest {
            schema: "holonics.condition-current.v1".into(),
            source_chart: self.source_chart,
            metric: self.metric,
            contacts: self.contacts,
            words,
        };
        value.validate()?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn current_wire_preserves_words_and_refuses_incompatible_condition_shape() {
        let value = ConditionCurrentRest {
            schema: "holonics.condition-current.v1".into(),
            source_chart: ConstitutiveSourceChart::BilinearContact {
                source_complex: 1,
                condition_complex: 1,
            },
            metric: ConditionContactMetric::UnitAdmittanceRealification,
            contacts: 7,
            words: vec![3, 4, 5],
        };
        let mut bytes = Vec::new();
        value.write(&mut bytes).unwrap();
        assert_eq!(
            ConditionCurrentRest::read(&mut bytes.as_slice()).unwrap(),
            value
        );
        let mut wrong = value;
        wrong.words.push(1);
        assert!(wrong.validate().is_err());
        wrong.words.pop();
        wrong.source_chart = ConstitutiveSourceChart::Linear;
        assert!(wrong.validate().is_err());
    }
}
