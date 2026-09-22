//! Explicit incident codec admission and atomic E/R cohort growth.
use super::*;
use crate::alpha::exposure::{ExposureOccurrence, ExposurePartition};
use holonic_engine::{
    codec_recovery::SymbolAlphabet,
    native_ecology::constitutive_fibre::{BoundaryMaterialSeed, NativeNormalPrior},
};

impl<'c> NativeFieldSession<'c> {
    pub fn admit_incident_source_texts(&mut self, texts: &[String]) -> Result<Value> {
        if self.presentation.spec.source_chart
            == crate::native::field_session::FieldSourceChart::GeneratorMachine
        {
            return self.admit_generator_source_texts(texts);
        }
        let (new_labels, additions) =
            discover_unseen_scalars(&self.presentation.spec.symbols, texts);
        let new_chart = {
            if additions.is_empty() {
                return Ok(
                    json!({"admitted":[],"codec_version":self.incident.as_ref().ok_or_else(||invalid("incident session state"))?.receiver.codec_version()}),
                );
            }
            let alphabet = SymbolAlphabet::declared(
                new_labels
                    .iter()
                    .map(|label| (label.clone(), label.as_bytes().to_vec()))
                    .collect(),
            )
            .map_err(invalid)?;
            SymbolCurrentChart::declared(alphabet)
        };
        let old_count = self.presentation.spec.symbols.len();
        let identities = (old_count..new_labels.len()).collect::<Vec<_>>();
        let version = self
            .incident
            .as_ref()
            .ok_or_else(|| invalid("incident session state"))?
            .receiver
            .codec_version()
            .checked_add(1)
            .ok_or_else(|| invalid("incident codec version"))?;
        self.admit_incident_source_symbols_with_chart(identities, new_labels, new_chart, version)
    }

    fn admit_incident_source_symbols_with_chart(
        &mut self,
        identities: Vec<usize>,
        new_labels: Vec<String>,
        new_chart: SymbolCurrentChart,
        codec_version: u64,
    ) -> Result<Value> {
        let options = self
            .presentation
            .spec
            .incident
            .as_ref()
            .ok_or_else(|| invalid("incident codec declaration"))?;
        let (encoder_append, cohort) = {
            let incident = self
                .incident
                .as_ref()
                .ok_or_else(|| invalid("incident session state"))?;
            let current = incident.encoder.producing_views().len();
            let new_count = current
                .checked_add(identities.len())
                .ok_or_else(|| invalid("incident codec extent"))?;
            if new_count != new_labels.len() {
                return Err(invalid("incident codec source count"));
            }
            let append = incident
                .encoder
                .prepare_append_from_seed(new_count, &identities)?;
            let seed = BoundaryMaterialSeed::new(
                options.material_seed,
                self.presentation.spec.fractional_bits,
            );
            let maps = seed
                .initial_maps(new_count, incident.width / 2)
                .map_err(invalid)?;
            let decoder_rows = maps.decoder.into_iter().skip(current).collect::<Vec<_>>();
            let prior = NativeNormalPrior::from_coefficients(decoder_rows).map_err(invalid)?;
            let cohort = incident.receiver.prepare_text_cohort_with_prior(
                self.surface,
                identities.len(),
                codec_version,
                prior,
            )?;
            (append, cohort)
        };
        let incident = self
            .incident
            .as_mut()
            .ok_or_else(|| invalid("incident session state"))?;
        let expected_start = incident
            .receiver
            .cohorts()
            .iter()
            .map(|cohort| cohort.class_count)
            .sum::<usize>();
        if cohort.cohort.class_start != expected_start
            || cohort.cohort.codec_version <= incident.receiver.codec_version()
        {
            return Err(invalid("incident receiver cohort publication precheck"));
        }
        incident.encoder.publish_append(encoder_append)?;
        incident.receiver.publish_text_cohort(cohort)?;
        self.presentation.spec.symbols = new_labels;
        self.presentation.chart = new_chart;
        Ok(json!({"codec_version":codec_version,"admitted":identities,
            "source_count":self.presentation.spec.symbols.len()}))
    }

    pub fn admit_incident_development_occurrence(
        &mut self,
        occurrence: &ExposureOccurrence,
    ) -> Result<Value> {
        if occurrence.partition != ExposurePartition::Development {
            return Err(invalid("incident target admission is development-only"));
        }
        let texts = occurrence
            .development_parts()
            .map_err(invalid)?
            .iter()
            .map(|part| {
                part.text
                    .clone()
                    .ok_or_else(|| invalid("incident development part has no text"))
            })
            .collect::<Result<Vec<_>>>()?;
        self.admit_incident_source_texts(&texts)
    }
}

fn discover_unseen_scalars(existing: &[String], texts: &[String]) -> (Vec<String>, Vec<String>) {
    let mut labels = existing.to_vec();
    let mut additions = Vec::new();
    for text in texts {
        for scalar in text.chars() {
            let label = scalar.to_string();
            if !labels.iter().any(|known| known == &label) {
                labels.push(label.clone());
                additions.push(label);
            }
        }
    }
    (labels, additions)
}

#[cfg(test)]
mod tests {
    use super::discover_unseen_scalars;

    #[test]
    fn unseen_unicode_is_admitted_in_encounter_order() {
        let (labels, additions) =
            discover_unseen_scalars(&["a".into(), "b".into()], &["bλ".into(), "λμ".into()]);
        assert_eq!(additions, vec!["λ", "μ"]);
        assert_eq!(labels, vec!["a", "b", "λ", "μ"]);
    }
}
