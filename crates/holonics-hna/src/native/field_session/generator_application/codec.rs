//! Atomic generator E/R codec admission.

use super::*;
use holonic_engine::codec_recovery::SymbolAlphabet;
use holonic_engine::native_ecology::constitutive_fibre::{BoundaryMaterialSeed, NativeNormalPrior};

impl<'c> NativeFieldSession<'c> {
    pub fn admit_generator_source_texts(&mut self, texts: &[String]) -> Result<Value> {
        let (new_labels, additions) =
            discover_unseen_scalars(&self.presentation.spec.symbols, texts);
        if additions.is_empty() {
            let version = self
                .generator
                .as_ref()
                .ok_or_else(|| invalid("generator presentation"))?
                .receiver
                .inner()
                .codec_version();
            return Ok(json!({"admitted": [], "codec_version": version}));
        }
        let options = self
            .presentation
            .spec
            .generator
            .as_ref()
            .ok_or_else(|| invalid("generator session declaration"))?;
        let model = self
            .generator
            .as_ref()
            .ok_or_else(|| invalid("generator presentation"))?;
        let current = model.encoder.producing_views().len();
        let new_count = current
            .checked_add(additions.len())
            .ok_or_else(|| invalid("generator codec extent"))?;
        if new_count != new_labels.len() {
            return Err(invalid("generator codec source count"));
        }
        let identities = (current..new_count).collect::<Vec<_>>();
        let codec_version = model
            .receiver
            .inner()
            .codec_version()
            .checked_add(1)
            .ok_or_else(|| invalid("generator codec version"))?;
        let seed = BoundaryMaterialSeed::new(
            options.material_seed,
            self.presentation.spec.fractional_bits,
        );
        // E_in owns 3 real source coordinates per injection site; R_text owns
        // six complex coordinates per receiving port. They are separate charts.
        let encoder_append = model
            .encoder
            .prepare_append_from_seed(new_count, &identities)?;
        let decoder_maps = seed
            .initial_maps(
                new_count,
                options
                    .receiver
                    .ports
                    .len()
                    .checked_mul(6)
                    .ok_or_else(|| invalid("generator receiver chart extent"))?,
            )
            .map_err(invalid)?;
        let decoder_rows = decoder_maps
            .decoder
            .into_iter()
            .skip(current)
            .collect::<Vec<_>>();
        let prior = NativeNormalPrior::from_coefficients(decoder_rows).map_err(invalid)?;
        let cohort = model.receiver.inner().prepare_text_cohort_with_prior(
            self.surface,
            additions.len(),
            codec_version,
            prior,
        )?;
        // All declarations and resident successor material are prepared before
        // either owner is mutated.
        let expected_start = model
            .receiver
            .inner()
            .cohorts()
            .iter()
            .map(|cohort| cohort.class_count)
            .sum::<usize>();
        if cohort.cohort.class_start != expected_start
            || cohort.cohort.codec_version <= model.receiver.inner().codec_version()
        {
            return Err(invalid("generator receiver cohort publication precheck"));
        }
        let new_chart = SymbolAlphabet::declared(
            new_labels
                .iter()
                .map(|label| (label.clone(), label.as_bytes().to_vec()))
                .collect(),
        )
        .map_err(invalid)?;
        let model = self
            .generator
            .as_mut()
            .ok_or_else(|| invalid("generator presentation"))?;
        model.encoder.publish_append(encoder_append)?;
        model.receiver.inner_mut().publish_text_cohort(cohort)?;
        self.presentation.spec.symbols = new_labels;
        self.presentation.chart = SymbolCurrentChart::declared(new_chart);
        Ok(json!({
            "codec_version": codec_version,
            "admitted": identities,
            "source_count": self.presentation.spec.symbols.len(),
        }))
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
