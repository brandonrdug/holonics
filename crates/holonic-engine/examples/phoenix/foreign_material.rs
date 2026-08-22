//! Example-only foreign source adapter. It is intentionally absent from production Phoenix.

use holonic_engine::foreign_map::ForeignDtype;
use holonic_engine::ported_operation::{PortedOperationComplex, SourceTestimony};
use holonic_engine::source_occurrence::{
    BindingValidation, OccurrenceWitness, OccurrenceWitnessRefusal, RegionIdentity,
    SourceOccurrence,
};
use holonic_engine::streamed_standing::StagedRegion;

use super::super::resident_layer::Source;
use super::super::tower;
use super::MaterialSource;

pub struct ForeignMaterialSource {
    pub source: Source,
    pub witness: ForeignOccurrenceWitness,
}

/// Example-only chart transition from production's path-free rested symbols back to the live
/// source occurrence. The production complex is cloned locally, each rested symbol receives this
/// authenticated source's locator, and the foreign witness performs its ordinary exact resolution.
pub struct ForeignOccurrenceWitness {
    inner: SourceOccurrence,
}

impl OccurrenceWitness for ForeignOccurrenceWitness {
    fn witness(&self) -> &'static str {
        "foreign source rebased from rested testimony"
    }

    fn validate(
        &self,
        complex: &PortedOperationComplex,
    ) -> Result<Vec<BindingValidation>, OccurrenceWitnessRefusal> {
        let mut foreign = complex.clone();
        for operation in foreign.operations.values_mut() {
            for testimony in &mut operation.testimony {
                if let SourceTestimony::RestedImplementation { symbol } = testimony {
                    *testimony = SourceTestimony::Implementation {
                        locator: self.inner.implementation.locator.clone(),
                        symbol: symbol.clone(),
                    };
                }
            }
        }
        Ok(self.inner.validate(&foreign)?)
    }
}

impl ForeignMaterialSource {
    pub fn open(root: &str, content_sha256: Option<String>) -> Result<Self, String> {
        let source = Source::open(root)?;
        let mut regions = std::collections::BTreeMap::new();
        for layer in 0..tower::LAYERS {
            for name in tower::populations(layer) {
                regions.insert(name.clone(), source.region(&name, None)?);
            }
            let scalar = tower::named(layer, "layer_scalar");
            regions.insert(scalar.clone(), source.region(&scalar, None)?);
            let whole = source
                .container
                .tensor(tower::PLE_MODEL_PROJECTION)
                .map_err(|e| e.to_string())?;
            let dim = whole.shape[1];
            let mut slice = source.region(tower::PLE_MODEL_PROJECTION, None)?;
            slice.population = format!(
                "{} rows {}..{}",
                tower::PLE_MODEL_PROJECTION,
                tower::PLE_WIDTH * layer,
                tower::PLE_WIDTH * (layer + 1)
            );
            slice.shape = vec![tower::PLE_WIDTH, dim];
            slice.start += (tower::PLE_WIDTH * layer * dim * 2) as u64;
            slice.end = slice.start + (tower::PLE_WIDTH * dim * 2) as u64;
            regions.insert(slice.population.clone(), slice);
        }
        for name in [
            tower::PLE_MODEL_PROJECTION,
            tower::PLE_PROJECTION_NORM,
            tower::EMBED,
            tower::PLE_EMBED,
            tower::FINAL_NORM,
        ] {
            regions.insert(name.to_owned(), source.region(name, None)?);
        }
        let witness =
            super::super::resident_layer::source_occurrence(root, regions, content_sha256)?;
        Ok(Self {
            source,
            witness: ForeignOccurrenceWitness { inner: witness },
        })
    }
    pub fn whole(&mut self, population: &str) -> Result<(Vec<u16>, Vec<usize>), String> {
        self.source.whole(population)
    }
}

impl MaterialSource for ForeignMaterialSource {
    fn file(&self) -> Result<&std::fs::File, String> {
        Ok(&self.source.file)
    }
    fn file_octets(&self) -> Result<u64, String> {
        Ok(self.source.container.file_octets)
    }
    fn region(&self, population: &str) -> Result<RegionIdentity, String> {
        self.source.region(population, None)
    }
    fn staged(&self, population: &str) -> Result<StagedRegion, String> {
        let tensor = self
            .source
            .container
            .tensor(population)
            .map_err(|e| e.to_string())?;
        let words = (tensor.end - tensor.start) / 2;
        let dim = *tensor.shape.last().unwrap_or(&0);
        if tensor.dtype != ForeignDtype::Bf16 {
            return Err(format!("{population} is {:?}; BF16 required", tensor.dtype));
        }
        Ok(StagedRegion {
            population: population.to_owned(),
            start: self.source.container.payload_base() + tensor.start,
            words: u32::try_from(words).map_err(|_| format!("{population} is too wide"))?,
            dim,
        })
    }
    fn rows(
        &mut self,
        population: &str,
        from: usize,
        count: usize,
    ) -> Result<(Vec<u16>, usize), String> {
        self.source.rows(population, from, count)
    }
    fn occurrence(&self) -> &dyn OccurrenceWitness {
        &self.witness
    }
    fn source_identity(&self) -> String {
        let container = &self.witness.inner.container;
        format!(
            "{} octets, header {} octets, header sha256 {}, content sha256 {:?}, identity {:?}",
            container.octets,
            container.header_octets,
            container.header_sha256,
            container.content_sha256,
            container.identity
        )
    }
    fn verify_stable(&self) -> Result<(), String> {
        self.witness
            .inner
            .container
            .verify_still()
            .map_err(|e| e.to_string())
    }
}
