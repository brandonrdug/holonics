use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;
use serde_json::Value;
use thiserror::Error;

use crate::foreign_map::{ForeignContainer, ForeignDtype, ForeignTensor};

use super::ForeignConfigurationChart;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ExteriorModality {
    Text,
    Image,
    Video,
    Audio,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ForeignTransportFamilyKind {
    Language,
    Vision,
    Audio,
    VisionProjection,
    AudioProjection,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ForeignTransportFamilyChart {
    pub kind: ForeignTransportFamilyKind,
    pub tensor_names: Vec<String>,
    pub tensor_population: usize,
    pub declared_octets: u64,
    pub rank_population: BTreeMap<usize, usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Gemma4ExteriorTransportChart {
    pub configuration_address: String,
    pub processor_address: String,
    pub container_address: String,
    pub architecture: String,
    pub model_type: String,
    pub input_modalities: BTreeSet<ExteriorModality>,
    pub output_modality: ExteriorModality,
    pub shared_carrier_extent: usize,
    pub text_layer_population: usize,
    pub vision_layer_population: usize,
    pub audio_layer_population: usize,
    pub vocabulary_extent: usize,
    pub image_token_id: u64,
    pub audio_token_id: u64,
    pub video_token_id: u64,
    pub image_soft_token_extent: usize,
    pub audio_soft_token_extent: usize,
    pub sampled_video_frame_extent: usize,
    pub audio_sampling_rate: u64,
    pub families: Vec<ForeignTransportFamilyChart>,
    pub tensor_population: usize,
    pub payload_octets: u64,
    pub unclassified_tensors: BTreeSet<String>,
    pub source_names_are_cold: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ForeignModalityExcitationTestimony {
    pub occurrence: String,
    pub modality: ExteriorModality,
    pub activated_tensors: BTreeSet<String>,
    pub interventions: BTreeSet<String>,
    pub receiver_consequences: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AdmittedForeignModalityExcitation {
    pub occurrence: String,
    pub modality: ExteriorModality,
    pub activated_tensors: BTreeSet<String>,
    pub interventions: BTreeSet<String>,
    pub receiver_consequences: BTreeSet<String>,
    pub source_coordinates_remain_cold: bool,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ForeignMultimodalChartError {
    #[error("{address}: the foreign chart is malformed at {field}")]
    Malformed {
        address: String,
        field: &'static str,
    },
    #[error("the Gemma 4 exterior chart has an unknown tensor family: {0}")]
    UnknownTensor(String),
    #[error("the Gemma 4 exterior chart is missing or mis-shapes {0}")]
    Projection(&'static str),
    #[error("the foreign modality excitation is empty or leaves its declared tensor family")]
    Excitation,
}

impl Gemma4ExteriorTransportChart {
    pub fn from_charts(
        configuration: &ForeignConfigurationChart,
        processor: &ForeignConfigurationChart,
        container: &ForeignContainer,
    ) -> Result<Self, ForeignMultimodalChartError> {
        let config = json_root(configuration)?;
        let processing = json_root(processor)?;
        let architecture = string_array(&config, "architectures")?
            .into_iter()
            .next()
            .filter(|architecture| architecture == "Gemma4ForConditionalGeneration")
            .ok_or_else(|| malformed(configuration, "architectures"))?;
        let model_type = string(&config, "model_type")?;
        if model_type != "gemma4" {
            return Err(malformed(configuration, "model_type"));
        }
        let text = object(&config, "text_config", configuration)?;
        let vision = object(&config, "vision_config", configuration)?;
        let audio = object(&config, "audio_config", configuration)?;
        let shared_carrier_extent = usize_value(text, "hidden_size", configuration)?;
        let text_layer_population = usize_value(text, "num_hidden_layers", configuration)?;
        let vision_layer_population = usize_value(vision, "num_hidden_layers", configuration)?;
        let audio_layer_population = usize_value(audio, "num_hidden_layers", configuration)?;
        let vocabulary_extent = usize_value(text, "vocab_size", configuration)?;
        let image_token_id = u64_value(&config, "image_token_id", configuration)?;
        let audio_token_id = u64_value(&config, "audio_token_id", configuration)?;
        let video_token_id = u64_value(&config, "video_token_id", configuration)?;
        let processing_fields = processing
            .as_object()
            .ok_or_else(|| malformed(processor, "root"))?;
        let image_soft_token_extent =
            usize_value(processing_fields, "image_seq_length", processor)?;
        let audio_soft_token_extent =
            usize_value(processing_fields, "audio_seq_length", processor)?;
        let video_processor = object(&processing, "video_processor", processor)?;
        let sampled_video_frame_extent = usize_value(video_processor, "num_frames", processor)?;
        let feature_extractor = object(&processing, "feature_extractor", processor)?;
        let audio_sampling_rate = u64_object_value(feature_extractor, "sampling_rate", processor)?;

        require_projection(
            container,
            "model.embed_vision.embedding_projection.weight",
            &[
                shared_carrier_extent,
                usize_value(vision, "hidden_size", configuration)?,
            ],
        )?;
        require_projection(
            container,
            "model.embed_audio.embedding_projection.weight",
            &[
                shared_carrier_extent,
                usize_value(audio, "output_proj_dims", configuration)?,
            ],
        )?;
        require_projection(
            container,
            "model.language_model.embed_tokens.weight",
            &[vocabulary_extent, shared_carrier_extent],
        )?;

        let mut members = BTreeMap::<ForeignTransportFamilyKind, Vec<&ForeignTensor>>::new();
        let mut unclassified_tensors = BTreeSet::new();
        for tensor in container.tensors.values() {
            let kind = classify(&tensor.name);
            if let Some(kind) = kind {
                members.entry(kind).or_default().push(tensor);
            } else {
                unclassified_tensors.insert(tensor.name.clone());
            }
        }
        if let Some(first) = unclassified_tensors.first() {
            return Err(ForeignMultimodalChartError::UnknownTensor(first.clone()));
        }
        let order = [
            ForeignTransportFamilyKind::Language,
            ForeignTransportFamilyKind::Vision,
            ForeignTransportFamilyKind::Audio,
            ForeignTransportFamilyKind::VisionProjection,
            ForeignTransportFamilyKind::AudioProjection,
        ];
        let mut families = Vec::with_capacity(order.len());
        for kind in order {
            let Some(mut tensors) = members.remove(&kind) else {
                return Err(ForeignMultimodalChartError::UnknownTensor(format!(
                    "missing {kind:?} family"
                )));
            };
            tensors.sort_by(|left, right| left.name.cmp(&right.name));
            let mut rank_population = BTreeMap::new();
            for tensor in &tensors {
                if tensor.dtype != ForeignDtype::Bf16 || tensor.extent_agrees() != Some(true) {
                    return Err(ForeignMultimodalChartError::UnknownTensor(
                        tensor.name.clone(),
                    ));
                }
                *rank_population.entry(tensor.rank()).or_insert(0) += 1;
            }
            families.push(ForeignTransportFamilyChart {
                kind,
                tensor_population: tensors.len(),
                declared_octets: tensors.iter().map(|tensor| tensor.declared_octets()).sum(),
                rank_population,
                tensor_names: tensors
                    .into_iter()
                    .map(|tensor| tensor.name.clone())
                    .collect(),
            });
        }
        let tensor_population = families.iter().map(|family| family.tensor_population).sum();
        if tensor_population != container.tensors.len()
            || families
                .iter()
                .map(|family| family.declared_octets)
                .sum::<u64>()
                != container.payload_octets
        {
            return Err(malformed(configuration, "tensor population/payload"));
        }
        Ok(Self {
            configuration_address: configuration.address.clone(),
            processor_address: processor.address.clone(),
            container_address: container.address.clone(),
            architecture,
            model_type,
            input_modalities: BTreeSet::from([
                ExteriorModality::Text,
                ExteriorModality::Image,
                ExteriorModality::Video,
                ExteriorModality::Audio,
            ]),
            output_modality: ExteriorModality::Text,
            shared_carrier_extent,
            text_layer_population,
            vision_layer_population,
            audio_layer_population,
            vocabulary_extent,
            image_token_id,
            audio_token_id,
            video_token_id,
            image_soft_token_extent,
            audio_soft_token_extent,
            sampled_video_frame_extent,
            audio_sampling_rate,
            families,
            tensor_population,
            payload_octets: container.payload_octets,
            unclassified_tensors,
            source_names_are_cold: true,
        })
    }

    pub fn admit_excitation(
        &self,
        testimony: ForeignModalityExcitationTestimony,
    ) -> Result<AdmittedForeignModalityExcitation, ForeignMultimodalChartError> {
        if testimony.occurrence.is_empty()
            || testimony.activated_tensors.is_empty()
            || testimony.interventions.is_empty()
            || testimony.receiver_consequences.is_empty()
            || !self.input_modalities.contains(&testimony.modality)
        {
            return Err(ForeignMultimodalChartError::Excitation);
        }
        let admitted_kinds = match testimony.modality {
            ExteriorModality::Text => BTreeSet::from([ForeignTransportFamilyKind::Language]),
            ExteriorModality::Image | ExteriorModality::Video => BTreeSet::from([
                ForeignTransportFamilyKind::Vision,
                ForeignTransportFamilyKind::VisionProjection,
            ]),
            ExteriorModality::Audio => BTreeSet::from([
                ForeignTransportFamilyKind::Audio,
                ForeignTransportFamilyKind::AudioProjection,
            ]),
        };
        let admitted_tensors = self
            .families
            .iter()
            .filter(|family| admitted_kinds.contains(&family.kind))
            .flat_map(|family| family.tensor_names.iter())
            .collect::<BTreeSet<_>>();
        if testimony
            .activated_tensors
            .iter()
            .any(|tensor| !admitted_tensors.contains(tensor))
        {
            return Err(ForeignMultimodalChartError::Excitation);
        }
        Ok(AdmittedForeignModalityExcitation {
            occurrence: testimony.occurrence,
            modality: testimony.modality,
            activated_tensors: testimony.activated_tensors,
            interventions: testimony.interventions,
            receiver_consequences: testimony.receiver_consequences,
            source_coordinates_remain_cold: true,
        })
    }

    pub fn family(&self, kind: ForeignTransportFamilyKind) -> Option<&ForeignTransportFamilyChart> {
        self.families.iter().find(|family| family.kind == kind)
    }
}

fn classify(name: &str) -> Option<ForeignTransportFamilyKind> {
    if name.starts_with("model.embed_vision.") {
        Some(ForeignTransportFamilyKind::VisionProjection)
    } else if name.starts_with("model.embed_audio.") {
        Some(ForeignTransportFamilyKind::AudioProjection)
    } else if name.starts_with("model.language_model.") {
        Some(ForeignTransportFamilyKind::Language)
    } else if name.starts_with("model.vision_tower.") {
        Some(ForeignTransportFamilyKind::Vision)
    } else if name.starts_with("model.audio_tower.") {
        Some(ForeignTransportFamilyKind::Audio)
    } else {
        None
    }
}

fn require_projection(
    container: &ForeignContainer,
    name: &'static str,
    shape: &[usize],
) -> Result<(), ForeignMultimodalChartError> {
    let Some(tensor) = container.tensors.get(name) else {
        return Err(ForeignMultimodalChartError::Projection(name));
    };
    if tensor.dtype != ForeignDtype::Bf16
        || tensor.shape != shape
        || tensor.extent_agrees() != Some(true)
    {
        return Err(ForeignMultimodalChartError::Projection(name));
    }
    Ok(())
}

fn json_root(chart: &ForeignConfigurationChart) -> Result<Value, ForeignMultimodalChartError> {
    serde_json::from_slice::<Value>(&chart.raw)
        .ok()
        .filter(Value::is_object)
        .ok_or_else(|| malformed(chart, "root"))
}

fn object<'a>(
    value: &'a Value,
    field: &'static str,
    chart: &ForeignConfigurationChart,
) -> Result<&'a serde_json::Map<String, Value>, ForeignMultimodalChartError> {
    value
        .get(field)
        .and_then(Value::as_object)
        .ok_or_else(|| malformed(chart, field))
}

fn string_array(
    value: &Value,
    field: &'static str,
) -> Result<Vec<String>, ForeignMultimodalChartError> {
    value
        .get(field)
        .and_then(Value::as_array)
        .and_then(|values| {
            values
                .iter()
                .map(|value| value.as_str().map(str::to_owned))
                .collect::<Option<Vec<_>>>()
        })
        .ok_or_else(|| ForeignMultimodalChartError::Malformed {
            address: "config.json".to_owned(),
            field,
        })
}

fn string(value: &Value, field: &'static str) -> Result<String, ForeignMultimodalChartError> {
    value
        .get(field)
        .and_then(Value::as_str)
        .map(str::to_owned)
        .ok_or_else(|| ForeignMultimodalChartError::Malformed {
            address: "config.json".to_owned(),
            field,
        })
}

fn usize_value(
    object: &serde_json::Map<String, Value>,
    field: &'static str,
    chart: &ForeignConfigurationChart,
) -> Result<usize, ForeignMultimodalChartError> {
    object
        .get(field)
        .and_then(Value::as_u64)
        .and_then(|value| usize::try_from(value).ok())
        .ok_or_else(|| malformed(chart, field))
}

fn u64_value(
    value: &Value,
    field: &'static str,
    chart: &ForeignConfigurationChart,
) -> Result<u64, ForeignMultimodalChartError> {
    value
        .get(field)
        .and_then(Value::as_u64)
        .ok_or_else(|| malformed(chart, field))
}

fn u64_object_value(
    object: &serde_json::Map<String, Value>,
    field: &'static str,
    chart: &ForeignConfigurationChart,
) -> Result<u64, ForeignMultimodalChartError> {
    object
        .get(field)
        .and_then(Value::as_u64)
        .ok_or_else(|| malformed(chart, field))
}

fn malformed(
    chart: &ForeignConfigurationChart,
    field: &'static str,
) -> ForeignMultimodalChartError {
    ForeignMultimodalChartError::Malformed {
        address: chart.address.clone(),
        field,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foreign_map::{ContainerSpecies, ForeignTensor};

    fn tensor(name: &str, shape: Vec<usize>, start: u64) -> ForeignTensor {
        let elements = shape.iter().product::<usize>() as u64;
        ForeignTensor {
            name: name.to_owned(),
            dtype: ForeignDtype::Bf16,
            shape,
            start,
            end: start + elements * 2,
        }
    }

    fn fixture() -> (
        ForeignConfigurationChart,
        ForeignConfigurationChart,
        ForeignContainer,
    ) {
        let config = ForeignConfigurationChart::read(
            "config.json",
            br#"{
              "architectures":["Gemma4ForConditionalGeneration"],
              "model_type":"gemma4",
              "image_token_id":101,
              "audio_token_id":102,
              "video_token_id":103,
              "text_config":{"hidden_size":8,"num_hidden_layers":2,"vocab_size":16},
              "vision_config":{"hidden_size":4,"num_hidden_layers":1},
              "audio_config":{"hidden_size":6,"output_proj_dims":5,"num_hidden_layers":1}
            }"#
            .to_vec(),
        )
        .expect("configuration");
        let processor = ForeignConfigurationChart::read(
            "processor_config.json",
            br#"{
              "image_seq_length":7,
              "audio_seq_length":9,
              "feature_extractor":{"sampling_rate":16000},
              "video_processor":{"num_frames":3}
            }"#
            .to_vec(),
        )
        .expect("processor");
        let declarations = [
            tensor("model.language_model.embed_tokens.weight", vec![16, 8], 0),
            tensor("model.vision_tower.layer.weight", vec![4, 4], 256),
            tensor(
                "model.embed_vision.embedding_projection.weight",
                vec![8, 4],
                288,
            ),
            tensor("model.audio_tower.layer.weight", vec![6, 6], 352),
            tensor(
                "model.embed_audio.embedding_projection.weight",
                vec![8, 5],
                424,
            ),
        ];
        let payload_octets = declarations
            .iter()
            .map(ForeignTensor::declared_octets)
            .sum();
        let tensors = declarations
            .into_iter()
            .map(|tensor| (tensor.name.clone(), tensor))
            .collect();
        let container = ForeignContainer {
            address: "model.safetensors".to_owned(),
            species: ContainerSpecies::Safetensors {
                header_octets: 1,
                base: 9,
            },
            file_octets: payload_octets + 9,
            payload_octets,
            container_metadata: BTreeMap::new(),
            tensors,
            refused: Vec::new(),
        };
        (config, processor, container)
    }

    #[test]
    fn multimodal_manifest_keeps_source_families_cold_and_complete() {
        let (config, processor, container) = fixture();
        let chart = Gemma4ExteriorTransportChart::from_charts(&config, &processor, &container)
            .expect("multimodal chart");
        assert_eq!(chart.tensor_population, 5);
        assert_eq!(chart.output_modality, ExteriorModality::Text);
        assert!(chart.source_names_are_cold);
        assert!(chart.unclassified_tensors.is_empty());
        assert_eq!(chart.input_modalities.len(), 4);
    }

    #[test]
    fn modality_excitation_cannot_cross_a_foreign_family() {
        let (config, processor, container) = fixture();
        let chart = Gemma4ExteriorTransportChart::from_charts(&config, &processor, &container)
            .expect("multimodal chart");
        let admitted = chart
            .admit_excitation(ForeignModalityExcitationTestimony {
                occurrence: "image/0".to_owned(),
                modality: ExteriorModality::Image,
                activated_tensors: BTreeSet::from([
                    "model.vision_tower.layer.weight".to_owned(),
                    "model.embed_vision.embedding_projection.weight".to_owned(),
                ]),
                interventions: BTreeSet::from(["remove-image".to_owned()]),
                receiver_consequences: BTreeSet::from(["caption-face".to_owned()]),
            })
            .expect("image excitation");
        assert!(admitted.source_coordinates_remain_cold);
        let crossed = chart.admit_excitation(ForeignModalityExcitationTestimony {
            occurrence: "image/1".to_owned(),
            modality: ExteriorModality::Image,
            activated_tensors: BTreeSet::from(["model.audio_tower.layer.weight".to_owned()]),
            interventions: BTreeSet::from(["remove-image".to_owned()]),
            receiver_consequences: BTreeSet::from(["caption-face".to_owned()]),
        });
        assert_eq!(crossed, Err(ForeignMultimodalChartError::Excitation));
    }
}
