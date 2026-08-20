//! Exact Station-B modality projection deed constructors.
//!
//! The source-admission site and W1 share this owner.  Neither caller re-authors the operation
//! laws: this file is the one place where the three-operation modality complex and its resident
//! realization are founded.

use holonic_engine::front_passage::{Contract, ResidentRealization, RmsRebase, Standing};
use holonic_engine::ported_operation::{OperationSpecies, PortedOperationComplex};
use holonic_engine::resident_section::Dyadic;

use super::resident_layer;

/// Found one modality projection with the exact Station-B testimony.
///
/// `width_field` and `eps_text` are configuration readings supplied by the caller.  The width,
/// epsilon dyadic, and source carrier remain explicit inputs so this constructor does not read a
/// source path or invent a configuration scope.
pub fn found(
    modality: &str,
    width: usize,
    width_field: &str,
    population: &str,
    eps_text: &str,
    eps: Dyadic,
) -> Result<(PortedOperationComplex, ResidentRealization), String> {
    let mut complex =
        PortedOperationComplex::new(format!("{modality} projection into the shared stream"));
    let modality_port = complex.port(format!("{modality} tower output, {width}"));
    let standing = complex.port("continuing standing, 2560");
    let mut realization = ResidentRealization::default();

    let tower_output = resident_layer::law(
        &mut complex,
        &format!("{modality} tower output"),
        OperationSpecies::Construction,
        vec![],
        vec![modality_port],
        None,
        vec![
            resident_layer::implementation(if modality == "vision" {
                "Gemma4Model.get_image_features (vision_outputs.pooler_output = self.embed_vision(inputs_embeds=last_hidden_state))"
            } else {
                "Gemma4Model.get_audio_features (audio_outputs.pooler_output = self.embed_audio(inputs_embeds=audio_outputs.last_hidden_state))"
            }),
            resident_layer::implementation(
                "Gemma4MultimodalEmbedder.forward (embs_normed = self.embedding_pre_projection_norm(inputs_embeds))",
            ),
        ],
    )?;
    realization.bind(
        tower_output,
        Standing {
            name: format!("{modality} tower output"),
        },
    );

    let rebase = resident_layer::law(
        &mut complex,
        &format!("{modality} pre-projection rebase, no gain"),
        OperationSpecies::Transport,
        vec![modality_port],
        vec![modality_port],
        None,
        vec![
            resident_layer::implementation(
                "Gemma4MultimodalEmbedder.forward (embs_normed = self.embedding_pre_projection_norm(inputs_embeds))",
            ),
            resident_layer::implementation(
                "Gemma4MultimodalEmbedder.__init__ (self.embedding_pre_projection_norm = Gemma4RMSNorm(self.multimodal_hidden_size, eps=self.eps, with_scale=False))",
            ),
            resident_layer::implementation(
                "Gemma4RMSNorm._norm (return hidden_states * torch.pow(mean_squared, -0.5))",
            ),
            resident_layer::implementation(
                "Gemma4MultimodalEmbedder.__init__ (self.multimodal_hidden_size = getattr(multimodal_config, \"output_proj_dims\", multimodal_config.hidden_size))",
            ),
            resident_layer::configuration("rms_norm_eps", eps_text),
            resident_layer::configuration(width_field, &width.to_string()),
        ],
    )?;
    realization.bind(
        rebase,
        RmsRebase {
            group: width,
            gain: None,
            eps,
        },
    );
    resident_layer::bond(
        &mut complex,
        "tower output rebases",
        modality_port,
        tower_output,
        rebase,
        0,
    )?;

    let projection = resident_layer::law(
        &mut complex,
        &format!("{modality} projection"),
        OperationSpecies::Transport,
        vec![modality_port],
        vec![standing],
        Some(population.to_owned()),
        vec![
            resident_layer::implementation(
                "Gemma4MultimodalEmbedder.forward (return self.embedding_projection(embs_normed))",
            ),
            resident_layer::implementation(
                "Gemma4MultimodalEmbedder.__init__ (self.embedding_projection = nn.Linear(self.multimodal_hidden_size, self.text_hidden_size, bias=False))",
            ),
            resident_layer::shape(population, &[super::tower::HIDDEN, width]),
        ],
    )?;
    realization.bind(
        projection,
        Contract {
            population: population.to_owned(),
        },
    );
    resident_layer::bond(
        &mut complex,
        "projects into the stream",
        modality_port,
        rebase,
        projection,
        0,
    )?;
    Ok((complex, realization))
}
