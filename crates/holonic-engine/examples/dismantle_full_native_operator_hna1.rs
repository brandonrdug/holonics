use std::path::Path;

use holonic_engine::native_ecology::holonic_intelligence::dismantle_full_native_operator;
use serde::Serialize;

#[derive(Serialize)]
struct Receipt {
    coefficient_population: usize,
    coefficient_octets: u64,
    operative_coefficient_population: usize,
    obstructed_coefficient_population: usize,
    carrier_chart_population: usize,
    operation_population: usize,
    layer_population: usize,
    local_layer_population: usize,
    global_layer_population: usize,
    shared_kv_layer_population: usize,
    source_names_absent_from_hot_return: bool,
    source_activation_fixtures_absent: bool,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let returned = dismantle_full_native_operator(Path::new(&root))?;
    returned.native.validate()?;
    let hot = serde_json::to_vec(&returned.native)?;
    let carries = |needle: &[u8]| hot.windows(needle.len()).any(|window| window == needle);
    let local = returned
        .native
        .layers
        .iter()
        .filter(|layer| {
            matches!(
                layer.attention,
                holonic_engine::native_ecology::holonic_intelligence::NativeAttentionTopology::Local
            )
        })
        .count();
    let global = returned.native.layers.len() - local;
    let shared = returned
        .native
        .layers
        .iter()
        .filter(|layer| {
            matches!(
                layer.kv_standing,
                holonic_engine::native_ecology::holonic_intelligence::NativeKvStanding::SharedFrom {
                    ..
                }
            )
        })
        .count();
    println!(
        "{}",
        serde_json::to_string_pretty(&Receipt {
            coefficient_population: returned.native.coefficient_populations.len(),
            coefficient_octets: returned.native.coefficient_octets()?,
            operative_coefficient_population: returned.native.operative_coefficient_population(),
            obstructed_coefficient_population: returned.native.coefficient_obstructions.len(),
            carrier_chart_population: returned.native.carriers.len(),
            operation_population: returned.native.operations.len(),
            layer_population: returned.native.layers.len(),
            local_layer_population: local,
            global_layer_population: global,
            shared_kv_layer_population: shared,
            source_names_absent_from_hot_return: ![
                b"model.".as_slice(),
                b"language".as_slice(),
                b".weight".as_slice(),
                b"gemma".as_slice(),
            ]
            .iter()
            .any(|needle| carries(needle)),
            source_activation_fixtures_absent: ![
                b"activation_fixture".as_slice(),
                b"receiver_factor".as_slice(),
                b"state_identifier".as_slice(),
            ]
            .iter()
            .any(|needle| carries(needle)),
        })?
    );
    Ok(())
}
