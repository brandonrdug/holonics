use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::causal::EventId;
use holonic_engine::embedding_fiber::{AlignedMaterial, MountedReadout, ResidentReadout};
use holonic_engine::exact_linear::ExactRatMatrix;
use holonic_engine::exact_owner_testimony::ExactOwnerOccurrence;
use holonic_engine::exact_work::{WorkBudget, WorkMetric};
use holonic_engine::front_passage::{
    AlignedMaterialPlan, ApparatusPrediction, ContractTiled, DeedAdmission, DeedReceiver, Enter,
    EnteringRows, ExactOwnerDeedReceipt, FrontPassage, MaterialAdmission, MountedPopulation,
    ResidentMaterial, ResidentRealization,
};
use holonic_engine::resident_section::{
    Dyadic, LaneTree, LaunchCandidate, ResidentGrain, ResidentSurface, TileGeometry,
};
use num_traits::ToPrimitive;
use serde::Serialize;

#[derive(Clone, Copy)]
pub struct ResidentEvents {
    pub affine_enter: EventId,
    pub affine_contract: EventId,
    pub heat_enter: EventId,
    pub heat_contract: EventId,
    pub quantity_enter: EventId,
    pub quantity_contract: EventId,
}

impl ResidentEvents {
    fn all(self) -> [EventId; 6] {
        [
            self.affine_enter,
            self.affine_contract,
            self.heat_enter,
            self.heat_contract,
            self.quantity_enter,
            self.quantity_contract,
        ]
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct CandidateReceipt {
    pub shape: [usize; 3],
    pub tile: [u32; 5],
    pub symbol: String,
    pub block: u32,
    pub shared_octets: u32,
    pub registers: u32,
    pub resident_blocks: u32,
    pub occupancy: [u32; 2],
    pub blocks: u64,
    pub serial_k_per_lane: u64,
    pub dependency_span: u64,
    pub accepted: bool,
    pub refusal_reasons: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct ResidentReturn {
    pub schema: String,
    pub device: String,
    pub ptx_sha256: String,
    pub grain: u32,
    pub tile_receiver: Vec<String>,
    pub candidate_fibre: Vec<CandidateReceipt>,
    pub selected_tiles: BTreeMap<String, [u32; 5]>,
    pub material_reconciliation: Vec<(String, u64, u64)>,
    pub material_admission: MaterialAdmission,
    pub deed_prediction: holonic_engine::exact_work::ExactWork,
    pub apparatus_prediction: ApparatusPrediction,
    pub deed_admission: DeedAdmission,
    pub semantic_price: u64,
    pub starved_control_refused: bool,
    pub graph: [usize; 8],
    pub front_cover: Vec<(usize, usize, usize, String, String)>,
    pub traffic_fronts: Vec<(usize, u64, u64, u64)>,
    pub readbacks: BTreeMap<u64, Vec<(i64, i64)>>,
    pub obstruction_population: usize,
    pub deed_launches: u64,
    pub synchronizations: u64,
    pub cpu_cells: usize,
    pub exact_owner_receipt: String,
}

pub struct ResidentDeed {
    pub returned: ResidentReturn,
    pub receipt: ExactOwnerDeedReceipt,
}

#[allow(clippy::too_many_arguments)]
pub fn conduct(
    operation: &holonic_engine::ported_operation::PortedOperationComplex,
    exact_owner: &ExactOwnerOccurrence,
    events: ResidentEvents,
    affine_matrix: &ExactRatMatrix,
    heat_matrix: &ExactRatMatrix,
    quantity_matrix: &ExactRatMatrix,
) -> Result<ResidentDeed, String> {
    let readout = ResidentReadout::new().map_err(debug)?;
    let surface = ResidentSurface::on(&readout).map_err(display)?;
    let grain = admitted_integer_grain(&[affine_matrix, heat_matrix, quantity_matrix])?;
    let passage = FrontPassage::new(&surface, grain).reading(events.all());

    let (affine_tile, mut candidate_fibre) = select_tile(&surface, 4, 3, 1)?;
    let (heat_tile, heat_fibre) = select_tile(&surface, 1, 2, 1)?;
    let (quantity_tile, quantity_fibre) = select_tile(&surface, 1, 3, 1)?;
    candidate_fibre.extend(heat_fibre);
    candidate_fibre.extend(quantity_fibre);
    let plan = AlignedMaterialPlan::maps(vec![
        (
            "affine-map".to_owned(),
            affine_matrix.rows(),
            affine_matrix.columns(),
        ),
        (
            "heat-map".to_owned(),
            heat_matrix.rows(),
            heat_matrix.columns(),
        ),
        (
            "quantity-map".to_owned(),
            quantity_matrix.rows(),
            quantity_matrix.columns(),
        ),
    ]);
    let material_prediction = passage.predict_aligned_material(&plan);
    let material_admission = passage
        .admit_material(&material_prediction)
        .map_err(debug)?;

    let (affine_mounted, affine_mass_octaves) = mount_matrix(&readout, affine_matrix)?;
    let (heat_mounted, heat_mass_octaves) = mount_matrix(&readout, heat_matrix)?;
    let (quantity_mounted, quantity_mass_octaves) = mount_matrix(&readout, quantity_matrix)?;
    let mut material = ResidentMaterial::empty();
    material.entering.insert(
        "affine-x".to_owned(),
        entering(&[3, -1, 1, 3, -1, 1, -1, 3, 1, -1, 3, 1], 4, 3)?,
    );
    material
        .entering
        .insert("heat-x".to_owned(), entering(&[2, 2], 1, 2)?);
    material
        .entering
        .insert("quantity-x".to_owned(), entering(&[1, 1, -2], 1, 3)?);
    material.populations.insert(
        "affine-map".to_owned(),
        MountedPopulation {
            readout: affine_mounted,
            mass_value_octaves: affine_mass_octaves,
        },
    );
    material.populations.insert(
        "heat-map".to_owned(),
        MountedPopulation {
            readout: heat_mounted,
            mass_value_octaves: heat_mass_octaves,
        },
    );
    material.populations.insert(
        "quantity-map".to_owned(),
        MountedPopulation {
            readout: quantity_mounted,
            mass_value_octaves: quantity_mass_octaves,
        },
    );
    let reconciliation = material_admission.reconcile(&material);
    if reconciliation
        .iter()
        .any(|(_, predicted, actual)| predicted != actual)
    {
        return Err("the admitted and mounted M1 material disagree".to_owned());
    }

    let mut realization = ResidentRealization::default();
    bind_enter(&mut realization, events.affine_enter, "affine-x");
    bind_enter(&mut realization, events.heat_enter, "heat-x");
    bind_enter(&mut realization, events.quantity_enter, "quantity-x");
    bind_contract(
        &mut realization,
        events.affine_contract,
        "affine-map",
        affine_tile,
    );
    bind_contract(
        &mut realization,
        events.heat_contract,
        "heat-map",
        heat_tile,
    );
    bind_contract(
        &mut realization,
        events.quantity_contract,
        "quantity-map",
        quantity_tile,
    );

    let compiled = passage
        .compile(
            operation,
            &realization,
            &material,
            exact_owner,
            events.affine_contract,
        )
        .map_err(debug)?;
    let deed_prediction = compiled.deed_prediction.clone();
    let apparatus_prediction = compiled.apparatus_prediction.clone();
    let metric = WorkMetric::width_weighted();
    let price = metric
        .price(&deed_prediction)
        .to_u64()
        .ok_or_else(|| "the exact M1 work price exceeds u64".to_owned())?;
    let starved_price = price
        .checked_sub(1)
        .ok_or_else(|| "the M1 work price is zero".to_owned())?;
    let receiver =
        DeedReceiver::unbounded().with_scalar(WorkBudget::declared(metric.clone(), price));
    let starved =
        DeedReceiver::unbounded().with_scalar(WorkBudget::declared(metric, starved_price));
    let starved_control_refused = passage
        .admit(&compiled, &starved, Some(&material_admission))
        .is_err();
    if !starved_control_refused {
        return Err("the one-less exact-work receiver admitted the M1 deed".to_owned());
    }
    let admission = passage
        .admit(&compiled, &receiver, Some(&material_admission))
        .map_err(debug)?;
    let deed_admission = admission.clone();
    let bound = passage
        .realize(compiled, &material, admission)
        .map_err(debug)?;
    let graph = bound.graph();
    let graph_receipt = [
        graph.0.nodes,
        graph.0.edges,
        graph.0.kernel_nodes,
        graph.0.memset_nodes,
        graph.0.memcpy_nodes,
        graph.0.other_nodes,
        graph.1 .0,
        graph.1 .1,
    ];
    let front_cover = bound
        .fronts()
        .iter()
        .map(|front| {
            (
                front.depth,
                front.cover.device_cells,
                front.cover.cpu_cells,
                front.cover.occupied_lanes.to_string(),
                front.cover.idle_lanes.to_string(),
            )
        })
        .collect::<Vec<_>>();
    let cpu_cells = front_cover.iter().map(|front| front.2).sum();
    if cpu_cells != 0 {
        return Err("the M1 hot deed placed a semantic cell on the CPU".to_owned());
    }
    let traffic_fronts = bound.traffic.fronts.clone();
    let (returned, receipt) = bound
        .launch_with_exact_owner_receipt(&bound.mode)
        .map_err(debug)?;
    bound.standing(&returned).map_err(debug)?;
    if !returned.obstruction.refusals.is_empty() {
        return Err("the M1 resident deed returned an obstruction".to_owned());
    }
    let expected_zero = [
        (events.affine_contract, vec![(0, 0), (0, 0), (0, 0), (0, 0)]),
        (events.heat_contract, vec![(0, 0)]),
        (events.quantity_contract, vec![(0, 0)]),
    ];
    for (event, expected) in expected_zero {
        let words = bound.read_section(&returned, event).map_err(debug)?;
        if words != expected {
            return Err(format!(
                "M1 terminal event {} did not return exact zero",
                event.0
            ));
        }
    }
    let selected = events.all().into_iter().collect::<BTreeSet<_>>();
    if !receipt.matches_complex_and_selection(operation, &selected)
        || receipt.readbacks().len() != selected.len()
    {
        return Err(
            "the post-card receipt does not bind the complete six-event complex".to_owned(),
        );
    }
    let readbacks = receipt
        .readbacks()
        .iter()
        .map(|(event, words)| (event.0, words.clone()))
        .collect::<BTreeMap<_, _>>();
    let after = &returned.census_after;
    if after.deed_launches != 1 || after.synchronizations != 1 {
        return Err("M1 was not returned by one graph launch and one synchronization".to_owned());
    }
    let summary = ResidentReturn {
        schema: "eros.m1-three-branch-front-passage.v1".to_owned(),
        device: surface.device_name().to_owned(),
        ptx_sha256: surface.ptx_sha256().to_owned(),
        grain: grain.0,
        tile_receiver: vec![
            "emitted for the exact branch shape".to_owned(),
            "exact row cover".to_owned(),
            "exact output cover".to_owned(),
            "no K partition".to_owned(),
            "no shared K stage below first positive staged aperture".to_owned(),
            "one complete device warp".to_owned(),
        ],
        candidate_fibre,
        selected_tiles: BTreeMap::from([
            ("affine".to_owned(), tile_words(affine_tile)),
            ("heat".to_owned(), tile_words(heat_tile)),
            ("quantity".to_owned(), tile_words(quantity_tile)),
        ]),
        material_reconciliation: reconciliation,
        material_admission,
        deed_prediction,
        apparatus_prediction,
        deed_admission,
        semantic_price: price,
        starved_control_refused,
        graph: graph_receipt,
        front_cover,
        traffic_fronts,
        readbacks,
        obstruction_population: returned.obstruction.refusals.len(),
        deed_launches: after.deed_launches,
        synchronizations: after.synchronizations,
        cpu_cells,
        exact_owner_receipt: receipt.address().to_owned(),
    };
    Ok(ResidentDeed {
        returned: summary,
        receipt,
    })
}

fn select_tile(
    surface: &ResidentSurface<'_>,
    rows: usize,
    inner: usize,
    out_width: usize,
) -> Result<(TileGeometry, Vec<CandidateReceipt>), String> {
    let candidates = surface
        .contract_candidates(rows, inner, out_width)
        .map_err(display)?;
    let first_positive_stage = candidates
        .iter()
        .filter_map(|candidate| (candidate.tile.k_tile > 0).then_some(candidate.tile.k_tile))
        .min()
        .ok_or_else(|| {
            "the emitted candidate family has no positive staging aperture".to_owned()
        })?;
    if inner >= first_positive_stage as usize {
        return Err("the M1 inner extent reaches the first staged-K aperture".to_owned());
    }
    let warp = surface.declaration().warp_size.max(1);
    let mut receipts = Vec::with_capacity(candidates.len());
    let mut admitted = Vec::new();
    for candidate in candidates {
        let tile = candidate.tile;
        let mut reasons = Vec::new();
        if tile.tile_rows as usize != rows {
            reasons.push("row tile does not exactly cover the admitted rows".to_owned());
        }
        if tile.outs_per_block as usize != out_width {
            reasons.push("output tile does not exactly cover the admitted outputs".to_owned());
        }
        if tile.splits != 1 {
            reasons.push("split-K partitions the complete inner extent".to_owned());
        }
        if tile.k_tile != 0 {
            reasons.push(format!(
                "shared K staging begins at {first_positive_stage}, above both material extents"
            ));
        }
        if candidate.block != warp {
            reasons.push(format!(
                "block {} is not exactly one mounted warp of {warp}",
                candidate.block
            ));
        }
        let accepted = reasons.is_empty();
        if accepted {
            admitted.push(tile);
        }
        receipts.push(candidate_receipt(
            &candidate,
            [rows, inner, out_width],
            accepted,
            reasons,
        ));
    }
    if admitted.len() != 1 {
        return Err(format!(
            "the exact-cover/no-partial/no-staging receiver retained {} candidates",
            admitted.len()
        ));
    }
    Ok((admitted[0], receipts))
}

fn candidate_receipt(
    candidate: &LaunchCandidate,
    shape: [usize; 3],
    accepted: bool,
    refusal_reasons: Vec<String>,
) -> CandidateReceipt {
    CandidateReceipt {
        shape,
        tile: tile_words(candidate.tile),
        symbol: candidate.symbol.to_owned(),
        block: candidate.block,
        shared_octets: candidate.shared_octets,
        registers: candidate.registers,
        resident_blocks: candidate.resident_blocks,
        occupancy: [candidate.occupancy.0, candidate.occupancy.1],
        blocks: candidate.blocks,
        serial_k_per_lane: candidate.serial_k_per_lane,
        dependency_span: candidate.dependency_span,
        accepted,
        refusal_reasons,
    }
}

fn tile_words(tile: TileGeometry) -> [u32; 5] {
    [
        tile.tile_rows,
        tile.lanes,
        tile.outs_per_block,
        tile.k_tile,
        tile.splits,
    ]
}

fn mount_matrix<'chart>(
    readout: &'chart ResidentReadout,
    matrix: &ExactRatMatrix,
) -> Result<(MountedReadout<'chart>, u32), String> {
    let entries = matrix
        .entries()
        .iter()
        .map(|value| {
            value
                .to_integer()
                .to_i64()
                .ok_or_else(|| "resident exact matrix entry exceeds i64".to_owned())
        })
        .collect::<Result<Vec<_>, _>>()?;
    let aligned = AlignedMaterial {
        entry_octaves: entries
            .iter()
            .map(|value| 64 - value.unsigned_abs().leading_zeros())
            .max()
            .unwrap_or(0),
        negatives: entries.iter().filter(|value| **value < 0).count() as u64,
        entries,
        exponent: 0,
    };
    let mass = aligned
        .entries
        .chunks(matrix.columns())
        .map(|row| {
            row.iter()
                .try_fold(0u64, |sum, value| sum.checked_add(value.unsigned_abs()))
                .ok_or_else(|| "resident row mass overflows u64".to_owned())
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .max()
        .unwrap_or(0);
    let mass_value_octaves = if mass == 0 {
        0
    } else {
        u64::BITS - mass.leading_zeros()
    };
    let mounted = readout.mount(&aligned, matrix.columns()).map_err(debug)?;
    Ok((mounted, mass_value_octaves))
}

fn admitted_integer_grain(matrices: &[&ExactRatMatrix]) -> Result<ResidentGrain, String> {
    matrices
        .iter()
        .flat_map(|matrix| matrix.entries())
        .all(num_rational::Ratio::is_integer)
        .then_some(ResidentGrain(0))
        .ok_or_else(|| {
            "M1's resident integer-grain receiver refused a non-integer matrix".to_owned()
        })
}

fn entering(values: &[i32], rows: usize, width: usize) -> Result<EnteringRows, String> {
    if rows == 0 || width == 0 || rows.checked_mul(width) != Some(values.len()) {
        return Err("resident entering population is ragged".to_owned());
    }
    Ok(EnteringRows {
        words: values
            .iter()
            .copied()
            .map(bfloat16_integer)
            .collect::<Result<Vec<_>, _>>()?,
        rows,
        width,
    })
}

fn bind_enter(realization: &mut ResidentRealization, event: EventId, population: &str) {
    realization.bind(
        event,
        Enter {
            population: population.to_owned(),
            scale: Dyadic::ONE,
        },
    );
}

fn bind_contract(
    realization: &mut ResidentRealization,
    event: EventId,
    population: &str,
    tile: TileGeometry,
) {
    realization.bind(
        event,
        ContractTiled {
            population: population.to_owned(),
            tile,
            admitted_node_octaves: ResidentSurface::carrier_octaves(),
            tree: LaneTree::Descending,
        },
    );
}

fn bfloat16_integer(value: i32) -> Result<u16, String> {
    if value == 0 {
        return Ok(0);
    }
    let negative = value < 0;
    let magnitude = value.unsigned_abs();
    let exponent = 31 - magnitude.leading_zeros();
    let significand = if exponent <= 7 {
        magnitude << (7 - exponent)
    } else {
        let shift = exponent - 7;
        if magnitude & ((1u32 << shift) - 1) != 0 {
            return Err(format!("{value} is not exactly representable as bfloat16"));
        }
        magnitude >> shift
    };
    let field = exponent + 127;
    Ok(((negative as u16) << 15) | ((field as u16) << 7) | (significand as u16 - 128))
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}

fn debug(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}
