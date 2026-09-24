//! Placement evidence for the geometric field's actual row operators.
//!
//! This adapter certifies the logical staged rows and their read footprints. It does not claim
//! that a row is a physical lane or that a normal-material fit is independent: the latter remains
//! one joined reduction over the complete staged section.

use super::super::NativeSessionError;
use super::{CompiledFieldGeometry, GeometricRowGroup};
use holonics::hardware_cover::{Chart, CoverDecomposition, FrontCell, HardwareCover};
use holonic_engine::resident_section::{ResidentSurface, SLOT_WORDS};
use holonic_engine::section_partition::{
    DeclaredSpecies, JunctionOutput, ReadRegion, ResourceDeclaration, SectionCell, SectionLineage,
    SectionPartition, SectionRegion, SectionShape,
};
use serde_json::{Value, json};
use std::collections::BTreeMap;

const KERNELS: &[&str] = &[
    "section_enclosure_gather_phase",
    "section_enclosure_scatter_phase_adjoint",
    "section_phase_participation",
    "section_phase_participation_adjoint",
    "section_enclosure_bilinear_features",
    "section_enclosure_bilinear_adjoint",
    "section_enclosure_refine_rows",
];

fn region(row: usize, width: usize) -> Result<SectionRegion, NativeSessionError> {
    SectionRegion::new(row, row + 1, 0, width)
        .map_err(|defect| NativeSessionError::Application(defect.to_string()))
}

fn partition_for(
    layout: &CompiledFieldGeometry,
    components: usize,
    condition_components: usize,
    reverse: bool,
) -> Result<(SectionPartition, Vec<String>), NativeSessionError> {
    let packet_width = components
        .checked_add(1)
        .and_then(|width| width.checked_mul(4))
        .ok_or_else(|| NativeSessionError::Application("geometric row packet extent".into()))?;
    let condition_packet_width = condition_components
        .checked_add(1)
        .and_then(|width| width.checked_mul(4))
        .ok_or_else(|| {
            NativeSessionError::Application("geometric condition packet extent".into())
        })?;
    let output_width = packet_width
        .checked_add(SLOT_WORDS.div_ceil(2))
        .ok_or_else(|| NativeSessionError::Application("geometric row status extent".into()))?;
    let shape = SectionShape::of(layout.rows, output_width, 0);
    let packet_shape = SectionShape::of(layout.rows, packet_width, 0);
    let mut populations = BTreeMap::new();
    populations.insert("query-current".to_owned(), packet_shape);
    populations.insert("neighbor-current".to_owned(), packet_shape);
    populations.insert("seed-current".to_owned(), packet_shape);
    populations.insert(
        "condition-chart".to_owned(),
        SectionShape::of(layout.rows, condition_packet_width, 0),
    );
    if reverse {
        populations.insert("reverse-current".to_owned(), packet_shape);
        populations.insert("reverse-covector".to_owned(), shape);
    }

    let mut cells = Vec::new();
    let mut refusal_words = Vec::new();
    let mut index = 0usize;
    for (group_index, group) in layout.groups.iter().enumerate() {
        for (local, &receiver) in group.receivers.iter().enumerate() {
            let write = region(receiver, output_width)?;
            let reads = if reverse {
                vec![
                    ReadRegion {
                        population: "reverse-current".to_owned(),
                        region: packet_shape.whole(),
                    },
                    ReadRegion {
                        population: "reverse-covector".to_owned(),
                        region: shape.whole(),
                    },
                    ReadRegion {
                        population: "seed-current".to_owned(),
                        region: packet_shape.whole(),
                    },
                ]
            } else {
                let mut reads = vec![ReadRegion {
                    population: "query-current".to_owned(),
                    region: region(receiver, packet_width)?,
                }];
                let start = local.checked_mul(group.neighbors).ok_or_else(|| {
                    NativeSessionError::Application("geometric source footprint".into())
                })?;
                let end = start.checked_add(group.neighbors).ok_or_else(|| {
                    NativeSessionError::Application("geometric source footprint".into())
                })?;
                let sources = group.sources.get(start..end).ok_or_else(|| {
                    NativeSessionError::Application("geometric source footprint".into())
                })?;
                for &source in sources {
                    reads.push(ReadRegion {
                        population: "neighbor-current".to_owned(),
                        region: region(source, packet_width)?,
                    });
                }
                reads.push(ReadRegion {
                    population: "seed-current".to_owned(),
                    region: packet_shape.whole(),
                });
                reads
            };
            cells.push(SectionCell {
                index,
                write,
                reads,
                partial_of: None,
            });
            refusal_words.push(format!(
                "{}-group-{group_index}-row-{receiver}-refusal",
                if reverse { "reverse" } else { "forward" }
            ));
            index += 1;
        }
    }
    Ok((
        SectionPartition {
            lineage: SectionLineage {
                source: "analytic-geometric-field".to_owned(),
                population: if reverse {
                    "geometric-reverse-staged-rows".to_owned()
                } else {
                    "geometric-forward-staged-rows".to_owned()
                },
                body: "native-field-geometric-word".to_owned(),
            },
            shape,
            populations,
            cells,
        },
        refusal_words,
    ))
}

fn certify_direction(
    surface: &ResidentSurface<'_>,
    layout: &CompiledFieldGeometry,
    components: usize,
    condition_components: usize,
    reverse: bool,
) -> Result<Value, NativeSessionError> {
    let (partition, refusal_words) =
        partition_for(layout, components, condition_components, reverse)?;
    let front: Vec<_> = partition
        .cells
        .iter()
        .map(|cell| FrontCell {
            index: cell.index,
            extent: cell.write.extent(),
        })
        .collect();
    let kernel = if reverse {
        "native-geometric-reverse-row"
    } else {
        "native-geometric-forward-row"
    };
    let device_cover = HardwareCover::of_charts(vec![Chart::Device(surface.declaration().clone())]);
    let cover = &device_cover;
    let placement = CoverDecomposition::of(cover, &front, kernel);
    placement.independence(&front).map_err(|barriers| {
        NativeSessionError::Application(format!("geometric placement: {barriers:?}"))
    })?;
    let resources = ResourceDeclaration {
        species: Vec::<DeclaredSpecies>::new(),
        enactment_aperture: u64::MAX,
    };
    let receipt = partition
        .certify(cover, &[] as &[JunctionOutput], &resources, kernel)
        .map_err(|defects| {
            NativeSessionError::Application(format!("geometric section partition: {defects:?}"))
        })?;
    let work = placement
        .work(cover)
        .into_iter()
        .map(|work| {
            json!({
                "chart": work.chart.to_string(),
                "cells": work.cells.to_string(),
                "members": work.members.to_string(),
                "occupied_lanes": work.occupied_lanes.to_string(),
                "idle_lanes": work.idle_lanes.to_string(),
            })
        })
        .collect::<Vec<_>>();
    let read_footprints = receipt
        .cells
        .iter()
        .map(|cell| {
            json!({
                "cell": cell.index,
                "write": {
                    "row_from": cell.write.row_from,
                    "row_to": cell.write.row_to,
                    "column_from": cell.write.column_from,
                    "column_to": cell.write.column_to,
                },
                "reads": cell.reads.iter().map(|read| json!({
                    "population": read.population,
                    "row_from": read.region.row_from,
                    "row_to": read.region.row_to,
                    "column_from": read.region.column_from,
                    "column_to": read.region.column_to,
                })).collect::<Vec<_>>(),
            })
        })
        .collect::<Vec<_>>();
    Ok(json!({
        "direction": if reverse { "reverse" } else { "forward" },
        "cells": receipt.cells.len(),
        "row_packet_width": receipt.shape.width - SLOT_WORDS.div_ceil(2),
        "row_receipt_i64_words": SLOT_WORDS.div_ceil(2),
        "row_output_width_with_status": receipt.shape.width,
        "read_footprints": read_footprints,
        "rows": layout.rows,
        "groups": layout.groups.len(),
        "shared_immutable_reads": receipt.shared_reads.iter().map(|read| read.population.clone()).collect::<Vec<_>>(),
        "disjointness": receipt.disjointness.disjoint,
        "partition_complete": receipt.completeness.complete,
        "interchangeable": receipt.certificate.is_interchangeable(),
        "kernel": kernel,
        "row_block_realization": {
            "logical_rows": layout.rows,
            "staged_output_rows": receipt.cells.len(),
            "one_logical_cell_per_row": true,
            "physical_lane_schedule": "device-only row blocks; counts below are cover-derived, not profiler observations",
        },
        "row_status_words": refusal_words,
        "final_status_union": format!("deterministic OR/union of {} row status words", receipt.cells.len()),
        "shared_opaque_reads": ["D", "M"],
        "cover": {
            "charts": cover.charts().iter().map(|chart| chart.id().to_string()).collect::<Vec<_>>(),
            "cover_capacity": cover.charts().iter().map(|chart| json!({
                "chart": chart.id().to_string(),
                "grain": chart.grain(),
                "resident_lanes": chart.resident_lanes(),
            })).collect::<Vec<_>>(),
            "derived_work": work,
            "execution_observed": false,
        },
    }))
}

impl CompiledFieldGeometry {
    /// Certify the complete logical row placement used by geometric forward and reverse words.
    /// Shared source, seed, material and covector populations are immutable reads; staged rows
    /// own one refusal word each, and their final obstruction is a separate deterministic union.
    pub(crate) fn certify_placement(
        &self,
        surface: &ResidentSurface<'_>,
        components: usize,
        condition_components: usize,
    ) -> Result<&Value, NativeSessionError> {
        if components == 0 || condition_components == 0 || self.rows == 0 {
            return Err(NativeSessionError::Application(
                "geometric placement shape".into(),
            ));
        }
        let mode = surface.mode();
        if let Some((d, k, owner, value)) = self.placement.get() {
            if *d != components || *k != condition_components || *owner != mode {
                return Err(NativeSessionError::Application(
                    "geometric placement belongs to another source/device chart".into(),
                ));
            }
            return Ok(value);
        }
        let forward = certify_direction(surface, self, components, condition_components, false)?;
        let reverse = certify_direction(surface, self, components, condition_components, true)?;
        let value = json!({
            "schema": "holonics-hna.geometric-placement.v1",
            "rows": self.rows,
            "components": components,
            "condition_components": condition_components,
            "phase_groups": self.groups.iter().map(|group: &GeometricRowGroup| json!({
                "receivers": group.receivers,
                "sources": group.sources,
                "phase_count": group.phases.len(),
                "neighbors": group.neighbors,
            })).collect::<Vec<_>>(),
            "kernel_content": KERNELS,
            "forward": forward,
            "reverse": reverse,
            "normal_material": "one joined shared reduction; not certified as independent row writes",
            "physical_lanes": "reported only through the mounted surface cover",
        });
        self.placement
            .set((components, condition_components, mode, value))
            .map_err(|_| {
                NativeSessionError::Application("geometric placement already founded".into())
            })?;
        Ok(&self.placement.get().unwrap().3)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonics::hardware_cover::HardwareCover;
    use std::collections::BTreeMap;

    fn partition(cells: Vec<SectionCell>) -> SectionPartition {
        SectionPartition {
            lineage: SectionLineage {
                source: "test".into(),
                population: "rows".into(),
                body: "placement".into(),
            },
            shape: SectionShape::of(2, 3, 0),
            populations: BTreeMap::new(),
            cells,
        }
    }

    #[test]
    fn placement_falsifiers_refuse_duplicate_and_omitted_rows() {
        let row = |index| SectionCell {
            index,
            write: SectionRegion::new(index, index + 1, 0, 3).unwrap(),
            reads: Vec::new(),
            partial_of: None,
        };
        let resources = ResourceDeclaration {
            species: Vec::new(),
            enactment_aperture: u64::MAX,
        };
        let cover = HardwareCover::cpu_only();
        let duplicate = partition(vec![row(0), row(0)])
            .certify(&cover, &[], &resources, "placement-test")
            .unwrap_err();
        assert!(!duplicate.is_empty());
        let omitted = partition(vec![row(0)])
            .certify(&cover, &[], &resources, "placement-test")
            .unwrap_err();
        assert!(!omitted.is_empty());
    }
}
