//! The adjoint of the contraction and the deposit it leaves: SKE1's first owner.
//!
//! A returning differential `d` (`rows × out`) crosses a cross-section `W` (`out × inner`)
//! transposed, tile by tile under the single alignment pool, and the partial returns are joined by
//! re-entry: `dx = d · W`. The same differential and the carrier the cross-section was presented
//! deposit one factorized overlay atom `u · v` with `u = −η · dᵀ` and `v = x`, the factor grains
//! derived from the carrier budget of the consuming contraction. For cultivation the atom is the
//! morphology change; for dissection the support of `dx` and of the atom is the cone the receiver
//! made load-bearing at this population.

use serde::Serialize;

use crate::resident_section::{
    PassageReading, ResidentGrain, ResidentRefusal, ResidentSection, ResidentSurface,
};

use super::{
    NativeOperatorResidence, NativeOperatorResidenceError, NativeTensorOrdinal,
    operative_return::{
        DepositMaterial, NativeMorphologyDeposit, NativeReturnAperture, OverlayAtom,
        deposit_from_material,
    },
};

/// The exact return of one differential through one cross-section: `dx = d · W`.
pub struct NativeAdjointContraction<'chart> {
    pub section: ResidentSection<'chart>,
    pub bound_octaves: u32,
    pub tiles: usize,
}

#[derive(Debug, thiserror::Error)]
pub enum NativeAdjointError {
    #[error("operator residence: {0}")]
    Residence(#[from] NativeOperatorResidenceError),
    #[error("resident apparatus: {0}")]
    Resident(#[from] ResidentRefusal),
    #[error("the differential does not match the cross-section: {0}")]
    Shape(String),
    #[error("resident adjoint returned obstruction flags {flags:#x}")]
    Obstruction { flags: u32 },
}

fn bound_of(reading: &PassageReading) -> Result<u32, NativeAdjointError> {
    if !reading.obstruction.is_empty() {
        return Err(NativeAdjointError::Obstruction {
            flags: reading.obstruction.joined_flags(),
        });
    }
    Ok(reading
        .slots
        .last()
        .map(|slot| slot.max_octave.max(1))
        .unwrap_or(1))
}

/// `dx = d · W` over every aligned tile of the population.  Every tile writes wide partials into
/// one retained split-K standing (tiles padded to a power of two with exact zeros, and each tile's
/// rows divided into sub-splits to fill the card); one join folds them under the fixed tree and
/// rounds once, so the return is the serial chart's own placement.  The alignment pool is
/// exclusive per tile; every section is founded before each capture opens.
pub fn adjoint_contract<'chart>(
    residence: &mut NativeOperatorResidence<'chart>,
    population: NativeTensorOrdinal,
    differential: &ResidentSection<'chart>,
    differential_octaves: u32,
) -> Result<NativeAdjointContraction<'chart>, NativeAdjointError> {
    let descriptor = residence
        .populations()
        .get(population.0 as usize)
        .ok_or(NativeOperatorResidenceError::Population)?;
    let (total_rows, inner) = (descriptor.rows, descriptor.dim);
    let map_exponent = descriptor.frame.exponent;
    if differential.width() != total_rows || differential.rows() == 0 {
        return Err(NativeAdjointError::Shape(format!(
            "differential is {} x {} over a cross-section of {} rows",
            differential.rows(),
            differential.width(),
            total_rows
        )));
    }
    let capacity = residence.aligned_row_capacity(population)?;
    if capacity == 0 {
        return Err(NativeAdjointError::Shape("the alignment pool admits no rows".to_owned()));
    }
    let tiles = total_rows.div_ceil(capacity);
    let tile_slots = u32::try_from(tiles.next_power_of_two())
        .map_err(|_| NativeAdjointError::Shape("too many tiles".to_owned()))?;
    if tile_slots > 16 {
        return Err(NativeAdjointError::Shape(format!(
            "{tiles} tiles exceed the sixteen-slot partial standing"
        )));
    }
    let sub_splits = 16 / tile_slots;
    let splits = tile_slots * sub_splits;
    let surface = residence.surface();
    let rows = differential.rows();
    let grain = differential.grain();
    let standing = surface.retain_partials(rows, inner, splits)?;
    surface.zero_partials(&standing)?;
    let ceil_log2 = |n: usize| n.max(1).next_power_of_two().ilog2();
    let mut admitted_node_octaves = differential_octaves + ceil_log2(total_rows) + 1;
    let mut first_row = 0usize;
    let mut tile_index = 0u32;
    while first_row < total_rows {
        let tile_rows = (total_rows - first_row).min(capacity);
        let tile = residence.align_tile(population, first_row, tile_rows)?;
        let readout = &tile.mounted.readout;
        admitted_node_octaves = admitted_node_octaves.max(
            differential_octaves + readout.entry_octaves() + ceil_log2(total_rows) + 1,
        );
        let select_shape = surface.shape_select_columns(
            rows,
            differential.width(),
            first_row,
            tile_rows,
            differential_octaves,
        )?;
        let selected = surface.fresh_section(rows, tile_rows, grain)?;
        let partial_shape = surface.shape_contract_transposed_partial(
            rows,
            tile_rows,
            differential_octaves,
            readout,
            sub_splits,
            admitted_node_octaves,
        )?;
        let mut builder = surface.begin_passage(&[vec![], vec![0]])?;
        {
            let lane = builder.open(0, &[])?;
            surface.record_select_columns(&lane, differential, first_row, tile_rows, &selected)?;
        }
        builder.close(0, &selected, select_shape.needed)?;
        {
            let lane = builder.open(1, &[0])?;
            surface.record_contract_transposed_partial(
                &lane,
                &selected,
                readout,
                &standing,
                tile_index * sub_splits,
                sub_splits,
                partial_shape.needed,
            )?;
        }
        builder.close_fused(1)?;
        let reading = builder.finish()?.launch()?;
        bound_of(&reading)?;
        drop(tile);
        drop(selected);
        tile_index += 1;
        first_row += tile_rows;
    }
    let section = surface.fresh_section(rows, inner, grain)?;
    let join_needed = admitted_node_octaves;
    let mut builder = surface.begin_passage(&[vec![]])?;
    {
        let lane = builder.open(0, &[])?;
        surface.record_partial_join(&lane, &standing, map_exponent, admitted_node_octaves, &section)?;
    }
    builder.close(0, &section, join_needed)?;
    let reading = builder.finish()?.launch()?;
    let bound_octaves = bound_of(&reading)?;
    surface.release_partials(&standing)?;
    Ok(NativeAdjointContraction {
        section,
        bound_octaves,
        tiles,
    })
}

/// The support of a returned differential: how many coordinates carry a nonzero enclosure, per
/// row, read from the exact words.  Testimony for the cone; the deed stays on the card.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeDifferentialSupport {
    pub rows: usize,
    pub width: usize,
    pub nonzero_coordinates: usize,
    pub nonzero_per_row: Vec<usize>,
    pub widest_interval: u64,
}

pub fn differential_support(
    rows: usize,
    width: usize,
    intervals: &[(i64, i64)],
) -> NativeDifferentialSupport {
    let mut nonzero_per_row = vec![0usize; rows];
    let mut widest = 0u64;
    let mut nonzero = 0usize;
    for (at, (lo, hi)) in intervals.iter().enumerate() {
        if *lo != 0 || *hi != 0 {
            nonzero += 1;
            if width > 0 {
                let row = at / width;
                if row < rows {
                    nonzero_per_row[row] += 1;
                }
            }
        }
        widest = widest.max(lo.abs_diff(*hi));
    }
    NativeDifferentialSupport {
        rows,
        width,
        nonzero_coordinates: nonzero,
        nonzero_per_row,
        widest_interval: widest,
    }
}

/// Deposit one overlay atom on a cross-section from the differential that returned to its output
/// and the carrier it was presented.
pub(super) fn deposit_on_cross_section<'chart>(
    surface: &'chart ResidentSurface<'chart>,
    differential: &ResidentSection<'chart>,
    differential_octaves: u32,
    presented: &ResidentSection<'chart>,
    presented_octaves: u32,
    grain: ResidentGrain,
    aperture: NativeReturnAperture,
) -> Result<(OverlayAtom<'chart>, NativeMorphologyDeposit), ResidentRefusal> {
    deposit_from_material(
        surface,
        DepositMaterial {
            differential,
            differential_octaves,
            presented,
            presented_octaves,
            grain,
        },
        aperture,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn support_counts_nonzero_enclosures_per_row() {
        let support = differential_support(2, 3, &[(0, 0), (1, 1), (0, 0), (-2, -1), (0, 0), (0, 3)]);
        assert_eq!(support.nonzero_coordinates, 3);
        assert_eq!(support.nonzero_per_row, vec![1, 2]);
        assert_eq!(support.widest_interval, 3);
    }
}
