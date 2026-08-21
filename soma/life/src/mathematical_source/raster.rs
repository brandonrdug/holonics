use super::*;
use std::collections::VecDeque;

use holonic_engine::image::{ExactRaster, ExactRgb};

/// The exact pixel adjacency aperture. It travels with every raster return.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum PixelConnectivity {
    Four,
    Eight,
}

/// One complete alternative component population. Both four- and eight-connected populations are
/// returned; neither silently seals diagonal contact.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RasterComponentFiber {
    pub artifact: ArtifactIdentity,
    pub connectivity: PixelConnectivity,
    pub occurrences: Vec<PlacedCarrier>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RasterSourceFiber {
    pub artifact: ArtifactIdentity,
    pub background: ExactRgb,
    pub four_connected: RasterComponentFiber,
    pub eight_connected: RasterComponentFiber,
    pub work: SourceLayoutWorkDemand,
    pub omitted_background_alternatives_open: bool,
}

/// Admit a returned component population as raster testimony without expanding an authored
/// inter-component graph. The component's own four/eight pixel connectivity is already its
/// incidence; planar relations between disconnected marks remain open and cross-chart overlap is
/// asked separately. This bounded passage is linear in the returned component population.
pub fn raster_component_admission_demand(
    fiber: &RasterComponentFiber,
) -> Result<SourceLayoutWorkDemand, SourceLayoutError> {
    Ok(SourceLayoutWorkDemand {
        pair_visits: 0,
        sample_visits: 0,
        carried_octets: carried_octets(&fiber.occurrences)?,
    })
}

pub fn admit_raster_components(
    fiber: &RasterComponentFiber,
    extent: ExactExtent,
    cover: &SourceLayoutWorkCover,
) -> Result<SourceLayoutTestimony, SourceLayoutError> {
    validate_occurrences(&fiber.artifact, &extent, &fiber.occurrences)?;
    let work = raster_component_admission_demand(fiber)?;
    if !cover.admits(&work) {
        return Err(SourceLayoutError::WorkCoverInsufficient {
            demand: work,
            cover: cover.clone(),
        });
    }
    Ok(SourceLayoutTestimony {
        schema: SCHEMA.to_owned(),
        chart: TestimonyChart::Raster,
        artifact: fiber.artifact.clone(),
        extent,
        occurrences: fiber.occurrences.clone(),
        contacts: Vec::new(),
        complex: None,
        work,
        outside_declared_artifact_open: true,
    })
}

pub fn raster_demand(raster: &ExactRaster) -> Result<SourceLayoutWorkDemand, SourceLayoutError> {
    let samples =
        u128::try_from(raster.extent.sample_count()?).map_err(|_| SourceLayoutError::Extent)?;
    // Both connectivity charts: one seed visit and at most eight neighbour visits per sample.
    let sample_visits = samples.checked_mul(18).ok_or(SourceLayoutError::Extent)?;
    // Each foreground support entry carries x, y, and RGB in each of two alternative fibres.
    let carried_octets = samples.checked_mul(22).ok_or(SourceLayoutError::Extent)?;
    Ok(SourceLayoutWorkDemand {
        pair_visits: 0,
        sample_visits,
        carried_octets,
    })
}

pub fn derive_raster_fiber(
    occurrence: impl Into<String>,
    locator: impl Into<String>,
    encoded_artifact: &[u8],
    raster: &ExactRaster,
    background: ExactRgb,
    cover: &SourceLayoutWorkCover,
) -> Result<RasterSourceFiber, SourceLayoutError> {
    let artifact = ArtifactIdentity::of_bytes(occurrence, locator, encoded_artifact)?;
    let work = raster_demand(raster)?;
    if !cover.admits(&work) {
        return Err(SourceLayoutError::WorkCoverInsufficient {
            demand: work,
            cover: cover.clone(),
        });
    }
    let four_connected = raster_components(&artifact, raster, background, PixelConnectivity::Four)?;
    let eight_connected =
        raster_components(&artifact, raster, background, PixelConnectivity::Eight)?;
    Ok(RasterSourceFiber {
        artifact,
        background,
        four_connected,
        eight_connected,
        work,
        omitted_background_alternatives_open: true,
    })
}

fn raster_components(
    artifact: &ArtifactIdentity,
    raster: &ExactRaster,
    background: ExactRgb,
    connectivity: PixelConnectivity,
) -> Result<RasterComponentFiber, SourceLayoutError> {
    let derived_artifact = ArtifactIdentity {
        occurrence: format!(
            "{}:{}-connected-components",
            artifact.occurrence,
            match connectivity {
                PixelConnectivity::Four => "four",
                PixelConnectivity::Eight => "eight",
            }
        ),
        locator: artifact.locator.clone(),
        octets: artifact.octets,
        sha256: artifact.sha256.clone(),
    };
    let count = raster.extent.sample_count()?;
    let mut visited = vec![false; count];
    let mut occurrences = Vec::new();
    for row in 0..raster.extent.height {
        for column in 0..raster.extent.width {
            let ordinal = usize::try_from(
                u64::from(row) * u64::from(raster.extent.width) + u64::from(column),
            )
            .map_err(|_| SourceLayoutError::Extent)?;
            if visited[ordinal] || raster.sample(column, row) == Some(background) {
                visited[ordinal] = true;
                continue;
            }
            let mut queue = VecDeque::from([(column, row)]);
            visited[ordinal] = true;
            let mut support = Vec::new();
            let mut left = column;
            let mut right = column;
            let mut top = row;
            let mut bottom = row;
            while let Some((x, y)) = queue.pop_front() {
                let sample = raster.sample(x, y).ok_or(SourceLayoutError::Extent)?;
                support.push((y, x, sample.channels()));
                left = left.min(x);
                right = right.max(x);
                top = top.min(y);
                bottom = bottom.max(y);
                const OFFSETS: [(i32, i32); 8] = [
                    (-1, -1),
                    (0, -1),
                    (1, -1),
                    (-1, 0),
                    (1, 0),
                    (-1, 1),
                    (0, 1),
                    (1, 1),
                ];
                for (dx, dy) in OFFSETS {
                    if connectivity == PixelConnectivity::Four && dx != 0 && dy != 0 {
                        continue;
                    }
                    let candidate_x = i64::from(x) + i64::from(dx);
                    let candidate_y = i64::from(y) + i64::from(dy);
                    if candidate_x < 0
                        || candidate_y < 0
                        || candidate_x >= i64::from(raster.extent.width)
                        || candidate_y >= i64::from(raster.extent.height)
                    {
                        continue;
                    }
                    let next_x = candidate_x as u32;
                    let next_y = candidate_y as u32;
                    let next = usize::try_from(
                        u64::from(next_y) * u64::from(raster.extent.width) + u64::from(next_x),
                    )
                    .map_err(|_| SourceLayoutError::Extent)?;
                    if !visited[next] {
                        visited[next] = true;
                        if raster.sample(next_x, next_y) != Some(background) {
                            queue.push_back((next_x, next_y));
                        }
                    }
                }
            }
            support.sort_unstable();
            let support_octets = support
                .len()
                .checked_mul(11)
                .ok_or(SourceLayoutError::Extent)?;
            let mut carried_support = Vec::with_capacity(support_octets);
            for (y, x, channels) in support {
                carried_support.extend_from_slice(&x.to_le_bytes());
                carried_support.extend_from_slice(&y.to_le_bytes());
                carried_support.extend_from_slice(&channels);
            }
            let local = u64::try_from(occurrences.len()).map_err(|_| SourceLayoutError::Extent)?;
            occurrences.push(PlacedCarrier::new(
                &derived_artifact,
                local,
                carried_support,
                None,
                ExactBox::new(
                    Rat::from_integer(BigInt::from(left)),
                    Rat::from_integer(BigInt::from(top)),
                    Rat::from_integer(BigInt::from(right + 1)),
                    Rat::from_integer(BigInt::from(bottom + 1)),
                )?,
            )?);
        }
    }
    if occurrences.is_empty() {
        return Err(SourceLayoutError::NoForeground);
    }
    Ok(RasterComponentFiber {
        artifact: derived_artifact,
        connectivity,
        occurrences,
    })
}
