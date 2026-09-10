//! The observed material return is owned by the field, not by a modality adapter.
use super::*;
use crate::resident_section::SeriesAperture;

/// Declared receiver of the complete current difference. Normalization requires its own
/// group and series aperture; the complex-current receiver needs neither.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeMaterialResponseChart {
    ComplexCurrent,
    RelativeEntropy {
        group_width: usize,
        series: SeriesAperture,
    },
    SquaredProbability {
        group_width: usize,
        series: SeriesAperture,
    },
}

impl NativeMaterialResponseChart {
    pub fn from_metric(
        metric: NativeMaterialPullbackMetric,
        group_width: usize,
        series: SeriesAperture,
    ) -> Self {
        match metric {
            NativeMaterialPullbackMetric::SquaredCurrent => Self::ComplexCurrent,
            NativeMaterialPullbackMetric::RelativeEntropy => Self::RelativeEntropy {
                group_width,
                series,
            },
            NativeMaterialPullbackMetric::SquaredProbability => Self::SquaredProbability {
                group_width,
                series,
            },
        }
    }
}

impl<'c> NativeConstitutiveField<'c> {
    /// Return the latest actual observation through its producing material and contacts.
    /// An unlinked occurrence or source-qualified actuation adds no observed target and returns
    /// None. The observer sees the original field/response before the atomic contact commit.
    /// Failure keeps the field at its post-reception state; reception itself is not replayed.
    pub fn respond_to_material_observation<R>(
        &mut self,
        receiving: usize,
        chart: NativeMaterialResponseChart,
        realization: NativeContactRealization,
        observer: impl FnOnce(&Self, &NativeMaterialContactResponse<'c>) -> R,
    ) -> Result<(Option<NativeMaterialContactResponse<'c>>, Option<R>), Error> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(Error::Uncertain);
        }
        if receiving.checked_add(1) != Some(self.history.len()) {
            return Err(Error::ForeignOccurrence);
        }
        let query = match chart {
            NativeMaterialResponseChart::ComplexCurrent => {
                let Some(query) = self.pull_back_material_current(receiving)? else {
                    return Ok((None, None));
                };
                query
            }
            NativeMaterialResponseChart::RelativeEntropy {
                group_width,
                series,
            }
            | NativeMaterialResponseChart::SquaredProbability {
                group_width,
                series,
            } => {
                let Some(returned) =
                    self.normalized_material_return(receiving, group_width, series)?
                else {
                    return Ok((None, None));
                };
                let metric = if matches!(chart, NativeMaterialResponseChart::RelativeEntropy { .. })
                {
                    NativeMaterialPullbackMetric::RelativeEntropy
                } else {
                    NativeMaterialPullbackMetric::SquaredProbability
                };
                self.pull_back_material_source(&returned, metric)?
            }
        };
        let response = self.material_contact_response(query)?;
        let observed = observer(self, &response);
        self.apply_material_contact_realization(&response, realization)?;
        Ok((Some(response), Some(observed)))
    }
}
