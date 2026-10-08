//! The actual observed receiving face returns through its producing controlled Word.
//!
//! This is an affine receiving-map update.  At fixed producing anchors, R enters linearly;
//! it does not claim a simultaneous receiving-map/contact ray or a world-policy derivative.
//! Source preparation, source moment, current, clocks and the native propagation operands
//! remain bound to the Word.  No requested consequence is used as an observed target.

use super::*;
use crate::hnn::constitution::{LinearLocus, Locus, Reach};
use crate::hnn::port::{ChangeCovector, Deposit, WordReturn};
use crate::hnn::ratio::{Face, ReceivingFaceRatio};
use crate::hnn::retention::Diamond;
use num_bigint::BigInt;

#[derive(Debug)]
pub struct NativeReceivingReturn {
    pub ratio: ReceivingFaceRatio,
    pub pullback: WordReturn,
    /// Conditional current-opening covector with the actual exterior returned waves held.
    /// It is not a derivative through World state, Robin solve or a material action policy.
    pub opening: ChangeCovector,
    /// A zero/absent actual comparison changes no normal statistic, remainder or commit.
    pub deposit: Option<Deposit>,
}

impl Word<'_> {
    pub(crate) fn return_observed_receiving(
        self,
        receiver: usize,
        applied: &action::AppliedPortPreparation,
        observed: Vec<Option<Face>>,
    ) -> Result<NativeReceivingReturn, HnnError> {
        applied.verify_producer(&self)?;
        let (theta, current, source, support) = self
            .native_source
            .as_ref()
            .ok_or(HnnError::Unadmitted {
                reason: "the observed receiving return consumes its actual source-bound Word",
            })?
            .clone();
        let field = self.field;
        let (phases, faces) = self.contact_receiving(receiver)?;
        if &phases != applied.phases()
            || observed.len() != applied.compared().len()
            || observed
                .iter()
                .zip(applied.compared())
                .any(|(q, &compared)| q.is_some() != compared)
        {
            return Err(HnnError::Unadmitted {
                reason: "the actual encounter comparison keeps its prepared receiving sections",
            });
        }
        let branch = BigInt::from(
            field
                .ring(phases.ring())
                .clock_at(&current.lift()[phases.ring()])?
                .winding()
                .clone(),
        );
        let ratio = ReceivingFaceRatio::compare_partition(faces, observed, branch)?;
        let covector = ratio.covector()?;
        let (pullback, opening) = self.pull_back_full(
            &covector,
            theta
                .receiving_map(phases.ring())
                .ok_or(HnnError::Unadmitted {
                    reason: "the producing receiving relation of the observed comparison",
                })?,
            &current.lift()[phases.ring()],
            &phases,
        )?;
        let diamond = Diamond::opened(field, &phases, &support);
        let composed = crate::hnn::reference::compose_return(
            field,
            &theta,
            &diamond,
            current.lift(),
            &current,
            &source,
            &pullback,
        )?;
        let mut linear: Vec<_> = composed
            .linear
            .into_iter()
            .filter(|step| step.locus == LinearLocus::Receiving(phases.ring()))
            .collect();
        let mut actual_stations = Vec::new();
        for step in &mut linear {
            if step.samples.len() != ratio.faces().faces.len() {
                return Err(HnnError::Unadmitted {
                    reason: "the observed receiving samples keep every actual producing crossing",
                });
            }
            step.samples = std::mem::take(&mut step.samples)
                .into_iter()
                .enumerate()
                .filter_map(|(j, sample)| {
                    (ratio.stations().contains(&j)
                        && !sample.weight.is_zero()
                        && sample.feature.iter().any(|x| !x.is_zero())
                        && sample.covector.iter().any(|x| !x.is_zero()))
                    .then(|| {
                        actual_stations.push((phases.first_epoch() + j) as u64);
                        sample
                    })
                })
                .collect();
        }
        linear.retain(|step| !step.samples.is_empty());
        actual_stations.sort_unstable();
        actual_stations.dedup();
        let deposit = if linear.is_empty() {
            None
        } else {
            let locus = Locus::ReceivingMap(phases.ring());
            if !composed.reached.contains(&locus) {
                return Err(HnnError::Unadmitted {
                    reason: "the actual receiving comparison reaches its native material locus",
                });
            }
            Some(
                Deposit::new(theta.commit(), linear, vec![], vec![locus]).with_reach(Reach {
                    receiver: phases.ring(),
                    stations: actual_stations,
                    entries: vec![0],
                    phases: composed.phases,
                    loci: diamond.retained(field),
                }),
            )
        };
        Ok(NativeReceivingReturn {
            ratio,
            pullback,
            opening,
            deposit,
        })
    }
}
