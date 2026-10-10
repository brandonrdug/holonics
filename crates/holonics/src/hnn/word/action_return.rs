//! The actual observed receiving face returns through its producing controlled Word.
//!
//! This is an affine receiving-map update.  At fixed producing anchors, R enters linearly;
//! it does not claim a simultaneous receiving-map/contact ray or a world-policy derivative.
//! Source preparation, source moment, current, clocks and the native propagation operands
//! remain bound to the Word.  No requested consequence is used as an observed target.

use super::*;
use crate::hnn::constitution::{LinearLocus, Locus, Reach};
use crate::hnn::port::{ChangeCovector, Deposit, WordReturn, WorldPort};
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
    /// [agent-inferred, October 9; the held-carry record §5] The contact families' factor steps of
    /// the same composed return, the World's returns held: their gradients are that conditional
    /// reading, and their within-Word feature energy and covector scale normalize a World-sensitive
    /// descent of the same comparison. Not deposited here.
    pub contacts: Vec<crate::hnn::constitution::FactorStep>,
    /// [agent-inferred, October 10; the held-carry record §7j] With a World port: the same contact
    /// families' factor steps of the return through the World's transpose, the covector reaching
    /// each family through both paths. `None` without a port.
    pub world_contacts: Option<Vec<crate::hnn::constitution::FactorStep>>,
}

impl Word<'_> {
    pub(crate) fn return_observed_receiving(
        self,
        receiver: usize,
        applied: &action::AppliedPortPreparation,
        observed: Vec<Option<Face>>,
        world: Option<&WorldPort>,
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
        let map = theta
            .receiving_map(phases.ring())
            .ok_or(HnnError::Unadmitted {
                reason: "the producing receiving relation of the observed comparison",
            })?
            .clone();
        let diamond = Diamond::opened(field, &phases, &support);
        // [§7j] Through the World port, beside the native return: the contact families' steps of
        // the covector that reaches them by both paths. The native return below is unchanged.
        let world_contacts = match world {
            None => None,
            Some(port) => {
                let adjoint = port.adjoint(&covector, &phases, applied.compared())?;
                let (through, _) = self.pull_back_world(
                    &covector,
                    &map,
                    &current.lift()[phases.ring()],
                    &phases,
                    &adjoint,
                )?;
                let composed = crate::hnn::reference::compose_return(
                    field,
                    &theta,
                    &diamond,
                    current.lift(),
                    &current,
                    &source,
                    &through,
                )?;
                Some(
                    composed
                        .factors
                        .into_iter()
                        .filter(|step| matches!(step.gradient.locus(), Locus::Channel(_)))
                        .collect(),
                )
            }
        };
        let (pullback, opening) = self.pull_back_full(
            &covector,
            &map,
            &current.lift()[phases.ring()],
            &phases,
        )?;
        let composed = crate::hnn::reference::compose_return(
            field,
            &theta,
            &diamond,
            current.lift(),
            &current,
            &source,
            &pullback,
        )?;
        let contacts: Vec<_> = composed
            .factors
            .iter()
            .filter(|step| matches!(step.gradient.locus(), Locus::Channel(_)))
            .cloned()
            .collect();
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
            // [definition; agent-inferred, October 8] **Each kept sample carries its own produced
            // masses `p̃`.** The observed face is soft: the covector's magnitude entries are
            // `q̃ − p̃` with `q̃` the observed face's odometer masses, so `p̃` cannot be read back from
            // it (the one-hot reconstruction reads `(⅚, ⅙)` for `p̃ = (½, ½)` against
            // `q̃ = (⅔, ⅓)`). The sample at index `j` is the comparison at receiving phase `j`:
            // `compose_return` makes one sample per `back.reads[j]`, whose gradient `pull_back_full`
            // took as `covector.logits()[j]` of this very `ratio` (negated), and
            // `ReceivingFaceRatio::covector` built that entry from `faces[j].odometer_masses()`,
            // `q̃_j` and the phases. So `ratio.faces().faces[j].odometer_masses()` is exactly the
            // `p̃` of sample `j`'s covector; the same `j` selects the compared station above.
            let mut kept = Vec::new();
            for (j, mut sample) in std::mem::take(&mut step.samples).into_iter().enumerate() {
                if ratio.stations().contains(&j)
                    && !sample.weight.is_zero()
                    && sample.feature.iter().any(|x| !x.is_zero())
                    && sample.covector.iter().any(|x| !x.is_zero())
                {
                    actual_stations.push((phases.first_epoch() + j) as u64);
                    sample.masses = Some(ratio.faces().faces[j].odometer_masses()?);
                    kept.push(sample);
                }
            }
            step.samples = kept;
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
            contacts,
            world_contacts,
        })
    }
}
