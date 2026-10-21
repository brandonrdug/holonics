//! A bounded, explicitly attached contextual response law. Actual wave testimony
//! and branch-local empirical material have separate owners from source E and R.
use super::{NativeEncounter, WaveJointStep};
use crate::hnn::receiving::ReceivingPhases;
use crate::hnn::word::{Word, action::CoupledPassage};
use crate::hnn::{Encoded, Field, HnnError};
use crate::ratio::{Rat, integer};
use num_traits::{Signed, Zero};
use std::collections::BTreeMap;
mod material;
pub use material::{Complex, EmpiricalMaterial};
use material::{complex, features, minus, plus, real};
fn refusal(reason: &'static str) -> HnnError {
    HnnError::Unadmitted { reason }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContextualBounds {
    pub branches: usize,
    pub pending: usize,
    pub precision_bits: u32,
    pub rational_bits: u64,
    pub max_features: usize,
    pub max_scalar_work: u64,
}
impl ContextualBounds {
    fn admit(&self) -> Result<(), HnnError> {
        if self.branches == 0
            || self.branches > 64
            || self.pending == 0
            || self.pending > 64
            || !(1..=30).contains(&self.precision_bits)
            || self.rational_bits < 64
            || self.rational_bits > 4096
            || self.max_features == 0
            || self.max_features > 64
        {
            return Err(refusal(
                "finite contextual branch/pending/precision/range declarations",
            ));
        }
        Ok(())
    }
    fn check<'a>(&self, values: impl Iterator<Item = &'a Rat>) -> Result<(), HnnError> {
        if values
            .into_iter()
            .any(|q| q.numer().bits() > self.rational_bits || q.denom().bits() > self.rational_bits)
        {
            return Err(refusal("contextual rational range bound"));
        }
        Ok(())
    }
}
/// Explicit same-port Cartesian chart and units. Context is the actual incident
/// wave, sealed before its response. Declaring this port is not a language codec.
#[derive(Clone, Debug, PartialEq)]
pub struct WaveObservationPort {
    pub ring: usize,
    pub width: usize,
    pub units: String,
    pub chart: Encoded,
    pub field: Field,
    pub admittance: Rat,
    pub step: Rat,
}
impl WaveObservationPort {
    fn immutable_identity_text(&self) -> String {
        format!(
            "wave-observation-port-v1|{}|{}|{:?}|{}|{:?}|{}|{}",
            self.ring,
            self.width,
            self.units,
            self.chart.immutable_identity_text(),
            self.field,
            self.admittance,
            self.step
        )
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContextualBranch {
    pub id: u64,
    pub previous: Vec<Complex>,
    pub current: Vec<Complex>,
    pub prior_is_observed: bool,
    pub material: EmpiricalMaterial,
}
/// Complete discrete support. Prior alternatives are declarations, not two
/// incompatible claims of fully observed history. No error-based elimination.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContextualPrior {
    pub id: u64,
    pub previous: Vec<Rat>,
    pub current: Vec<Rat>,
    pub observed: bool,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct BranchCut {
    previous_is_observed: bool,
    current_is_observed: bool,
    theta: u64,
    previous: Vec<Complex>,
    current: Vec<Complex>,
    context: Vec<Complex>,
    feature: Vec<Complex>,
    produced: Vec<Complex>,
    material_observations: u64,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Pending {
    native_tick: usize,
    opened_at: usize,
    producing_commit: u64,
    incident: Vec<Rat>,
    branches: Vec<BranchCut>,
    actual: Option<Vec<Complex>>,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ContextualWork {
    pub sealed_occurrences: u64,
    pub actual_returns: u64,
    pub material_formations: u64,
    pub branch_formations: u64,
    pub normal_fits: u64,
    pub response_contractions: u64,
    pub prospective_word_passages: u64,
    pub ce_candidate_word_replays: u64,
}
/// Transient prospective response plus the Word that actually consumed that branch's
/// callbacks. Counts are completed owner calls, not GPU kernels or root iterations.
pub struct ContextualProspect<'w> {
    pub branch_id: u64,
    pub passage: CoupledPassage,
    pub native: Word<'w>,
    pub response_contractions: u64,
    pub native_word_passages: u64,
}
#[derive(Clone, Debug, PartialEq)]
pub struct ContextualFamily {
    port: WaveObservationPort,
    bounds: ContextualBounds,
    branches: Vec<ContextualBranch>,
    pending: BTreeMap<u64, Pending>,
    next_id: u64,
    actual_tick: usize,
    automatic: bool,
    actual_history_depth: u8,
    work: ContextualWork,
    last_refusal: Option<String>,
}
impl ContextualFamily {
    pub fn found(
        port: WaveObservationPort,
        bounds: ContextualBounds,
        priors: Vec<ContextualPrior>,
        actual_tick: usize,
        automatic: bool,
    ) -> Result<Self, HnnError> {
        bounds.admit()?;
        if port.ring >= port.field.rings().len()
            || !port.field.sources().contains(&port.ring)
            || port.field.ring(port.ring).width() != port.width
            || port.field.ring(port.ring).admittance() != &port.admittance
            || port.field.step() != &port.step
        {
            return Err(refusal(
                "the declared contextual port on its exact native field",
            ));
        }
        let n = port.width / 2;
        let f = 3 * n + n + 3 * n * n;
        if port.width == 0
            || port.width % 2 != 0
            || port.units.is_empty()
            || port.admittance <= Rat::zero()
            || port.step <= Rat::zero()
            || priors.is_empty()
            || priors.len() > bounds.branches
            || f > bounds.max_features
        {
            return Err(refusal(
                "one bounded same-port complex observation and context declaration",
            ));
        }
        let mut ids = std::collections::BTreeSet::new();
        let mut branches = Vec::new();
        let mut observed_prior = None;
        for p in priors {
            if !ids.insert(p.id) || p.previous.len() != port.width || p.current.len() != port.width
            {
                return Err(refusal(
                    "distinct co-indexed branches with full source frames",
                ));
            }
            bounds.check(p.previous.iter().chain(&p.current))?;
            if p.observed {
                let pair = (p.previous.clone(), p.current.clone());
                if observed_prior.as_ref().is_some_and(|q| q != &pair) {
                    return Err(refusal(
                        "fully observed histories cannot differ across supported alternatives",
                    ));
                }
                observed_prior = Some(pair);
            }
            branches.push(ContextualBranch {
                id: p.id,
                previous: complex(&p.previous)?,
                current: complex(&p.current)?,
                prior_is_observed: p.observed,
                material: EmpiricalMaterial::found(f, n),
            });
        }
        if let Some((p, c)) = &observed_prior {
            if branches
                .iter()
                .any(|b| real(&b.previous) != *p || real(&b.current) != *c)
            {
                return Err(refusal(
                    "every branch respects fully observed original p/c testimony",
                ));
            }
        }
        if observed_prior.is_some() {
            for b in &mut branches {
                b.prior_is_observed = true;
            }
        }
        let d = (2 * f) as u64;
        let work = (branches.len() as u64)
            .checked_mul(d * d * d + 10 * d * d + 10 * d)
            .ok_or(HnnError::CountOverflow)?;
        if work > bounds.max_scalar_work {
            return Err(refusal("declared bounded normal-formation scalar work"));
        }
        let actual_history_depth = if branches.iter().all(|b| b.prior_is_observed) {
            2
        } else {
            0
        };
        Ok(Self {
            port,
            bounds,
            branches,
            pending: BTreeMap::new(),
            next_id: 0,
            actual_tick,
            automatic,
            actual_history_depth,
            work: ContextualWork::default(),
            last_refusal: None,
        })
    }
    pub fn port(&self) -> &WaveObservationPort {
        &self.port
    }
    pub fn branches(&self) -> &[ContextualBranch] {
        &self.branches
    }
    pub fn work(&self) -> &ContextualWork {
        &self.work
    }
    pub fn actual_tick(&self) -> usize {
        self.actual_tick
    }
    pub fn pending_ids(&self) -> Vec<u64> {
        self.pending.keys().copied().collect()
    }
    pub fn last_refusal(&self) -> Option<&str> {
        self.last_refusal.as_deref()
    }
    pub(super) fn admit(
        &self,
        field: &Field,
        chart: &Encoded,
        ring: usize,
        width: usize,
        y: &Rat,
        h: &Rat,
        tick: usize,
    ) -> Result<(), HnnError> {
        if &self.port.field != field
            || &self.port.chart != chart
            || ring != self.port.ring
            || width != self.port.width
            || y != &self.port.admittance
            || h != &self.port.step
            || tick != self.actual_tick
        {
            return Err(refusal(
                "the contextual observation port's actual chart/units/admittance/step/clock",
            ));
        }
        Ok(())
    }
    /// Called only by the actual world owner after source_wave and before Robin return.
    pub(super) fn before(
        &mut self,
        word: &Word<'_>,
        incident: &[Rat],
        commit: u64,
    ) -> Result<u64, HnnError> {
        if self.pending.len() >= self.bounds.pending {
            return Err(refusal("bounded outstanding original contextual cuts"));
        }
        let tick = word
            .opened_at()
            .checked_add(word.ticks())
            .ok_or(HnnError::CountOverflow)?;
        if tick != self.actual_tick + 1 || incident.len() != self.port.width {
            return Err(refusal(
                "a contextual pre-return on the next actual native tick",
            ));
        }
        self.bounds.check(incident.iter())?;
        let context = complex(incident)?;
        let mut cuts = Vec::new();
        for b in &self.branches {
            let f = features(&b.previous, &b.current, &context);
            self.bounds.check(f.iter().flat_map(|v| v.iter()))?;
            let eta = b.material.contract(&f)?;
            cuts.push(BranchCut {
                theta: b.id,
                previous_is_observed: b.prior_is_observed || self.actual_history_depth >= 2,
                current_is_observed: b.prior_is_observed || self.actual_history_depth >= 1,
                previous: b.previous.clone(),
                current: b.current.clone(),
                context: context.clone(),
                feature: f,
                produced: b
                    .current
                    .iter()
                    .zip(eta)
                    .map(|(c, e)| plus(c, &e))
                    .collect(),
                material_observations: b.material.observations,
            });
        }
        let id = self.next_id;
        self.next_id = self.next_id.checked_add(1).ok_or(HnnError::CountOverflow)?;
        self.pending.insert(
            id,
            Pending {
                native_tick: tick,
                opened_at: word.opened_at(),
                producing_commit: commit,
                incident: incident.to_vec(),
                branches: cuts,
                actual: None,
            },
        );
        self.work.sealed_occurrences += 1;
        self.work.response_contractions += self.branches.len() as u64;
        Ok(id)
    }
    /// Actual history advances once because this physical encounter happened. Failure
    /// of empirical formation cannot rewind it or relabel its b as a prediction.
    pub(super) fn after(&mut self, id: u64, step: &WaveJointStep) -> Result<(), HnnError> {
        let p = self
            .pending
            .get_mut(&id)
            .ok_or(refusal("one original contextual occurrence"))?;
        if p.actual.is_some()
            || step.native_tick != p.native_tick
            || step.incident != p.incident
            || step.native_tick != self.actual_tick + 1
        {
            return Err(refusal("one same-cut actual addressed reflected wave"));
        }
        let y = complex(&step.reflected)?;
        if step.reflected.len() != self.port.width {
            return Err(refusal("the declared reflected wave extent"));
        }
        p.actual = Some(y.clone());
        self.actual_history_depth = (self.actual_history_depth + 1).min(2);
        for b in &mut self.branches {
            b.previous = std::mem::replace(&mut b.current, y.clone());
            b.prior_is_observed = self.actual_history_depth == 2;
        }
        self.actual_tick = step.native_tick;
        self.work.actual_returns += 1;
        if self.automatic {
            if let Err(e) = self.form(id) {
                self.last_refusal = Some(e.to_string());
            }
        }
        Ok(())
    }
    /// Material reads the ORIGINAL joint source/context and ACTUAL y. Delayed returns
    /// update contemporary branch material, never a stale material snapshot or marginal.
    /// All supported branches stage before any material/pending publication.
    pub fn form(&mut self, id: u64) -> Result<(), HnnError> {
        self.form_with_work_bound(id, self.bounds.branches)
    }
    /// A bounded requested material formation may stop after a staged branch. No
    /// branch material or pending token publishes until the complete family stages.
    pub fn form_with_work_bound(
        &mut self,
        id: u64,
        maximum_branch_stages: usize,
    ) -> Result<(), HnnError> {
        let p = self
            .pending
            .get(&id)
            .ok_or(refusal("unconsumed contextual observation ID"))?;
        let actual = p.actual.as_ref().ok_or(refusal(
            "an actual addressed return before empirical formation",
        ))?;
        let mut staged = Vec::new();
        for (index, b) in self.branches.iter().enumerate() {
            if index >= maximum_branch_stages {
                return Err(refusal(
                    "bounded requested contextual branch formation work",
                ));
            }
            let cut = p
                .branches
                .iter()
                .find(|c| c.theta == b.id)
                .ok_or(refusal("original jointly supported branch frame"))?;
            let eta: Vec<_> = actual
                .iter()
                .zip(&cut.current)
                .map(|(y, c)| minus(y, c))
                .collect();
            staged.push(b.material.stage(&cut.feature, &eta, &self.bounds)?);
            self.work.normal_fits += 1;
        }
        for (b, m) in self.branches.iter_mut().zip(staged) {
            b.material = m;
        }
        self.pending.remove(&id);
        self.work.material_formations += 1;
        self.work.branch_formations += self.branches.len() as u64;
        Ok(())
    }
    /// Each branch receives its own simulated source/context and native Word. Nothing
    /// actual advances, and predicted b is never fed into form as observation.
    pub(super) fn prospects<'w>(
        &self,
        word: &Word<'w>,
        phases: &ReceivingPhases,
        compared: &[bool],
    ) -> Result<Vec<ContextualProspect<'w>>, HnnError> {
        if word.opened_at() != self.actual_tick {
            return Err(refusal(
                "a contextual prospect at its actual retained crossing",
            ));
        }
        let mut out = Vec::new();
        for b in &self.branches {
            let mut p = b.previous.clone();
            let mut c = b.current.clone();
            let mut calls = 0;
            let mut returns = |_: usize, a: &[Rat]| {
                calls += 1;
                let h = complex(a)?;
                let f = features(&p, &c, &h);
                self.bounds.check(f.iter().flat_map(|v| v.iter()))?;
                let eta = b.material.contract(&f)?;
                let next: Vec<_> = c.iter().zip(eta).map(|(v, e)| plus(v, &e)).collect();
                p = std::mem::replace(&mut c, next.clone());
                let r = real(&next);
                self.bounds.check(r.iter())?;
                Ok(r)
            };
            let (passage, native) = word.prospective_coupled_passage(
                self.port.ring,
                phases,
                compared,
                &mut returns,
                &mut |_, _| Ok(()),
            )?;
            out.push(ContextualProspect {
                branch_id: b.id,
                passage,
                native,
                response_contractions: calls,
                native_word_passages: 1,
            });
        }
        Ok(out)
    }
    /// Actual encounter evidence can be inspected without calling any target extractor.
    pub fn actual_returns<'a>(
        &self,
        encounter: &'a NativeEncounter,
    ) -> Result<&'a [WaveJointStep], HnnError> {
        if encounter.chart() != &self.port.chart || encounter.after_native_tick > self.actual_tick {
            return Err(refusal("the bound contextual encounter lineage"));
        }
        Ok(encounter.steps())
    }
}

mod checkpoint;
#[cfg(test)]
mod tests;
