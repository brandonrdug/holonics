//! Separate class-coordinate application of the recovered empirical law (Refs #73 #62).
//! Actual testimony is an admitted Encoded e_k. Prefix context is the declared
//! source-opening coordinate, sealed BEFORE reading y. u=eta_M controls B=P^lift E;
//! it is neither a token continuation nor wave testimony. Actual ingress happens
//! once, independently of fit publication. No CE veto or source/R overwrite.
use super::observed::{IngestClassReceipt, ObservedCrib};
use super::*;
use crate::hnn::encoding::observed::PairedObservation;
use crate::hnn::paired::PairingDeclaration;
use crate::hnn::physical::action::contextual::{Complex, ContextualBounds, EmpiricalMaterial};
use crate::hnn::word::action::{PortPreparationReceipt, SourceClassPreparation};
use crate::ratio::linear::ExactRatMatrix;
use num_traits::{One, Zero};
use std::sync::Arc;
use std::time::Instant;
fn refuse(reason: &'static str) -> HnnError {
    HnnError::Unadmitted { reason }
}
fn embed(x: &[Rat]) -> Vec<Complex> {
    x.iter().map(|q| [q.clone(), Rat::zero()]).collect()
}
fn onehot(n: usize, k: usize) -> Vec<Rat> {
    (0..n)
        .map(|j| if j == k { Rat::one() } else { Rat::zero() })
        .collect()
}
fn feature(n: usize, p: usize, c: usize, h: &Rat) -> Vec<Complex> {
    let p = onehot(n, p);
    let c = onehot(n, c);
    let mut a: Vec<_> = c.iter().zip(&p).map(|(c, p)| c - p).collect();
    a.extend(c);
    a.extend(p);
    let mut f = a.clone();
    f.push(h.clone());
    f.extend(a.iter().map(|a| h * a));
    embed(&f)
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassInputBranch {
    pub id: u64,
    pub material: EmpiricalMaterial,
}
/// Original co-indexed producing operands. Only accepted actual returns wait here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassInputPending {
    pub address: u64,
    pub commit: u64,
    pub lift: Vec<BigInt>,
    pub previous: usize,
    pub current: usize,
    pub context: Rat,
    pub feature: Vec<Complex>,
    pub actual: usize,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ClassInputWork {
    pub actual_arrivals: u64,
    pub material_publications: u64,
    pub successful_fit_proposals: u64,
}
#[derive(Clone, Debug)]
pub struct ClassInput {
    resident: Resident,
    crib: ObservedCrib,
    pairing: PairingDeclaration,
    boundary: PairedObservation,
    ring: usize,
    context_coordinate: usize,
    units: String,
    bounds: ContextualBounds,
    history: Vec<usize>,
    accepted: u64,
    branches: Vec<ClassInputBranch>,
    pending: BTreeMap<u64, ClassInputPending>,
    work: ClassInputWork,
}
#[derive(Debug)]
pub struct ClassInputReceipt {
    pub address: u64,
    pub native: IngestClassReceipt,
    pub material: Result<(), HnnError>,
    pub producing: Option<ClassInputPending>,
    pub prefix_context_ns: u128,
    pub native_ingress_ns: u128,
    pub material_formation_ns: u128,
}
/// Native Word actually consuming this branch's control, not an affine output surrogate.
pub struct ClassInputProspect<'a> {
    pub branch: u64,
    pub context: Rat,
    pub control: Vec<Rat>,
    pub preparation: ExactRatMatrix,
    pub lift: BigInt,
    pub work: PortPreparationReceipt,
    pub native: Word<'a>,
    pub contraction_ns: u128,
    pub preparation_ns: u128,
    pub forward_ns: u128,
    pub forward_passes: u64,
    pub adjoint_passes: u64,
}
impl ClassInput {
    #[allow(clippy::too_many_arguments)]
    pub fn found(
        resident: Resident,
        crib: ObservedCrib,
        pairing: PairingDeclaration,
        boundary: PairedObservation,
        ring: usize,
        context_coordinate: usize,
        units: String,
        bounds: ContextualBounds,
        ids: &[u64],
    ) -> Result<Self, HnnError> {
        bounds.admit()?;
        resident.admit_exact_current()?;
        boundary.check_material(&resident.constitution)?;
        resident.field.admit(&boundary.encode(&[])?)?;
        if resident.participating_world.is_some()
            || resident.moments.len() != 1
            || resident.moments.values().next().map(SourceMoment::cells) != Some(0)
            || !resident.pending.is_empty()
            || !resident.staged.is_empty()
            || resident.arrived.is_some()
            || crib.next_position() != 0
            || units.is_empty()
            || !resident.field.is_source(ring)
            || context_coordinate >= resident.field.ring(ring).width()
            || ids.is_empty()
            || ids.len() > bounds.branches
            || ids
                .iter()
                .copied()
                .collect::<std::collections::BTreeSet<_>>()
                .len()
                != ids.len()
        {
            return Err(refuse(
                "fresh class material at one actual native source with declared finite support",
            ));
        }
        let n = resident.field.alphabet();
        let f = 6 * n + 1;
        if f > bounds.max_features
            || (2 * f).pow(3) as u64 * ids.len() as u64 > bounds.max_scalar_work
        {
            return Err(refuse("bounded class-coordinate empirical formation work"));
        }
        // Also checks whole-opening/exact-domain admission; no receiving forward or J.
        let source = Arc::new(resident.moments.values().next().unwrap().clone());
        let (word, _) = Word::open_source_exact_received(
            &resident.field,
            &resident.constitution,
            &resident.current,
            source,
            &resident.reception_opening(),
        )?;
        SourceClassPreparation::at(&word, &boundary, ring)?;
        let branches = ids
            .iter()
            .map(|&id| ClassInputBranch {
                id,
                material: EmpiricalMaterial::found(f, n),
            })
            .collect();
        Ok(Self {
            resident,
            crib,
            pairing,
            boundary,
            ring,
            context_coordinate,
            units,
            bounds,
            history: Vec::new(),
            accepted: 0,
            branches,
            pending: BTreeMap::new(),
            work: ClassInputWork::default(),
        })
    }
    pub fn resident(&self) -> &Resident {
        &self.resident
    }
    pub fn boundary(&self) -> &PairedObservation {
        &self.boundary
    }
    pub fn branches(&self) -> &[ClassInputBranch] {
        &self.branches
    }
    pub fn pending(&self) -> &BTreeMap<u64, ClassInputPending> {
        &self.pending
    }
    pub fn work(&self) -> &ClassInputWork {
        &self.work
    }
    pub fn accepted(&self) -> u64 {
        self.accepted
    }
    fn word(&self) -> Result<Word<'_>, HnnError> {
        self.boundary.check_material(&self.resident.constitution)?;
        let source = Arc::new(
            self.resident
                .moments
                .values()
                .next()
                .ok_or(refuse("one actual class source moment"))?
                .clone(),
        );
        Ok(Word::open_source_exact_received(
            &self.resident.field,
            &self.resident.constitution,
            &self.resident.current,
            source,
            &self.resident.reception_opening(),
        )?
        .0)
    }
    fn context(&self) -> Result<Rat, HnnError> {
        self.boundary.check_material(&self.resident.constitution)?;
        let source = self
            .resident
            .moments
            .values()
            .next()
            .ok_or(refuse("one actual prefix source moment"))?;
        let storage = source.open_storage(
            &self.resident.field,
            &self.resident.constitution,
            &self.resident.current,
        )?;
        Ok(storage[self.ring][self.context_coordinate].clone())
    }
    /// `address` is actual accepted offset, not a freely rebound material commit.
    /// Prefix h is sealed before this routine reads Encoded's later y.
    pub fn observe(
        &mut self,
        reference: &Reference,
        encoded: &Encoded,
        at: usize,
        address: u64,
    ) -> Result<ClassInputReceipt, HnnError> {
        self.observe_with_formation_limit(reference, encoded, at, address, self.bounds.branches)
    }
    pub fn observe_with_formation_limit(
        &mut self,
        reference: &Reference,
        encoded: &Encoded,
        at: usize,
        address: u64,
        maximum_branch_stages: usize,
    ) -> Result<ClassInputReceipt, HnnError> {
        if address != self.accepted
            || encoded.observation() != Some(&self.boundary)
            || encoded.placement().is_some()
            || self.pending.len() >= self.bounds.pending
        {
            return Err(refuse(
                "next actual addressed class at its immutable boundary and bounded outstanding returns",
            ));
        }
        self.resident.field.admit(encoded)?;
        self.boundary.check_material(&self.resident.constitution)?;
        let started = Instant::now();
        let h = self.context()?;
        // No target read before this producing feature is sealed.
        let producing = if self.history.len() == 2 {
            Some((
                self.history[0],
                self.history[1],
                feature(
                    self.resident.field.alphabet(),
                    self.history[0],
                    self.history[1],
                    &h,
                ),
            ))
        } else {
            None
        };
        let prefix_context_ns = started.elapsed().as_nanos();
        let class = encoded
            .cells()
            .get(at)
            .ok_or(refuse("an actual class occurrence"))?
            .class();
        let mut next = self.clone();
        let commit = next.resident.constitution.commit();
        let lift = next.resident.current.lift().to_vec();
        let started = Instant::now();
        // Ingest failure publishes neither material nor testimony. Successful ingress is
        // retained even if subsequent material publication refuses.
        let native = reference.ingest_class_continuing(
            &mut next.resident,
            &mut next.crib,
            &next.pairing,
            class,
            None,
        )?;
        let native_ingress_ns = started.elapsed().as_nanos();
        next.accepted = next
            .accepted
            .checked_add(1)
            .ok_or(HnnError::CountOverflow)?;
        next.work.actual_arrivals += 1;
        next.history.push(class);
        if next.history.len() > 2 {
            next.history.remove(0);
        }
        if let Some((previous, current, feature)) = producing {
            next.pending.insert(
                address,
                ClassInputPending {
                    address,
                    commit,
                    lift,
                    previous,
                    current,
                    context: h,
                    feature,
                    actual: class,
                },
            );
        }
        let producing = next.pending.get(&address).cloned();
        let started = Instant::now();
        let material = if next.pending.contains_key(&address) {
            next.form_with_formation_limit(address, maximum_branch_stages)
        } else {
            Ok(())
        };
        let material_formation_ns = started.elapsed().as_nanos();
        *self = next;
        Ok(ClassInputReceipt {
            address,
            native,
            material,
            producing,
            prefix_context_ns,
            native_ingress_ns,
            material_formation_ns,
        })
    }
    pub fn form(&mut self, address: u64) -> Result<(), HnnError> {
        self.form_with_formation_limit(address, self.bounds.branches)
    }
    pub fn form_with_formation_limit(
        &mut self,
        address: u64,
        maximum_branch_stages: usize,
    ) -> Result<(), HnnError> {
        let cut = self
            .pending
            .get(&address)
            .ok_or(refuse("one unconsumed actual class return"))?;
        let n = self.resident.field.alphabet();
        let y = onehot(n, cut.actual);
        let c = onehot(n, cut.current);
        let eta = embed(&y.iter().zip(c).map(|(y, c)| y - c).collect::<Vec<_>>());
        let mut staged = Vec::new();
        for (index, b) in self.branches.iter().enumerate() {
            if index >= maximum_branch_stages {
                return Err(refuse("bounded requested class material work"));
            }
            staged.push(b.material.stage(&cut.feature, &eta, &self.bounds)?);
            self.work.successful_fit_proposals += 1;
        }
        for (b, m) in self.branches.iter_mut().zip(staged) {
            b.material = m;
        }
        self.pending.remove(&address);
        self.work.material_publications += 1;
        Ok(())
    }
    /// Each branch is evaluated on a disposable native Word. Material response is
    /// CONTROL eta_M, without adding c or injecting another exterior arrival.
    pub fn prospects(
        &self,
        ticks: usize,
        max_abs_work: &Rat,
    ) -> Result<Vec<ClassInputProspect<'_>>, HnnError> {
        if ticks == 0 || ticks > 64 || self.history.len() != 2 {
            return Err(refuse(
                "bounded class prospect after two actual observations",
            ));
        }
        let h = self.context()?;
        let f = feature(
            self.resident.field.alphabet(),
            self.history[0],
            self.history[1],
            &h,
        );
        self.bounds.check(f.iter().flat_map(|z| z.iter()))?;
        let mut out = Vec::new();
        for b in &self.branches {
            let started = Instant::now();
            let response = b.material.contract(&f)?;
            if response.iter().any(|z| !z[1].is_zero()) {
                return Err(refuse(
                    "real class-coordinate controls without imaginary projection",
                ));
            }
            let control = response.iter().map(|z| z[0].clone()).collect::<Vec<_>>();
            let contraction_ns = started.elapsed().as_nanos();
            let word = self.word()?;
            let started = Instant::now();
            let binding = SourceClassPreparation::at(&word, &self.boundary, self.ring)?;
            if binding.source_opening()[self.context_coordinate] != h {
                return Err(refuse(
                    "same actual producing prefix context and whole source opening",
                ));
            }
            let preparation = binding.preparation().map().clone();
            let lift = binding.lift().clone();
            let (mut native, work) =
                binding.apply(word, &control, max_abs_work, self.bounds.rational_bits)?;
            let preparation_ns = started.elapsed().as_nanos();
            let started = Instant::now();
            native.run(ticks)?;
            let forward_ns = started.elapsed().as_nanos();
            out.push(ClassInputProspect {
                branch: b.id,
                context: h.clone(),
                control,
                preparation,
                lift,
                work,
                native,
                contraction_ns,
                preparation_ns,
                forward_ns,
                forward_passes: 1,
                adjoint_passes: 0,
            });
        }
        Ok(out)
    }
}

// Length-framed exterior composite: complete native continuation + finite crib +
// bounded class material/original outstanding sources, with no World or event archive.
mod checkpoint;
#[cfg(test)]
mod tests;
