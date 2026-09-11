//! A fixed normal generator on the admitted difference/comparand source plane.
//! The continuing state is a generator word with its original seed, resident power cache and
//! certified remainder. Current faces are observations of that state, not its history archive.
use super::*;
use std::collections::BTreeMap;
mod actuate;
pub use actuate::NormalSourceActuation;
mod develop;
pub use develop::NormalWaveDevelopment;
mod receive;
pub use receive::{NormalWaveReception, NormalWaveReceptionReading};
mod rest;
pub use rest::NormalWaveRest;
mod family;
pub use family::{NormalWaveFamily,NormalWaveFamilyRest,NormalFamilySupport,NormalFamilyReceiverReading,NormalWaveFamilyReceiver};
mod source;
pub use source::{NormalWaveSource,NormalWaveJointSource};
mod basis;
pub use basis::{NormalWaveBasisChart, NormalWaveBasisFace, NormalWaveBasisReading, NormalBasisSelection, NormalBasisScore};
mod reference;
pub use reference::{NormalWaveReference, NormalWaveReferenceReading};
mod comparison;
use comparison::ProducingCut;
pub use comparison::{NormalProducingHandle, NormalWavePrediction, NormalWaveComparison, NormalWaveComparisonReading};

/// Which operator family the transported enclosure describes. Applied uses the actual stored
/// dyadic M, retaining source uncertainty and numerical realization error. NormalReference also
/// transports the comparison with the compatible normal minimizer P. These are different
/// receivers; the reference certificate is not uncertainty in the chosen coefficients themselves.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum NormalWaveTransport {
    Applied,
    #[default]
    NormalReference,
}
impl NormalWaveTransport {
    fn is_reference(self) -> bool { self == Self::NormalReference }
}

pub struct NormalWaveTransportChange<'c> {
    pub predecessor: NormalWaveFibre<'c>,
    pub successor: NormalWaveFibre<'c>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum NormalWaveSeedKind {
    ExactPair,
    ReceivedCurrent,
    JointEnclosure,
}

struct WaveCurrent<'c> {
    section: ResidentSection<'c>,
    at: Option<u64>,
}
/// A shareable immutable current occurrence. Equality of coordinates is not this identity.
pub struct NormalWaveCurrent<'c> {
    inner: Rc<WaveCurrent<'c>>,
    surface: &'c ResidentSurface<'c>,
    width: usize,
    grain: ResidentGrain,
}
impl<'c> NormalWaveCurrent<'c> {
    pub fn snapshot(&self) -> Self {
        Self {
            inner: Rc::clone(&self.inner),
            surface: self.surface,
            width: self.width,
            grain: self.grain,
        }
    }
    pub fn same_occurrence(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.inner, &other.inner)
    }
    /// None is the initial previous current; Some(k) is the continuing occurrence epoch.
    pub fn at(&self) -> Option<u64> {
        self.inner.at
    }
    pub fn view(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        ResidentNormalEnclosureView {
            surface: self.surface,
            section: &self.inner.section,
            offset: 0,
            width: self.width,
            grain: self.grain,
        }
    }
}

/// The implicit joint family is the repeated same normal-law action on the original rational
/// pair. Its source chart and shared material are retained; no inverse of a source history is used.
pub struct NormalWaveFibre<'c> {
    pub transport: NormalWaveTransport,
    material: Rc<ResidentSection<'c>>,
    seed: Rc<ResidentSection<'c>>,
    surface: &'c ResidentSurface<'c>,
    roots: usize,
    grain: ResidentGrain,
    pub material_observations: u64,
    pub epoch: u64,
    pub seed_kind: NormalWaveSeedKind,
    pub steps: u64,
    pub seed_epochs: [Option<u64>; 2],
}
impl<'c> NormalWaveFibre<'c> {
    /// Share immutable standing and its generating recipe; this never clones a continuing body.
    pub fn snapshot(&self) -> Self {
        Self { material:Rc::clone(&self.material),seed:Rc::clone(&self.seed),
            surface:self.surface,roots:self.roots,grain:self.grain,
            material_observations:self.material_observations,epoch:self.epoch,
            seed_kind:self.seed_kind,steps:self.steps,seed_epochs:self.seed_epochs,
            transport:self.transport }
    }
    /// Exact point initials are available only before a bounded received-state rebase.
    pub fn initial(&self) -> Option<ResidentConstitutiveSection<'_, 'c>> {
        (self.seed_kind == NormalWaveSeedKind::ExactPair).then(|| {
            ResidentConstitutiveSection::rationals(&self.seed).expect("completed wave seed")
        })
    }
    pub fn initial_received(
        &self,
    ) -> Option<(
        ResidentNormalEnclosureView<'_, 'c>,
        ResidentConstitutiveCurrent<'_, 'c>,
    )> {
        (self.seed_kind == NormalWaveSeedKind::ReceivedCurrent).then(|| {
            (
                ResidentNormalEnclosureView {
                    surface: self.surface,
                    section: &self.seed,
                    offset: 0,
                    width: 2 * self.roots,
                    grain: self.grain,
                },
                ResidentConstitutiveSection::rationals(&self.seed)
                    .expect("completed received seed")
                    .row(2)
                    .expect("received current"),
            )
        })
    }
    pub fn initial_joint(&self) -> Option<ResidentNormalEnclosureView<'_, 'c>> {
        (self.seed_kind == NormalWaveSeedKind::JointEnclosure).then(|| {
            ResidentNormalEnclosureView {
                surface: self.surface,
                section: &self.seed,
                offset: 0,
                width: 4 * self.roots,
                grain: self.grain,
            }
        })
    }
    pub fn inspect_material(&self) -> Result<NativeNormalMaterialState, ConstitutiveFibreError> {
        decode_state(
            &self.surface.detach_section(&self.material, i64::BITS)?,
            self.roots,
            self.roots,
            self.grain.0,
        )
    }
}

#[derive(Debug, Serialize)]
pub struct NormalWaveReading {
    pub transport: NormalWaveTransport,
    pub steps: u64,
    pub maximum_computed_power_norm: Rat,
    pub uniform_power_equation_defect: Rat,
    pub operator_word_error: Rat,
    pub joint_current: NativeFieldCurrentBall,
}
pub struct NormalWaveStep<'c> {
    pub previous: NormalWaveCurrent<'c>,
    pub current: NormalWaveCurrent<'c>,
    pub fibre: NormalWaveFibre<'c>,
    joint: Rc<ResidentSection<'c>>,
    metadata: Rc<ResidentSection<'c>>,
}
impl NormalWaveStep<'_> {
    pub fn inspect(&self) -> Result<NormalWaveReading, ConstitutiveFibreError> {
        let surface = self.current.surface;
        let meta = wides(&surface.read_out(&self.metadata)?)?;
        let scale = BigInt::one() << self.current.grain.0;
        let joint = ResidentNormalEnclosureView {
            surface,
            section: &self.joint,
            offset: 0,
            width: 2 * self.current.width,
            grain: self.current.grain,
        }
        .inspect()?;
        Ok(NormalWaveReading {
            transport: self.fibre.transport,
            steps: self.fibre.steps,
            maximum_computed_power_norm: Rat::from_integer(meta[0].into()),
            uniform_power_equation_defect: Rat::new(meta[1].into(), scale.clone()),
            operator_word_error: Rat::new(meta[2].into(), scale),
            joint_current: joint,
        })
    }
}

pub struct NormalWaveSeedRefusal<'c> {
    pub material: ResidentNormalMaterial<'c>,
    pub reason: ConstitutiveFibreError,
}
impl std::fmt::Debug for NormalWaveSeedRefusal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.reason.fmt(f)
    }
}

pub struct ResidentNormalWave<'c> {
    transport: NormalWaveTransport,
    owner: Rc<()>,
    pending: BTreeMap<u64, Rc<ProducingCut<'c>>>,
    material: ResidentNormalMaterial<'c>,
    seed: Rc<ResidentSection<'c>>,
    seed_bound: Rc<ResidentSection<'c>>,
    joint: Rc<ResidentSection<'c>>,
    seed_kind: NormalWaveSeedKind,
    epoch: u64,
    power: ResidentSection<'c>,
    metadata: Rc<ResidentSection<'c>>,
    previous: NormalWaveCurrent<'c>,
    current: NormalWaveCurrent<'c>,
    steps: u64,
    seed_epochs: [Option<u64>; 2],
}
impl<'c> ResidentNormalMaterial<'c> {
    /// Declare the binding R(c-p,c,p) as a change in c's receiver chart. Matching dimensions
    /// alone does not establish that application-level chart; the caller supplies this binding.
    /// The learned material moves into the generator and remains fixed during its word.
    pub fn into_difference_wave(
        self,
        previous: ResidentConstitutiveCurrent<'_, 'c>,
        current: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentNormalWave<'c>, NormalWaveSeedRefusal<'c>> {
        self.into_difference_wave_source(previous.into(), current)
    }
    /// Found transport by the selected stored M from the supplied actual initial pair.
    /// The normal-reference certificate remains on material; it is not input uncertainty.
    pub fn into_applied_difference_wave(
        self,
        previous: ResidentConstitutiveCurrent<'_, 'c>,
        current: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentNormalWave<'c>, NormalWaveSeedRefusal<'c>> {
        let mut body = self.into_difference_wave(previous,current)?;
        body.transport = NormalWaveTransport::Applied;
        Ok(body)
    }
    fn into_difference_wave_source(
        self,
        previous: ResidentNormalInput<'_, 'c>,
        current: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentNormalWave<'c>, NormalWaveSeedRefusal<'c>> {
        let seed_kind = match previous {
            ResidentNormalInput::Point(_) => NormalWaveSeedKind::ExactPair,
            ResidentNormalInput::Enclosed(_) => NormalWaveSeedKind::ReceivedCurrent,
        };
        let staged = self.prepare_wave_seed(previous, current);
        match staged {
            Ok(StagedWaveSeed {
                seed,
                seed_bound,
                power,
                metadata,
                previous,
                current,
            }) => {
                let seed_bound = Rc::new(seed_bound);
                Ok(ResidentNormalWave {
                    transport: NormalWaveTransport::NormalReference,
                    owner: Rc::new(()),
                    pending: BTreeMap::new(),
                    material: self,
                    seed: Rc::new(seed),
                    joint: Rc::clone(&seed_bound),
                    seed_bound,
                    power,
                    metadata: Rc::new(metadata),
                    previous,
                    current,
                    steps: 0,
                    epoch: 0,
                    seed_kind,
                    seed_epochs: [None, Some(0)],
                })
            }
            Err(reason) => Err(NormalWaveSeedRefusal {
                material: self,
                reason,
            }),
        }
    }
}
struct StagedWaveSeed<'c> {
    seed: ResidentSection<'c>,
    seed_bound: ResidentSection<'c>,
    power: ResidentSection<'c>,
    metadata: ResidentSection<'c>,
    previous: NormalWaveCurrent<'c>,
    current: NormalWaveCurrent<'c>,
}
impl<'c> ResidentNormalMaterial<'c> {
    fn prepare_wave_seed(
        &self,
        previous: ResidentNormalInput<'_, 'c>,
        current: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<StagedWaveSeed<'c>, ConstitutiveFibreError> {
        let seed_kind = match previous {
            ResidentNormalInput::Point(_) => NormalWaveSeedKind::ExactPair,
            ResidentNormalInput::Enclosed(_) => NormalWaveSeedKind::ReceivedCurrent,
        };
        if self.roots != self.targets
            || previous.width() != 2 * self.roots
            || current.width != previous.width()
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let s = self.surface;
        let r = previous.width();
        let d = 2 * self.roots;
        let fresh = |width| s.fresh_section(1, width, ResidentGrain(0));
        let rows = if seed_kind == NormalWaveSeedKind::ExactPair {
            2
        } else {
            3
        };
        let seed = s.fresh_section(rows, r + 1, ResidentGrain(0))?;
        let seed_bound = fresh(2 * (2 * r + 1))?;
        let p = fresh(2 * (r + 1))?;
        let c = fresh(2 * (r + 1))?;
        let power = fresh(4 * d * d)?;
        let metadata = fresh(8)?;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_normal_wave_seed(
                &lane,
                previous,
                current,
                self.roots,
                self.grain.0,
                &seed,
                &seed_bound,
                &p,
                &c,
                &power,
                &metadata,
            )?;
        }
        passage.close(0, &seed_bound, i64::BITS)?;
        let returned = passage.finish()?.launch()?;
        if !returned.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "wave seed: {:?}",
                returned.obstruction
            )));
        }
        let wrap = |section, at| NormalWaveCurrent {
            inner: Rc::new(WaveCurrent { section, at }),
            surface: s,
            width: r,
            grain: self.grain,
        };
        let previous = wrap(p, None);
        let current = wrap(c, Some(0));
        Ok(StagedWaveSeed {
            seed,
            seed_bound,
            power,
            metadata,
            previous,
            current,
        })
    }
}
impl<'c> ResidentNormalWave<'c> {
    pub fn transport(&self) -> NormalWaveTransport { self.transport }

    /// Change the future operator-family receiver, never reinterpret or narrow the held joint.
    /// Rebase at this cut so a reference word is not silently re-read as an applied word.
    pub fn set_transport(
        &mut self,
        transport: NormalWaveTransport,
    ) -> Result<NormalWaveTransportChange<'c>, ConstitutiveFibreError> {
        let predecessor = self.fibre();
        if self.transport != transport {
            let staged = self.material.prepare_joint_seed(&self.joint,self.epoch)?;
            self.seed = Rc::clone(&self.joint);
            self.seed_bound = Rc::clone(&self.joint);
            self.seed_kind = NormalWaveSeedKind::JointEnclosure;
            self.power = staged.power;
            self.metadata = Rc::new(staged.metadata);
            self.steps = 0;
            self.seed_epochs = [self.previous.at(),self.current.at()];
            self.transport = transport;
        }
        Ok(NormalWaveTransportChange { predecessor, successor:self.fibre() })
    }

    pub fn epoch(&self) -> u64 {
        self.epoch
    }
    pub fn steps(&self) -> u64 {
        self.steps
    }
    pub fn previous(&self) -> &NormalWaveCurrent<'c> {
        &self.previous
    }
    pub fn current(&self) -> &NormalWaveCurrent<'c> {
        &self.current
    }
    pub fn fibre(&self) -> NormalWaveFibre<'c> {
        NormalWaveFibre {
            transport: self.transport,
            material: Rc::clone(&self.material.state),
            seed: Rc::clone(&self.seed),
            surface: self.material.surface,
            roots: self.material.roots,
            grain: self.material.grain,
            material_observations: self.material.observations,
            epoch: self.epoch,
            seed_kind: self.seed_kind,
            steps: self.steps,
            seed_epochs: self.seed_epochs,
        }
    }
    pub fn advance(&mut self) -> Result<NormalWaveStep<'c>, ConstitutiveFibreError> {
        let steps = self
            .steps
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let epoch = self
            .epoch
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let s = self.material.surface;
        let n = self.material.roots;
        let d = 2 * n;
        let r = 2 * n;
        let fresh = |width| s.fresh_section(1, width, ResidentGrain(0));
        let power = fresh(4 * d * d)?;
        let metadata = fresh(8)?;
        let joint = fresh(2 * (2 * r + 1))?;
        let current = fresh(2 * (r + 1))?;
        let work = fresh(6 * d)?;
        let mut passage = s.begin_passage(&[vec![], vec![0]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_normal_wave_power(
                &lane,
                &self.material.state,
                &self.power,
                n,
                self.material.grain.0,
                &power,
            )?;
        }
        passage.close(0, &power, i64::BITS)?;
        {
            let lane = passage.open(1, &[0])?;
            s.record_normal_wave_evaluate(
                &lane,
                &self.material.state,
                &power,
                &self.seed_bound,
                &self.metadata,
                n,
                self.material.grain.0,
                steps,
                &metadata,
                &joint,
                &current,
                &work,
                self.transport.is_reference(),
            )?;
        }
        passage.close(1, &joint, i64::BITS)?;
        let returned = passage.finish()?.launch()?;
        if !returned.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "wave continuation: {:?}",
                returned.obstruction
            )));
        }
        let current = NormalWaveCurrent {
            inner: Rc::new(WaveCurrent {
                section: current,
                at: Some(epoch),
            }),
            surface: s,
            width: r,
            grain: self.material.grain,
        };
        let previous = std::mem::replace(&mut self.current, current);
        self.previous = previous;
        self.power = power;
        self.metadata = Rc::new(metadata);
        self.steps = steps;
        self.epoch = epoch;
        self.joint = Rc::new(joint);
        Ok(NormalWaveStep {
            previous: self.previous.snapshot(),
            current: self.current.snapshot(),
            fibre: self.fibre(),
            joint: Rc::clone(&self.joint),
            metadata: Rc::clone(&self.metadata),
        })
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod comparison_tests;

#[cfg(test)]
mod transport_tests;

#[cfg(test)]
mod basis_tests;
