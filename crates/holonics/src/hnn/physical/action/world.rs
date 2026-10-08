//! The actual participating Holon at a power-conjugate wave boundary.
//!
//! The HNN action inference never reads this law's coefficients. Only the actual interaction
//! owner uses them to solve the Robin termination `a=e+Y^(-1)f`. The returned wave is
//! `b=e-Y^(-1)f`, so `e.f = sum Y(a²-b²)/4`. Both participants continue on the solved state.
//! This is the quadratic midpoint domain; no waveform is substituted for an effort input.

use crate::hnn::HnnError;
use crate::hnn::encoding::Encoded;
use crate::hnn::ratio::Face;
use crate::hnn::receiving::ReceivingRead;
use crate::holon::law::{HolonLaw, Scheme};
use crate::holon::{HolonError, HolonState};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{add, dot, sub};
use crate::ratio::{Rat, integer};
use crate::receiver::receipt::{Receipt, ReceiptLaw};
use crate::receiver::reception::{JointLaw, JointStep, ReceiverFace};
use num_traits::{Signed, Zero};

/// A solved actual interaction and its complete wave/effort/flow power reading.
#[derive(Debug)]
pub struct WaveJointStep {
    pub native_tick: usize,
    pub joint: JointStep,
    pub receipt: Receipt,
    pub incident: Vec<Rat>,
    pub reflected: Vec<Rat>,
    pub effort: Vec<Rat>,
    pub flow: Vec<Rat>,
    pub power: Rat,
    pub port_work: Rat,
}

impl WaveJointStep {
    pub fn closes(&self, admittance: &[Rat], h: &Rat) -> bool {
        if self.incident.len() != admittance.len()
            || self.reflected.len() != admittance.len()
            || self.effort.len() != admittance.len()
            || self.flow.len() != admittance.len()
        {
            return false;
        }
        let wave_power: Rat = admittance
            .iter()
            .zip(&self.incident)
            .zip(&self.reflected)
            .map(|((y, a), b)| y * (a * a - b * b) / integer(4))
            .sum();
        self.power == wave_power
            && self.power == dot(&self.effort, &self.flow)
            && self.joint.boundary().effort() == self.effort
            && self.joint.boundary().flow() == self.flow
            && self
                .incident
                .iter()
                .zip(&self.reflected)
                .zip(&self.effort)
                .all(|((a, b), e)| a + b == integer(2) * e)
            && self
                .incident
                .iter()
                .zip(&self.reflected)
                .zip(&self.flow)
                .zip(admittance)
                .all(|(((a, b), f), y)| y * (a - b) == integer(2) * f)
            && self.port_work == h * &self.power
            && self.joint.balance().port == self.port_work
            && self.joint.stored_after().joint() - self.joint.stored_before().joint()
                == self.joint.balance().stored_change
            && self.joint.balance().is_exact()
    }
}

/// An actual world producer, its current state and its declared common receiving chart.
/// Fields are private: source/clock identity and the solved next state cannot be overwritten.
/// The chart declares native log-amplitude/phase receiving coordinates, including their units;
/// a raw Cartesian quadrature is not thereby declared a lifted phase. Other chart/clock laws
/// need their actual transport before this consumer can admit them.
#[derive(Debug)]
pub struct BoundJointWorld {
    law: JointLaw,
    state: HolonState,
    face: ReceiverFace,
    receipt: ReceiptLaw,
    admittance: Vec<Rat>,
    common_chart: Encoded,
    native_origin: usize,
    world_origin: u64,
    /// A copied diagnostic current cannot become another active World execution.
    executable: bool,
}

/// Constructed only by the actual native encounter, never by an observation callback.
#[derive(Debug)]
pub struct NativeEncounter {
    pub before_native_tick: usize,
    pub after_native_tick: usize,
    pub before_world_tick: u64,
    pub after_world_tick: u64,
    chart: Encoded,
    steps: Vec<WaveJointStep>,
    observed: Vec<Option<Face>>,
}

impl NativeEncounter {
    pub fn chart(&self) -> &Encoded {
        &self.chart
    }
    pub fn steps(&self) -> &[WaveJointStep] {
        &self.steps
    }
    pub fn observed(&self) -> &[Option<Face>] {
        &self.observed
    }
}

/// A stopped actual encounter and every already executed interaction. Its physical state
/// remains published in BoundJointWorld; absence of a target at an unreached region is explicit.
#[derive(Debug)]
pub struct NativeEncounterFailure {
    pub error: HnnError,
    pub partial: NativeEncounter,
}

// Resident::clone is an exterior diagnostic copy. Preserve its actual physical state but
// refuse execution from that copy before either participant moves; never branch a live World.
impl Clone for BoundJointWorld {
    fn clone(&self) -> Self {
        Self {
            law: self.law.clone(),
            state: self.state.clone(),
            face: self.face.clone(),
            receipt: self.receipt.clone(),
            admittance: self.admittance.clone(),
            common_chart: self.common_chart.clone(),
            native_origin: self.native_origin,
            world_origin: self.world_origin,
            executable: false,
        }
    }
}

impl BoundJointWorld {
    /// The common chart is the full cell-free producing chart, not an equal class count.
    /// The two clock origins are an explicit affine identification; the actual world commit
    /// is retained unchanged. The first domain has equal clock steps and a fixed receiving map.
    pub fn new(
        law: JointLaw,
        state: HolonState,
        face: ReceiverFace,
        receipt: ReceiptLaw,
        admittance: Vec<Rat>,
        common_chart: Encoded,
        native_origin: usize,
    ) -> Result<Self, HnnError> {
        let counts = law.law().holon().counts();
        if law.law().scheme() != Scheme::Midpoint
            || law.law().holon().loaded_parametron().is_some()
            || law.source_extent() == 0
            || law.receiver_extent() == 0
            || state.configuration.len() != counts.storage
            || counts.external == 0
            || admittance.len() != counts.external
            || admittance.iter().any(|y| !y.is_positive())
            || face.chart_rate().iter().any(|x| !x.is_zero())
            || !common_chart.is_empty()
            || common_chart.classes() == 0
            || common_chart.located().is_some()
            || !common_chart.fibre().is_empty()
            || *common_chart.decoder() != ExactRatMatrix::identity(common_chart.classes())?
        {
            return Err(HnnError::Unadmitted {
                reason: "a two-participant exact midpoint world, positive wave chart and fixed common identity receiving chart",
            });
        }
        let initial = face.read(
            &state.configuration[..law.source_extent()],
            &state.configuration[law.source_extent()..],
        )?;
        if initial.len() != 2 * common_chart.classes() {
            return Err(HnnError::Unadmitted {
                reason: "the world face declares the complete realified common receiving carrier",
            });
        }
        let world_origin = state.commit;
        Ok(Self {
            law,
            state,
            face,
            receipt,
            admittance,
            common_chart,
            native_origin,
            world_origin,
            executable: true,
        })
    }

    pub fn state(&self) -> &HolonState {
        &self.state
    }
    pub fn common_chart(&self) -> &Encoded {
        &self.common_chart
    }
    pub fn native_tick(&self) -> Result<usize, HnnError> {
        let elapsed = self
            .state
            .commit
            .checked_sub(self.world_origin)
            .ok_or(HnnError::CountOverflow)?;
        self.native_origin
            .checked_add(usize::try_from(elapsed).map_err(|_| HnnError::CountOverflow)?)
            .ok_or(HnnError::CountOverflow)
    }

    pub(crate) fn admit(
        &self,
        chart: &Encoded,
        source_wave: &[Rat],
        y: &Rat,
        h: &Rat,
        native_tick: usize,
    ) -> Result<(), HnnError> {
        if !self.executable
            || &self.common_chart != chart
            || source_wave.len() != self.admittance.len()
            || self.admittance.iter().any(|actual| actual != y)
            || self.law.law().step() != h
            || self.native_tick()? != native_tick
        {
            return Err(HnnError::Unadmitted {
                reason: "the actual world and prepared source bind one wave frame, complete chart and actual clock",
            });
        }
        Ok(())
    }

    fn interact_wave(&mut self, incident: &[Rat]) -> Result<WaveJointStep, HnnError> {
        let reference = self.law.law();
        let holon = reference.holon();
        let counts = holon.counts();
        let n = counts.total();
        let pi = counts.external;
        let po = counts.storage + counts.resistive;
        if incident.len() != pi {
            return Err(HnnError::Unadmitted {
                reason: "an actual incoming wave on every declared external port",
            });
        }
        let zero = vec![Rat::zero(); pi];
        let coefficients = reference.prepare_commit(
            &self.state,
            &zero,
            holon.storage_at(self.state.commit),
            holon.active().relation(),
            holon.storage_at(
                self.state
                    .commit
                    .checked_add(1)
                    .ok_or(HnnError::CountOverflow)?,
            ),
        )?;
        if coefficients.system.rows() != n || coefficients.system.columns() != n {
            return Err(HnnError::Unadmitted {
                reason: "a square actual midpoint Dirac commit before Robin coupling",
            });
        }
        // Solve the actual Dirac step and Robin boundary together in (z,e), not by evaluating
        // the world at guessed drive points.  system z - external_target e = target;
        // e + Y^-1 (F_P z + c_P) = a.
        let mut rows = vec![vec![Rat::zero(); n + pi]; n + pi];
        let mut target = coefficients.target.clone();
        for i in 0..n {
            for j in 0..n {
                rows[i][j] = coefficients.system.get(i, j)?.clone();
            }
            for j in 0..pi {
                rows[i][n + j] = -coefficients.external_target.get(i, j)?;
            }
        }
        for i in 0..pi {
            for j in 0..n {
                rows[n + i][j] =
                    coefficients.flow_coefficient.get(po + i, j)? / &self.admittance[i];
            }
            rows[n + i][n + i] = integer(1);
            target.push(&incident[i] - &coefficients.flow_constant[po + i] / &self.admittance[i]);
        }
        let system = ExactRatMatrix::new(rows)?;
        let solved = match system.preimage_fibre(&target)? {
            None => return Err(HolonError::Inconsistent.into()),
            Some((point, kernel)) if kernel.is_empty() => point,
            Some((_, kernel)) => {
                return Err(HolonError::NotUniquelySolvable {
                    nullity: kernel.len(),
                }
                .into());
            }
        };
        let effort = solved[n..].to_vec();
        let full_flow = add(
            &coefficients.flow_coefficient.apply(&solved[..n])?,
            &coefficients.flow_constant,
        );
        let flow = full_flow[po..po + pi].to_vec();
        let impedance_flow: Vec<_> = flow
            .iter()
            .zip(&self.admittance)
            .map(|(f, y)| f / y)
            .collect();
        if add(&effort, &impedance_flow) != incident {
            return Err(HnnError::Unadmitted {
                reason: "the actual Robin solve closes its incident wave",
            });
        }
        let reflected = sub(&effort, &impedance_flow);
        let returned = self
            .law
            .interact(&self.state, &effort, &self.face, &self.receipt)?;
        let receipt = returned.receipt;
        let joint = returned
            .forward
            .into_present()
            .ok_or(HnnError::Realization {
                what: "the actual solved two-participant world interaction",
            })?;
        let native_tick = self
            .native_tick()?
            .checked_add(1)
            .ok_or(HnnError::CountOverflow)?;
        let power = dot(&effort, &flow);
        let port_work = reference.step() * &power;
        let step = WaveJointStep {
            native_tick,
            joint,
            receipt,
            incident: incident.to_vec(),
            reflected,
            effort,
            flow,
            power,
            port_work,
        };
        if !step.closes(&self.admittance, reference.step()) {
            return Err(HnnError::Unadmitted {
                reason: "the actual world step and conjugate wave interface close their work",
            });
        }
        // Publish only the native solved point. No caller selects one from a singular fibre.
        self.state = step.joint.next_state();
        if self.native_tick()? != native_tick {
            return Err(HnnError::CountOverflow);
        }
        Ok(step)
    }

    /// One actual co-clock native/World passage. Each native full tick emits its actual
    /// source storage wave, and the actual Robin return replaces that storage BEFORE
    /// the next native tick. SourceMoment is neither changed nor injected a second time.
    pub(super) fn execute_word(
        &mut self,
        word: &mut crate::hnn::word::Word<'_>,
        source_ring: usize,
        ticks: usize,
        epochs: &[usize],
        compared: &[bool],
        grain: u64,
    ) -> Result<NativeEncounter, NativeEncounterFailure> {
        let before_native_tick = word.opened_at();
        let before_world_tick = self.state.commit;
        let mut encounter = NativeEncounter {
            before_native_tick,
            after_native_tick: before_native_tick,
            before_world_tick,
            after_world_tick: before_world_tick,
            chart: self.common_chart.clone(),
            steps: Vec::with_capacity(ticks),
            observed: vec![None; epochs.len()],
        };
        if epochs.len() != compared.len()
            || epochs
                .iter()
                .zip(compared)
                .any(|(&e, &yes)| yes && (e == 0 || e >= ticks))
            || self.native_tick().ok() != Some(before_native_tick)
            || word.ticks() != 0
        {
            return Err(NativeEncounterFailure {
                error: HnnError::Unadmitted {
                    reason: "actual receiving sections and an unrun native Word on one World clock",
                },
                partial: encounter,
            });
        }
        for t in 1..=ticks {
            // A failure does not rewind either participant. The owning consumer publishes
            // the reached native carry, retains this World and returns this partial receipt.
            let result = (|| {
                word.tick()?;
                encounter.after_native_tick = word.opened_at() + word.ticks();
                let incident = word.source_wave(source_ring)?.to_vec();
                let step = self.interact_wave(&incident)?;
                encounter.after_world_tick = self.state.commit;
                // Preserve the executed World step even if its native boundary join refuses.
                encounter.steps.push(step);
                let step = encounter
                    .steps
                    .last()
                    .expect("the actual completed interaction");
                word.return_source_wave(
                    source_ring,
                    step.native_tick,
                    &step.incident,
                    &step.reflected,
                    &step.port_work,
                )?;
                for (j, (&e, &yes)) in epochs.iter().zip(compared).enumerate() {
                    if yes && e == t {
                        encounter.observed[j] = Some(Face::of_read(
                            &ReceivingRead::of_logits(step.joint.face().to_vec(), grain),
                            grain,
                        )?);
                    }
                }
                Ok::<_, HnnError>(())
            })();
            if let Err(error) = result {
                return Err(NativeEncounterFailure {
                    error,
                    partial: encounter,
                });
            }
        }
        if encounter
            .observed
            .iter()
            .zip(compared)
            .any(|(face, &yes)| face.is_some() != yes)
        {
            return Err(NativeEncounterFailure {
                error: HnnError::Unadmitted {
                    reason: "every compared target was actually received at its bound World section",
                },
                partial: encounter,
            });
        }
        Ok(encounter)
    }

    /// Mutable retained current, not transient step receipts or a history of actions.
    /// Immutable declarations are held separately; this is their current-state bit reading.
    pub fn current_bits(&self) -> u64 {
        self.state
            .configuration
            .iter()
            .map(|x| x.numer().bits() + x.denom().bits())
            .sum::<u64>()
            + u64::from(u64::BITS - self.state.commit.leading_zeros())
            + u64::from(usize::BITS - self.native_origin.leading_zeros())
            + u64::from(u64::BITS - self.world_origin.leading_zeros())
    }
}
