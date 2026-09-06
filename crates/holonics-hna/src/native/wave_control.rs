//! Independent exterior current compensation using the public native session, not a private
//! learner. The world's measured upstream response and downstream state are distinct ports.
use super::*;
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};
mod session;
pub use session::{
    resume_wave_control, run_wave_control_with_options, WaveApplication, WaveBoundary,
    WaveRunOptions, WaveSavedApplication,
};

pub const WAVE_CONTROL_SCHEMA: &str = "org.holonics.hna.wave-control.v1";

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WaveWorldSpec {
    pub couplings: Vec<CurrentWire>,
    pub state_rotation: CurrentWire,
    pub initial_state: CurrentWire,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "action", rename_all = "kebab-case", deny_unknown_fields)]
pub enum WaveChange {
    Rechart { gauges: Vec<CurrentWire> },
    ReplaceIncidence { node: usize, transport: CurrentWire },
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WaveIntervention {
    pub before_cycle: usize,
    pub change: WaveChange,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WaveControlSpec {
    pub schema: String,
    pub model: NativeModelSpec,
    pub world: WaveWorldSpec,
    pub initial_current: CurrentWire,
    pub cycles: usize,
    #[serde(default)]
    pub interventions: Vec<WaveIntervention>,
}

#[derive(Clone, Debug, Serialize)]
pub struct WaveCycle {
    pub cycle: usize,
    pub native: NativeSessionStep,
    pub measured_current: CurrentWire,
    pub actuation: Option<CurrentWire>,
    pub residual: CurrentWire,
    pub world_state: CurrentWire,
    pub unactuated_state: CurrentWire,
    pub world_norm_square: RationalWire,
    pub unactuated_norm_square: RationalWire,
}
#[derive(Clone, Debug, Serialize)]
pub struct WaveControlRun {
    pub schema: &'static str,
    pub cycles: Vec<WaveCycle>,
    pub final_native: NativeSessionStep,
    pub anatomy: NativeSessionAnatomy,
    pub persistent: bool,
    pub interruption: Option<WaveInterruption>,
    pub pending_receive: Option<PendingWaveReceive>,
    pub final_world_state: CurrentWire,
    pub final_unactuated_state: CurrentWire,
    pub next_cycle: usize,
    pub boundary: WaveBoundary,
    pub complete: bool,
    pub checkpoint: Option<std::path::PathBuf>,
    pub checkpoint_octets: Option<u64>,
    pub checkpoint_error: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct WaveInterruption {
    pub cycle: usize,
    pub stage: &'static str,
    pub detail: String,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PendingWaveReceive {
    pub current: CurrentWire,
    pub source: u64,
}

struct WaveWorld {
    couplings: Vec<ExactComplexWaveCurrent>,
    rotation: ExactComplexWaveCurrent,
    state: ExactComplexWaveCurrent,
    unactuated: ExactComplexWaveCurrent,
}
impl WaveWorld {
    fn measured(
        &self,
        source: &[CurrentWire],
    ) -> Result<ExactComplexWaveCurrent, NativeSessionError> {
        if source.len() != self.couplings.len() {
            return Err(NativeSessionError::Application(
                "wave port population differs".into(),
            ));
        }
        source.iter().zip(&self.couplings).try_fold(
            ExactComplexWaveCurrent::zero(),
            |sum, (source, coupling)| Ok(sum.add(&coupling.multiply(&source.current()?))),
        )
    }
    fn advance(
        &mut self,
        measured: &ExactComplexWaveCurrent,
        actuation: Option<&ExactComplexWaveCurrent>,
    ) -> ExactComplexWaveCurrent {
        // Absence is an open actuator port, not a guessed zero model answer.
        let residual = actuation.map_or_else(|| measured.clone(), |a| measured.subtract(a));
        self.state = self.rotation.multiply(&self.state).add(&residual);
        self.unactuated = self.rotation.multiply(&self.unactuated).add(measured);
        residual
    }
}

impl WaveControlSpec {
    pub fn validate(&self) -> Result<(), NativeSessionError> {
        self.model.material()?;
        self.initial_current.native()?;
        if self.schema != WAVE_CONTROL_SCHEMA
            || self.cycles == 0
            || self.world.couplings.len() != self.model.nodes.len()
        {
            return Err(NativeSessionError::Application(
                "wave-control schema, cycle count or port population".into(),
            ));
        }
        self.world.initial_state.current()?;
        if self.world.state_rotation.current()?.norm_square() != Rat::from_integer(1.into()) {
            return Err(NativeSessionError::Application(
                "world state rotation must be an exact unit phase".into(),
            ));
        }
        for coupling in &self.world.couplings {
            coupling.current()?;
        }
        for event in &self.interventions {
            if event.before_cycle >= self.cycles {
                return Err(NativeSessionError::Application(
                    "intervention is outside the declared run".into(),
                ));
            }
            match &event.change {
                WaveChange::Rechart { gauges } => {
                    if gauges.len() != self.model.nodes.len() {
                        return Err(NativeSessionError::Application(
                            "gauge population differs".into(),
                        ));
                    }
                    for g in gauges {
                        g.native()?;
                        if g.current()?.norm_square() != Rat::from_integer(1.into()) {
                            return Err(NativeSessionError::Application(
                                "gauge is not a unit phase".into(),
                            ));
                        }
                    }
                }
                WaveChange::ReplaceIncidence { node, transport } => {
                    transport.native()?;
                    if *node >= self.model.nodes.len()
                        || transport.current()?.norm_square() != Rat::from_integer(1.into())
                    {
                        return Err(NativeSessionError::Application(
                            "physical incidence change is outside the declared chart".into(),
                        ));
                    }
                }
            }
        }
        Ok(())
    }
}

pub fn run_wave_control(spec: &WaveControlSpec) -> Result<WaveControlRun, NativeSessionError> {
    run_wave_control_with_options(spec, &WaveRunOptions::default())
}
