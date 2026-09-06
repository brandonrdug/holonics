//! Independent exterior current compensation using the public native session, not a private
//! learner. The world's measured upstream response and downstream state are distinct ports.
use super::*;
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};

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
}

#[derive(Clone, Debug, Serialize)]
pub struct WaveInterruption {
    pub cycle: usize,
    pub stage: &'static str,
    pub detail: String,
}
#[derive(Clone, Debug, Serialize)]
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
    spec.validate()?;
    let initial = spec.world.initial_state.current()?;
    let mut world = WaveWorld {
        couplings: spec
            .world
            .couplings
            .iter()
            .map(CurrentWire::current)
            .collect::<Result<_, _>>()?,
        rotation: spec.world.state_rotation.current()?,
        state: initial.clone(),
        unactuated: initial,
    };
    let mut cycles = Vec::new();
    cycles
        .try_reserve(spec.cycles)
        .map_err(|e| NativeSessionError::Application(e.to_string()))?;
    with_native_session(&spec.model, |session| {
        let mut step = session.receive(&spec.initial_current, None)?;
        let mut interruption = None;
        let mut pending_receive = None;
        'run: for cycle in 0..spec.cycles {
            for event in spec
                .interventions
                .iter()
                .filter(|e| e.before_cycle == cycle)
            {
                let result = match &event.change {
                    WaveChange::Rechart { gauges } => session.rechart(gauges).map(|_| ()),
                    WaveChange::ReplaceIncidence { node, transport } => {
                        session.replace_incidence(*node, transport)
                    }
                };
                if let Err(error) = result {
                    interruption = Some(WaveInterruption {
                        cycle,
                        stage: "intervention",
                        detail: error.to_string(),
                    });
                    break 'run;
                }
            }
            let measured = match world.measured(&step.root_source_currents) {
                Ok(value) => value,
                Err(error) => {
                    interruption = Some(WaveInterruption {
                        cycle,
                        stage: "world-measurement",
                        detail: error.to_string(),
                    });
                    break;
                }
            };
            // Actuation is exactly the native admitted receiver current. The application never
            // calculates a fitted map or substitutes the world response for a missing inference.
            let actuation_result = (|| -> Result<_, NativeSessionError> {
                Ok(match &step.receiver {
                    ReceiverWire::Unique { current } if current.len() == 2 => {
                        Some(ExactComplexWaveCurrent::new(
                            current[0].rational()?,
                            current[1].rational()?,
                        ))
                    }
                    ReceiverWire::Unique { .. } => {
                        return Err(NativeSessionError::Application(
                            "the actuator requires one phase-pair receiver".into(),
                        ))
                    }
                    ReceiverWire::OutsideDomain { .. } | ReceiverWire::Plural { .. } => None,
                })
            })();
            let actuation = match actuation_result {
                Ok(value) => value,
                Err(error) => {
                    interruption = Some(WaveInterruption {
                        cycle,
                        stage: "actuator-projection",
                        detail: error.to_string(),
                    });
                    break;
                }
            };
            let residual = world.advance(&measured, actuation.as_ref());
            let receiving = CurrentWire::from_current(&measured);
            cycles.push(WaveCycle {
                cycle,
                native: step.clone(),
                measured_current: receiving.clone(),
                actuation: actuation.as_ref().map(CurrentWire::from_current),
                residual: CurrentWire::from_current(&residual),
                world_state: CurrentWire::from_current(&world.state),
                unactuated_state: CurrentWire::from_current(&world.unactuated),
                world_norm_square: RationalWire::from_rational(&world.state.norm_square()),
                unactuated_norm_square: RationalWire::from_rational(
                    &world.unactuated.norm_square(),
                ),
            });
            match session.receive(&receiving, Some(step.source)) {
                Ok(next) => step = next,
                Err(error) => {
                    interruption = Some(WaveInterruption {
                        cycle,
                        stage: "native-reception",
                        detail: error.to_string(),
                    });
                    pending_receive = Some(PendingWaveReceive {
                        current: receiving,
                        source: step.source,
                    });
                    break;
                }
            }
        }
        Ok(WaveControlRun {
            schema: WAVE_CONTROL_SCHEMA,
            cycles,
            final_native: step,
            anatomy: session.inspect(),
            persistent: false,
            interruption,
            pending_receive,
            final_world_state: CurrentWire::from_current(&world.state),
            final_unactuated_state: CurrentWire::from_current(&world.unactuated),
        })
    })
}
