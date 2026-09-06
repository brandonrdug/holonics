//! The independent application's continuing state. These exterior effect/delivery boundaries
//! do not partition native inference/training or supply a second learning mechanism.
use super::*;
use crate::{publication::PublicationReceipt, HnaStreamState};
use std::path::{Path, PathBuf};

const APPLICATION_SCHEMA: &str = "org.holonics.hna.wave-application.v1";
fn invalid(detail: impl std::fmt::Display) -> NativeSessionError {
    NativeSessionError::Application(format!("wave continuation: {detail}"))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum WaveBoundary {
    Intervention,
    World,
    Reception,
    Complete,
}
impl WaveBoundary {
    fn stage(self) -> &'static str {
        match self {
            Self::Intervention => "intervention",
            Self::World => "world-interaction",
            Self::Reception => "native-reception",
            Self::Complete => "complete",
        }
    }
}

/// A process cut, not a native semantic budget. None runs to the declared application end.
#[derive(Default)]
pub struct WaveRunOptions {
    pub cycles: Option<usize>,
    pub checkpoint: Option<PathBuf>,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WaveApplication {
    schema: String,
    spec: WaveControlSpec,
    cycle: usize,
    intervention_cursor: usize,
    boundary: WaveBoundary,
    world_state: CurrentWire,
    unactuated_state: CurrentWire,
    step: NativeSessionStep,
    pending: Option<PendingWaveReceive>,
}

impl WaveApplication {
    pub fn found(
        spec: &WaveControlSpec,
        session: &mut NativeSession<'_>,
    ) -> Result<Self, NativeSessionError> {
        spec.validate()?;
        if !session.matches_untouched_seed(&spec.model)? {
            return Err(invalid(
                "application founding requires its declared untouched seed",
            ));
        }
        let step = session.receive(&spec.initial_current, None)?;
        let mut app = Self {
            schema: APPLICATION_SCHEMA.into(),
            spec: spec.clone(),
            cycle: 0,
            intervention_cursor: 0,
            boundary: WaveBoundary::World,
            world_state: spec.world.initial_state.clone(),
            unactuated_state: spec.world.initial_state.clone(),
            step,
            pending: None,
        };
        app.select_next_boundary();
        Ok(app)
    }
    pub fn next_cycle(&self) -> usize {
        self.cycle
    }
    pub fn boundary(&self) -> WaveBoundary {
        self.boundary
    }
    pub fn intervention_cursor(&self) -> usize {
        self.intervention_cursor
    }
    pub fn pending_receive(&self) -> Option<&PendingWaveReceive> {
        self.pending.as_ref()
    }
    pub fn final_native(&self) -> &NativeSessionStep {
        &self.step
    }
    pub fn world_state(&self) -> &CurrentWire {
        &self.world_state
    }
    pub fn unactuated_state(&self) -> &CurrentWire {
        &self.unactuated_state
    }
    fn intervention_count(&self) -> usize {
        self.spec
            .interventions
            .iter()
            .filter(|e| e.before_cycle == self.cycle)
            .count()
    }
    fn select_next_boundary(&mut self) {
        self.boundary = if self.cycle == self.spec.cycles {
            WaveBoundary::Complete
        } else if self.intervention_cursor < self.intervention_count() {
            WaveBoundary::Intervention
        } else {
            WaveBoundary::World
        };
    }
    fn validate(&self) -> Result<(), NativeSessionError> {
        self.spec.validate()?;
        if self.schema != APPLICATION_SCHEMA
            || self.cycle > self.spec.cycles
            || self.cycle.checked_add(1).is_none()
            || self.intervention_cursor > self.intervention_count()
            || (self.cycle == self.spec.cycles) != (self.boundary == WaveBoundary::Complete)
            || (self.boundary == WaveBoundary::Intervention
                && self.intervention_cursor == self.intervention_count())
            || (matches!(self.boundary, WaveBoundary::World | WaveBoundary::Reception)
                && self.intervention_cursor != self.intervention_count())
            || (self.pending.is_some() != (self.boundary == WaveBoundary::Reception))
            || self.step.native_occurrence != self.cycle
            || self.step.predecessor_state != self.cycle.checked_sub(1)
        {
            return Err(invalid(
                "application position or pending-reception boundary",
            ));
        }
        self.world_state.current()?;
        self.unactuated_state.current()?;
        if let Some(p) = &self.pending {
            p.current.current()?;
            if p.source != self.step.source {
                return Err(invalid("pending current does not carry the emitted source"));
            }
        }
        let n = self.spec.model.nodes.len();
        if self.step.local_source_currents.len() != n
            || self.step.root_source_currents.len() != n
            || self.step.frame.root_to_local.len() != n
        {
            return Err(invalid("emitted port/frame population"));
        }
        for ((local, root), gauge) in self
            .step
            .local_source_currents
            .iter()
            .zip(&self.step.root_source_currents)
            .zip(&self.step.frame.root_to_local)
        {
            let gauge = gauge.current()?;
            if gauge.norm_square() != Rat::from_integer(1.into())
                || gauge.multiply(&root.current()?) != local.current()?
            {
                return Err(invalid("emission does not carry its root-to-local frame"));
            }
        }
        match &self.step.receiver {
            ReceiverWire::Unique { current } => {
                if current.len() != 2 {
                    return Err(invalid("phase receiver population"));
                }
                for r in current {
                    r.rational()?;
                }
            }
            ReceiverWire::OutsideDomain { source_remainder } => {
                if source_remainder.len() != 2 * n {
                    return Err(invalid("source remainder population"));
                }
                for r in source_remainder {
                    r.rational()?;
                }
            }
            ReceiverWire::Plural {
                particular,
                directions,
            } => {
                if particular.len() != 2
                    || directions.is_empty()
                    || directions.iter().any(|r| r.len() != 2)
                {
                    return Err(invalid("plural phase receiver population"));
                }
                for r in particular.iter().chain(directions.iter().flatten()) {
                    r.rational()?;
                }
            }
        }
        Ok(())
    }
    fn validate_session(&self, session: &NativeSession<'_>) -> Result<(), NativeSessionError> {
        if session.occurrence_count() != self.cycle + 1
            || session.nodes() != self.spec.model.nodes.len()
            || !session.has_source(self.step.source)
        {
            return Err(invalid(
                "native owner has advanced outside this application's retained boundary",
            ));
        }
        Ok(())
    }
    /// Enact exactly one next exterior effect or its native receiving. A failed native receiving
    /// retains the enacted world state and exact pending current; retry cannot repeat the world.
    pub fn advance_boundary(
        &mut self,
        session: &mut NativeSession<'_>,
    ) -> Result<Option<WaveCycle>, NativeSessionError> {
        self.validate_session(session)?;
        match self.boundary {
            WaveBoundary::Complete => Ok(None),
            WaveBoundary::Intervention => {
                let event = self
                    .spec
                    .interventions
                    .iter()
                    .filter(|e| e.before_cycle == self.cycle)
                    .nth(self.intervention_cursor)
                    .ok_or_else(|| invalid("intervention cursor"))?;
                match &event.change {
                    WaveChange::Rechart { gauges } => {
                        session.rechart(gauges)?;
                    }
                    WaveChange::ReplaceIncidence { node, transport } => {
                        session.replace_incidence(*node, transport)?
                    }
                }
                self.intervention_cursor += 1;
                self.select_next_boundary();
                Ok(None)
            }
            WaveBoundary::World => {
                let mut world = WaveWorld {
                    couplings: self
                        .spec
                        .world
                        .couplings
                        .iter()
                        .map(CurrentWire::current)
                        .collect::<Result<_, _>>()?,
                    rotation: self.spec.world.state_rotation.current()?,
                    state: self.world_state.current()?,
                    unactuated: self.unactuated_state.current()?,
                };
                let measured = world.measured(&self.step.root_source_currents)?;
                let actuation = match &self.step.receiver {
                    ReceiverWire::Unique { current } if current.len() == 2 => {
                        Some(ExactComplexWaveCurrent::new(
                            current[0].rational()?,
                            current[1].rational()?,
                        ))
                    }
                    ReceiverWire::Unique { .. } => {
                        return Err(invalid("the actuator requires one phase-pair receiver"))
                    }
                    ReceiverWire::OutsideDomain { .. } | ReceiverWire::Plural { .. } => None,
                };
                let residual = world.advance(&measured, actuation.as_ref());
                let receiving = CurrentWire::from_current(&measured);
                let world_state = CurrentWire::from_current(&world.state);
                let unactuated_state = CurrentWire::from_current(&world.unactuated);
                let cycle = WaveCycle {
                    cycle: self.cycle,
                    native: self.step.clone(),
                    measured_current: receiving.clone(),
                    actuation: actuation.as_ref().map(CurrentWire::from_current),
                    residual: CurrentWire::from_current(&residual),
                    world_state: world_state.clone(),
                    unactuated_state: unactuated_state.clone(),
                    world_norm_square: RationalWire::from_rational(&world.state.norm_square()),
                    unactuated_norm_square: RationalWire::from_rational(
                        &world.unactuated.norm_square(),
                    ),
                };
                self.world_state = world_state;
                self.unactuated_state = unactuated_state;
                self.pending = Some(PendingWaveReceive {
                    current: receiving,
                    source: self.step.source,
                });
                self.boundary = WaveBoundary::Reception;
                Ok(Some(cycle))
            }
            WaveBoundary::Reception => {
                let pending = self
                    .pending
                    .as_ref()
                    .ok_or_else(|| invalid("missing pending current"))?;
                let next = session.receive(&pending.current, Some(pending.source))?;
                self.step = next;
                self.pending = None;
                self.cycle += 1;
                self.intervention_cursor = 0;
                self.select_next_boundary();
                Ok(None)
            }
        }
    }
    pub fn checkpoint(
        &self,
        session: &NativeSession<'_>,
        path: impl AsRef<Path>,
    ) -> Result<PublicationReceipt<()>, NativeSessionError> {
        self.validate()?;
        self.validate_session(session)?;
        session.checkpoint_application(path, &HnaStreamState::default(), &serde_json::to_vec(self)?)
    }
}

pub struct WaveSavedApplication {
    native: NativeSavedSession,
    application: WaveApplication,
}
impl WaveSavedApplication {
    pub fn read(path: impl AsRef<Path>) -> Result<Self, NativeSessionError> {
        let native = NativeSavedSession::read(path)?;
        let bytes = native
            .application_state()
            .ok_or_else(|| invalid("checkpoint has no wave application state"))?;
        let application: WaveApplication = serde_json::from_slice(bytes)?;
        application.validate()?;
        if native.nodes() != application.spec.model.nodes.len()
            || native.occurrences() != application.cycle + 1
            || native
                .source_slots()
                .get(usize::try_from(application.step.source).map_err(invalid)?)
                != Some(&Some(application.step.native_occurrence))
            || *native.transport() != HnaStreamState::default()
        {
            return Err(invalid(
                "application/native source or delivery boundary differs",
            ));
        }
        Ok(Self {
            native,
            application,
        })
    }
    pub fn application(&self) -> &WaveApplication {
        &self.application
    }
    pub fn with_application<R>(
        self,
        operation: impl FnOnce(
            &mut NativeSession<'_>,
            &mut WaveApplication,
        ) -> Result<R, NativeSessionError>,
    ) -> Result<R, NativeSessionError> {
        let mut application = self.application;
        self.native
            .with_application_session(|session, _stream, _bytes| {
                operation(session, &mut application)
            })
    }
}

fn execute(
    app: &mut WaveApplication,
    session: &mut NativeSession<'_>,
    options: &WaveRunOptions,
) -> Result<WaveControlRun, NativeSessionError> {
    let stop = app
        .cycle
        .saturating_add(options.cycles.unwrap_or(usize::MAX))
        .min(app.spec.cycles);
    let mut cycles = Vec::new();
    let mut interruption = None;
    while app.cycle < stop {
        // Reserve the report slot before enacting the independently owned exterior effect.
        if app.boundary == WaveBoundary::World {
            if let Err(error) = cycles.try_reserve(1) {
                interruption = Some(WaveInterruption {
                    cycle: app.cycle,
                    stage: "report-allocation",
                    detail: error.to_string(),
                });
                break;
            }
        }
        match app.advance_boundary(session) {
            Ok(Some(cycle)) => cycles.push(cycle),
            Ok(None) => {}
            Err(error) => {
                interruption = Some(WaveInterruption {
                    cycle: app.cycle,
                    stage: app.boundary.stage(),
                    detail: error.to_string(),
                });
                break;
            }
        }
    }
    let (persistent, checkpoint_octets, checkpoint_error) = if let Some(path) = &options.checkpoint
    {
        match app.checkpoint(session, path) {
            Ok(receipt) => (true, Some(receipt.bytes), None),
            Err(error) => (false, None, Some(error.to_string())),
        }
    } else {
        (false, None, None)
    };
    Ok(WaveControlRun {
        schema: WAVE_CONTROL_SCHEMA,
        cycles,
        final_native: app.step.clone(),
        anatomy: session.inspect(),
        persistent,
        interruption,
        pending_receive: app.pending.clone(),
        final_world_state: app.world_state.clone(),
        final_unactuated_state: app.unactuated_state.clone(),
        next_cycle: app.cycle,
        boundary: app.boundary,
        complete: app.boundary == WaveBoundary::Complete,
        checkpoint: options.checkpoint.clone(),
        checkpoint_octets,
        checkpoint_error,
    })
}
fn preflight(options: &WaveRunOptions) -> Result<(), NativeSessionError> {
    if let Some(path) = &options.checkpoint {
        if path.exists() {
            return Err(crate::publication::PublicationError::ExistingTarget {
                path: path.clone(),
            }
            .into());
        }
        if let Some(parent) = path.parent().filter(|p| !p.as_os_str().is_empty()) {
            std::fs::create_dir_all(parent)?;
        }
    }
    Ok(())
}
pub fn run_wave_control_with_options(
    spec: &WaveControlSpec,
    options: &WaveRunOptions,
) -> Result<WaveControlRun, NativeSessionError> {
    spec.validate()?;
    preflight(options)?;
    with_native_session(&spec.model, |session| {
        let mut app = WaveApplication::found(spec, session)?;
        execute(&mut app, session, options)
    })
}
pub fn resume_wave_control(
    path: impl AsRef<Path>,
    options: &WaveRunOptions,
) -> Result<WaveControlRun, NativeSessionError> {
    preflight(options)?;
    WaveSavedApplication::read(path)?
        .with_application(|session, app| execute(app, session, options))
}

#[cfg(test)]
mod tests;
