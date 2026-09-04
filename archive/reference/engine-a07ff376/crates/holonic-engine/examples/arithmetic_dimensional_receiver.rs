//! Interactive exact dimensional receiver over the production counting ecology.
//!
//! This is a display conductor, not a second arithmetic or wave law.
//! Consecutive integer occurrences first condition `ArithmeticFiberLaw`; the
//! resulting exact standing mounts through `ArithmeticDimensionalMount`.
//! Prime-power occurrences then cause simultaneous finite-place currents in
//! `ExactDimensionalWaveLaw`. X11 receives only exact dimensional and wave
//! slice receipts.

use std::collections::BTreeMap;
use std::error::Error;
use std::fs::{File, create_dir_all, write};
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::thread;
use std::time::{Duration, Instant};

use holonic_engine::{
    ARITHMETIC_COUNT_AXIS, ARITHMETIC_RECOGNITION_DEPTH_AXIS, ARITHMETIC_SUPPORT_GRADE_AXIS,
    ARITHMETIC_VALUATION_MASS_AXIS, ArithmeticDimensionalMount, ArithmeticFiberEvent,
    ArithmeticFiberLaw, ArithmeticFiberStanding, CausalWorld, DimensionalGermDisposition,
    DimensionalReceiverAtlas, DimensionalReceiverDeed, DimensionalReceiverFounding,
    DimensionalReceiverRequest, DimensionalSliceReceipt, DimensionalWaveEvent,
    DimensionalWaveSectionDisposition, DimensionalWaveSliceReceipt, DisplayFace, EventId,
    ExactDimensionalWaveLaw, ExactReceiverPhasePopulation, ExactReceiverPrimaryDoctrine,
    ExactSliceConstraint, ExactSliceCovector, PlatformMembrane, RawPlatformInput, Rgb8,
    VisibleDimensionalWaveSection, X11Platform, encode_ppm, exact_residue_conic_phase,
};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};
use relational_geometry::{Rat, ReceiverId};

const RECEIVER: ReceiverId = ReceiverId(71);
const DEFAULT_LIMIT: u64 = 512;
const DEFAULT_WAVE_THROUGH: u64 = 128;
const DEFAULT_WIDTH: u32 = 1_100;
const DEFAULT_HEIGHT: u32 = 720;
const WAVE_CARRIER_DELAY: u32 = 4;
const WAVE_EVENT_BASE: u64 = 10_000_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ViewKind {
    PhaseProduct,
    CountDepth,
    CountValuation,
    CountGrade,
}

impl ViewKind {
    fn next(self, hand: i8) -> Self {
        let ordinal = match self {
            Self::PhaseProduct => 0_i8,
            Self::CountDepth => 1,
            Self::CountValuation => 2,
            Self::CountGrade => 3,
        };
        match (ordinal + hand).rem_euclid(4) {
            0 => Self::PhaseProduct,
            1 => Self::CountDepth,
            2 => Self::CountValuation,
            _ => Self::CountGrade,
        }
    }
}

struct InstrumentControl {
    view: ViewKind,
    pair_cursor: usize,
    gate_enabled: bool,
    gate_cursor: usize,
    gate_residue: u64,
    zoom: Rat,
}

impl InstrumentControl {
    fn initial(mount: &ArithmeticDimensionalMount) -> Self {
        let count = mount.phase_axes.len();
        Self {
            view: ViewKind::PhaseProduct,
            pair_cursor: count.saturating_div(2).saturating_sub(1),
            gate_enabled: false,
            gate_cursor: count.saturating_div(2).saturating_add(2).min(count - 1),
            gate_residue: 0,
            zoom: Rat::one(),
        }
    }

    fn primes(&self, mount: &ArithmeticDimensionalMount) -> Vec<u64> {
        mount.phase_axes.keys().copied().collect()
    }

    fn phase_pair(&self, mount: &ArithmeticDimensionalMount) -> (u64, u64) {
        let primes = self.primes(mount);
        let first = self.pair_cursor.min(primes.len() - 2);
        (primes[first], primes[first + 1])
    }

    fn gate(&self, mount: &ArithmeticDimensionalMount) -> Option<(u64, u64)> {
        if !self.gate_enabled {
            return None;
        }
        let primes = self.primes(mount);
        let prime = primes[self.gate_cursor.min(primes.len() - 1)];
        Some((prime, self.gate_residue % prime))
    }

    fn constraints(
        &self,
        mount: &ArithmeticDimensionalMount,
    ) -> Result<Vec<ExactSliceConstraint>, Box<dyn Error>> {
        let Some((prime, residue)) = self.gate(mount) else {
            return Ok(Vec::new());
        };
        let pair = mount.phase_axes[&prime];
        let (real, imaginary) = exact_residue_conic_phase(residue, prime)?;
        Ok(vec![
            ExactSliceConstraint {
                covector: ExactSliceCovector::axis(pair.real),
                center: real,
                radius: Rat::zero(),
            },
            ExactSliceConstraint {
                covector: ExactSliceCovector::axis(pair.imaginary),
                center: imaginary,
                radius: Rat::zero(),
            },
        ])
    }

    fn founding(
        &self,
        mount: &ArithmeticDimensionalMount,
    ) -> Result<DimensionalReceiverFounding, Box<dyn Error>> {
        let constraints = self.constraints(mount)?;
        let through = integer_rat(mount.through);
        let count_center = (&through + integer_rat(2)) / integer_rat(2);
        let count_span = ((&through - integer_rat(2)) / integer_rat(2)).max(Rat::one());
        let maximum_depth = mount
            .occurrences
            .values()
            .map(|occurrence| occurrence.recognition_depth)
            .max()
            .unwrap_or(1)
            .max(1);
        let maximum_valuation = mount
            .occurrences
            .values()
            .map(|occurrence| {
                occurrence
                    .valuation
                    .iter()
                    .map(|factor| u64::from(factor.exponent))
                    .sum::<u64>()
            })
            .max()
            .unwrap_or(1)
            .max(1);
        let maximum_grade = mount
            .occurrences
            .values()
            .map(|occurrence| occurrence.squarefree_support.len().saturating_sub(1))
            .max()
            .unwrap_or(1)
            .max(1);
        let result = match self.view {
            ViewKind::PhaseProduct => {
                let (first_prime, second_prime) = self.phase_pair(mount);
                let first = mount.phase_axes[&first_prime];
                let second = mount.phase_axes[&second_prime];
                // Two exact conic factors, with small exact chronology and
                // recognition currents. The drift unfolds recurrent visits
                // without identifying their common torus address.
                let count_drift = Rat::new(BigInt::one(), BigInt::from(4 * mount.through));
                let depth_drift = Rat::new(BigInt::one(), BigInt::from(4 * maximum_depth.max(1)));
                let third = Rat::new(BigInt::one(), BigInt::from(3));
                DimensionalReceiverFounding {
                    horizontal: ExactSliceCovector::new(BTreeMap::from([
                        (first.real, Rat::one()),
                        (second.real, third.clone()),
                        (ARITHMETIC_COUNT_AXIS, count_drift),
                    ]))?,
                    vertical: ExactSliceCovector::new(BTreeMap::from([
                        (first.imaginary, Rat::one()),
                        (second.imaginary, third),
                        (ARITHMETIC_RECOGNITION_DEPTH_AXIS, depth_drift),
                    ]))?,
                    depth: Some(ExactSliceCovector::axis(ARITHMETIC_COUNT_AXIS)),
                    horizontal_center: Rat::new(BigInt::one(), BigInt::from(8)),
                    vertical_center: Rat::new(BigInt::one(), BigInt::from(8)),
                    horizontal_span: &self.zoom * Rat::new(BigInt::from(3), BigInt::from(2)),
                    vertical_span: &self.zoom * Rat::new(BigInt::from(3), BigInt::from(2)),
                    constraints,
                    causal_horizon: None,
                    active_front: None,
                }
            }
            ViewKind::CountDepth => DimensionalReceiverFounding {
                horizontal: ExactSliceCovector::axis(ARITHMETIC_COUNT_AXIS),
                vertical: ExactSliceCovector::axis(ARITHMETIC_RECOGNITION_DEPTH_AXIS),
                depth: Some(ExactSliceCovector::axis(ARITHMETIC_SUPPORT_GRADE_AXIS)),
                horizontal_center: count_center,
                vertical_center: integer_rat(maximum_depth) / integer_rat(2),
                horizontal_span: &self.zoom * count_span,
                vertical_span: &self.zoom
                    * (integer_rat(maximum_depth) / integer_rat(2)).max(Rat::one()),
                constraints,
                causal_horizon: None,
                active_front: None,
            },
            ViewKind::CountValuation => DimensionalReceiverFounding {
                horizontal: ExactSliceCovector::axis(ARITHMETIC_COUNT_AXIS),
                vertical: ExactSliceCovector::axis(ARITHMETIC_VALUATION_MASS_AXIS),
                depth: Some(ExactSliceCovector::axis(ARITHMETIC_RECOGNITION_DEPTH_AXIS)),
                horizontal_center: count_center,
                vertical_center: integer_rat(maximum_valuation) / integer_rat(2),
                horizontal_span: &self.zoom * count_span,
                vertical_span: &self.zoom
                    * (integer_rat(maximum_valuation) / integer_rat(2)).max(Rat::one()),
                constraints,
                causal_horizon: None,
                active_front: None,
            },
            ViewKind::CountGrade => DimensionalReceiverFounding {
                horizontal: ExactSliceCovector::axis(ARITHMETIC_COUNT_AXIS),
                vertical: ExactSliceCovector::axis(ARITHMETIC_SUPPORT_GRADE_AXIS),
                depth: Some(ExactSliceCovector::axis(ARITHMETIC_VALUATION_MASS_AXIS)),
                horizontal_center: count_center,
                vertical_center: integer_rat(
                    u64::try_from(maximum_grade).expect("bounded arithmetic grade"),
                ) / integer_rat(2),
                horizontal_span: &self.zoom * count_span,
                vertical_span: &self.zoom
                    * (integer_rat(
                        u64::try_from(maximum_grade).expect("bounded arithmetic grade"),
                    ) / integer_rat(2))
                    .max(Rat::one()),
                constraints,
                causal_horizon: None,
                active_front: None,
            },
        };
        Ok(result)
    }

    fn description(&self, mount: &ArithmeticDimensionalMount) -> String {
        let view = match self.view {
            ViewKind::PhaseProduct => {
                let (first, second) = self.phase_pair(mount);
                format!("phase-product({first},{second}) + exact chronology/depth current")
            }
            ViewKind::CountDepth => "count × recognition-depth".to_owned(),
            ViewKind::CountValuation => "count × valuation-mass".to_owned(),
            ViewKind::CountGrade => "count × squarefree-grade".to_owned(),
        };
        let gate = self.gate(mount).map_or_else(
            || "no finite-place section".to_owned(),
            |(prime, residue)| format!("section n mod {prime} = {residue}"),
        );
        format!("{view}; {gate}; dilation={}", self.zoom)
    }
}

struct PropagationClock {
    next_event: u64,
    running: bool,
    interval: Duration,
    last_step: Instant,
}

impl PropagationClock {
    fn new(next_event: u64) -> Self {
        Self {
            next_event,
            running: true,
            interval: Duration::from_millis(70),
            last_step: Instant::now(),
        }
    }

    fn event(&mut self) -> Result<DimensionalWaveEvent, Box<dyn Error>> {
        let event = EventId(self.next_event);
        self.next_event = self
            .next_event
            .checked_add(1)
            .ok_or("wave event identity overflow")?;
        self.last_step = Instant::now();
        Ok(DimensionalWaveEvent {
            event,
            impulses: Vec::new(),
        })
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let limit = std::env::args()
        .nth(1)
        .map_or(Ok(DEFAULT_LIMIT), |value| value.parse::<u64>())?;
    if limit < 16 {
        return Err("the dimensional counting receiver requires a limit of at least 16".into());
    }
    let wave_through = std::env::var("HOLONIC_WAVE_THROUGH")
        .map_or(Ok(DEFAULT_WAVE_THROUGH.min(limit)), |value| {
            value.parse::<u64>()
        })?;
    if !(4..=limit).contains(&wave_through) {
        return Err("HOLONIC_WAVE_THROUGH must lie within 4..=source limit".into());
    }
    let mut arithmetic = CausalWorld::new(ArithmeticFiberLaw, ArithmeticFiberStanding::default());
    for value in 2..=limit {
        arithmetic.receive(&ArithmeticFiberEvent {
            event: EventId(value - 1),
            value,
        })?;
    }
    let mount = ArithmeticDimensionalMount::mount(arithmetic.standing())?;
    if mount.phase_axes.len() < 3 {
        return Err("the counting horizon did not found enough residue phase axes".into());
    }
    let wave_law = mount.exact_phase_wave_law_through(WAVE_CARRIER_DELAY, wave_through)?;
    let mut wave_world = conditioned_wave_world(&mount, &wave_law, wave_through)?;
    let mut control = InstrumentControl::initial(&mount);
    let headless = std::env::var_os("HOLONIC_SLICE_HEADLESS").is_some();
    let mut atlas = DimensionalReceiverAtlas::new(mount.source.clone())?;
    let mut next_event = limit
        .checked_add(10_000)
        .ok_or("receiver event identity overflow")?;
    let mut chronology = 1_u64;
    let initial = atlas.receive(&DimensionalReceiverRequest {
        event: EventId(next_event),
        chronology,
        receiver: RECEIVER,
        deed: DimensionalReceiverDeed::Found(control.founding(&mount)?),
    })?;
    let mut receipt = initial.receipt;
    let mut wave_receipt = wave_law.restrict(wave_world.standing(), &receipt)?;
    let mut width = DEFAULT_WIDTH;
    let mut height = DEFAULT_HEIGHT;
    let mut face = render_slice(&mount, &receipt, &wave_receipt, width, height)?;
    let output = PathBuf::from("output/arithmetic-dimensional-receiver");
    write_snapshot(&output, &mount, &control, &receipt, &wave_receipt, &face)?;
    report(
        &mount,
        wave_through,
        &control,
        &receipt,
        &wave_receipt,
        &output,
    );

    if headless {
        if std::env::var_os("HOLONIC_SLICE_SWEEP").is_some() {
            let sweep_directory = std::env::var_os("HOLONIC_SLICE_SWEEP_DIRECTORY")
                .map(PathBuf::from)
                .unwrap_or_else(|| output.join("parameter-atlas"));
            write_parameter_sweep(&sweep_directory, &mount, width, height)?;
        }
        return Ok(());
    }

    let next_wave_event = WAVE_EVENT_BASE
        .checked_add(wave_through)
        .and_then(|event| event.checked_add(1))
        .ok_or("wave event identity overflow")?;
    let mut propagation = PropagationClock::new(next_wave_event);
    let mut platform = X11Platform::new(
        width,
        height,
        "Holonic counting ecology — exact propagating dimensional receiver",
    )?;
    platform.present(&face)?;
    loop {
        while let Some(input) = platform.next_input()? {
            let mut deed = None;
            match input {
                RawPlatformInput::CloseRequested
                | RawPlatformInput::Key {
                    physical_code: 9,
                    pressed: true,
                    ..
                } => return Ok(()),
                RawPlatformInput::Key {
                    physical_code,
                    pressed: true,
                    ..
                } if matches!(physical_code, 25 | 39) => {
                    control.view = control.view.next(if physical_code == 25 { -1 } else { 1 });
                    deed = Some(DimensionalReceiverDeed::Reframe(control.founding(&mount)?));
                }
                RawPlatformInput::Key {
                    physical_code,
                    pressed: true,
                    ..
                } if matches!(physical_code, 113 | 114) => {
                    let count = mount.phase_axes.len();
                    control.pair_cursor = if physical_code == 113 {
                        control.pair_cursor.saturating_sub(1)
                    } else {
                        (control.pair_cursor + 1).min(count - 2)
                    };
                    deed = Some(DimensionalReceiverDeed::Reframe(control.founding(&mount)?));
                }
                RawPlatformInput::Key {
                    physical_code,
                    pressed: true,
                    ..
                } if matches!(physical_code, 111 | 116) => {
                    let (prime, _) = control.phase_pair(&mount);
                    let pair = mount.phase_axes[&prime];
                    deed = Some(DimensionalReceiverDeed::Turn {
                        first: pair.real,
                        second: pair.imaginary,
                        ratio: Rat::new(
                            BigInt::from(if physical_code == 111 { -1 } else { 1 }),
                            BigInt::from(16),
                        ),
                    });
                }
                RawPlatformInput::Key {
                    physical_code,
                    pressed: true,
                    ..
                } if matches!(physical_code, 38 | 40) => {
                    control.gate_enabled = true;
                    let primes = control.primes(&mount);
                    let gate_prime = primes[control.gate_cursor.min(primes.len() - 1)];
                    control.gate_residue = if physical_code == 38 {
                        control
                            .gate_residue
                            .checked_add(gate_prime)
                            .and_then(|value| value.checked_sub(1))
                            .ok_or("gate residue overflow")?
                            % gate_prime
                    } else {
                        (control.gate_residue + 1) % gate_prime
                    };
                    deed = Some(DimensionalReceiverDeed::Reframe(control.founding(&mount)?));
                }
                RawPlatformInput::Key {
                    physical_code: 65,
                    pressed: true,
                    ..
                } => {
                    control.gate_enabled = !control.gate_enabled;
                    deed = Some(DimensionalReceiverDeed::Reframe(control.founding(&mount)?));
                }
                RawPlatformInput::Key {
                    physical_code,
                    pressed: true,
                    ..
                } if matches!(physical_code, 52 | 53) => {
                    control.zoom *= if physical_code == 52 {
                        Rat::new(BigInt::from(4), BigInt::from(5))
                    } else {
                        Rat::new(BigInt::from(5), BigInt::from(4))
                    };
                    deed = Some(DimensionalReceiverDeed::Reframe(control.founding(&mount)?));
                }
                RawPlatformInput::Key {
                    physical_code: 33,
                    pressed: true,
                    ..
                } => {
                    propagation.running = !propagation.running;
                    propagation.last_step = Instant::now();
                    println!(
                        "exact wave propagation={} at tick {} with energy {}",
                        if propagation.running {
                            "running"
                        } else {
                            "paused"
                        },
                        wave_world.standing().tick,
                        wave_world.standing().energy,
                    );
                }
                RawPlatformInput::Key {
                    physical_code: 57,
                    pressed: true,
                    ..
                } => {
                    propagation.running = false;
                    let event = propagation.event()?;
                    let transition = wave_world.receive(&event)?;
                    let current = &transition.radiation[0];
                    if !current.exact_energy_residual.is_zero() {
                        return Err("wave event did not conserve exact energy".into());
                    }
                    wave_receipt = wave_law.restrict(wave_world.standing(), &receipt)?;
                    face = render_slice(&mount, &receipt, &wave_receipt, width, height)?;
                    platform.present(&face)?;
                }
                RawPlatformInput::Key {
                    physical_code: 26,
                    pressed: true,
                    ..
                } => {
                    let mut impulses = Vec::new();
                    for value in 2..=wave_through {
                        impulses.extend(mount.phase_wave_impulses(wave_world.law(), value)?);
                    }
                    let mut event = propagation.event()?;
                    event.impulses = impulses;
                    let transition = wave_world.receive(&event)?;
                    println!(
                        "re-emitted {} caused prime-power populations; exact source work={}",
                        event.impulses.len(),
                        transition.radiation[0].source_work,
                    );
                    wave_receipt = wave_law.restrict(wave_world.standing(), &receipt)?;
                    face = render_slice(&mount, &receipt, &wave_receipt, width, height)?;
                    platform.present(&face)?;
                }
                RawPlatformInput::Key {
                    physical_code: 43,
                    pressed: true,
                    ..
                } => {
                    write_snapshot(&output, &mount, &control, &receipt, &wave_receipt, &face)?;
                    report(
                        &mount,
                        wave_through,
                        &control,
                        &receipt,
                        &wave_receipt,
                        &output,
                    );
                }
                RawPlatformInput::Key {
                    physical_code: 27,
                    pressed: true,
                    ..
                } => {
                    control = InstrumentControl::initial(&mount);
                    wave_world = conditioned_wave_world(&mount, &wave_law, wave_through)?;
                    propagation = PropagationClock::new(next_wave_event);
                    deed = Some(DimensionalReceiverDeed::Reframe(control.founding(&mount)?));
                }
                RawPlatformInput::PointerButton {
                    at,
                    button: 1,
                    pressed: true,
                } => inspect_address(&mount, &receipt, at.column, at.row, width, height),
                RawPlatformInput::Resize {
                    width: next_width,
                    height: next_height,
                } if next_width > 0 && next_height > 0 => {
                    width = next_width;
                    height = next_height;
                    face = render_slice(&mount, &receipt, &wave_receipt, width, height)?;
                    platform.present(&face)?;
                }
                RawPlatformInput::RedrawRequested => platform.present(&face)?,
                _ => {}
            }
            if let Some(deed) = deed {
                next_event = next_event
                    .checked_add(1)
                    .ok_or("receiver event identity overflow")?;
                chronology = chronology
                    .checked_add(1)
                    .ok_or("receiver chronology overflow")?;
                receipt = atlas
                    .receive(&DimensionalReceiverRequest {
                        event: EventId(next_event),
                        chronology,
                        receiver: RECEIVER,
                        deed,
                    })?
                    .receipt;
                wave_receipt = wave_law.restrict(wave_world.standing(), &receipt)?;
                face = render_slice(&mount, &receipt, &wave_receipt, width, height)?;
                platform.present(&face)?;
            }
        }
        if propagation.running && propagation.last_step.elapsed() >= propagation.interval {
            let transition = wave_world.receive(&propagation.event()?)?;
            if !transition.radiation[0].exact_energy_residual.is_zero()
                || !transition.radiation[0].source_work.is_zero()
            {
                return Err("unforced propagation changed exact wave energy".into());
            }
            wave_receipt = wave_law.restrict(wave_world.standing(), &receipt)?;
            face = render_slice(&mount, &receipt, &wave_receipt, width, height)?;
            platform.present(&face)?;
        }
        thread::sleep(Duration::from_millis(3));
    }
}

fn conditioned_wave_world(
    mount: &ArithmeticDimensionalMount,
    law: &ExactDimensionalWaveLaw,
    through: u64,
) -> Result<CausalWorld<ExactDimensionalWaveLaw>, Box<dyn Error>> {
    let mut world = CausalWorld::new(law.clone(), law.initial_standing());
    for value in 2..=through {
        let impulses = mount.phase_wave_impulses(world.law(), value)?;
        let transition = world.receive(&DimensionalWaveEvent {
            event: EventId(
                WAVE_EVENT_BASE
                    .checked_add(value)
                    .ok_or("wave event identity overflow")?,
            ),
            impulses,
        })?;
        if !transition.radiation[0].exact_energy_residual.is_zero() {
            return Err("prime-power conditioning failed exact wave balance".into());
        }
    }
    Ok(world)
}

fn co_present_spectral_world(
    mount: &ArithmeticDimensionalMount,
    law: &ExactDimensionalWaveLaw,
    propagation_ticks: u64,
) -> Result<CausalWorld<ExactDimensionalWaveLaw>, Box<dyn Error>> {
    let mut world = CausalWorld::new(law.clone(), law.initial_standing());
    let mut impulses = Vec::new();
    for value in 2..=mount.through {
        impulses.extend(mount.phase_wave_impulses(world.law(), value)?);
    }
    let transition = world.receive(&DimensionalWaveEvent {
        event: EventId(62_000_000),
        impulses,
    })?;
    if !transition.radiation[0].exact_energy_residual.is_zero() {
        return Err("co-present prime-power spectrum failed exact energy balance".into());
    }
    for tick in 1..=propagation_ticks {
        let transition = world.receive(&DimensionalWaveEvent {
            event: EventId(
                62_000_000_u64
                    .checked_add(tick)
                    .ok_or("spectral event identity overflow")?,
            ),
            impulses: Vec::new(),
        })?;
        if !transition.radiation[0].source_work.is_zero()
            || !transition.radiation[0].exact_energy_residual.is_zero()
        {
            return Err("co-present spectrum propagation changed exact energy".into());
        }
    }
    law.validate_standing(world.standing())?;
    Ok(world)
}

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
struct TerminalPhaseContact {
    support_multiplicity: BigUint,
    wave_sections: Vec<usize>,
}

struct TerminalPhaseMembrane {
    width: u32,
    height: u32,
    contacts: Vec<Option<TerminalPhaseContact>>,
}

impl TerminalPhaseMembrane {
    fn new(width: u32, height: u32) -> Result<Self, Box<dyn Error>> {
        let extent = usize::try_from(
            u64::from(width)
                .checked_mul(u64::from(height))
                .ok_or("display carrier overflow")?,
        )?;
        Ok(Self {
            width,
            height,
            contacts: vec![None; extent],
        })
    }

    fn address(&self, x: i32, y: i32) -> Option<usize> {
        let (Ok(x), Ok(y)) = (u32::try_from(x), u32::try_from(y)) else {
            return None;
        };
        if x >= self.width || y >= self.height {
            return None;
        }
        usize::try_from(u64::from(y) * u64::from(self.width) + u64::from(x)).ok()
    }

    fn contact_mut(&mut self, x: i32, y: i32) -> Option<&mut TerminalPhaseContact> {
        let address = self.address(x, y)?;
        Some(self.contacts[address].get_or_insert_with(Default::default))
    }

    fn receive_support(&mut self, x: i32, y: i32) {
        if let Some(contact) = self.contact_mut(x, y) {
            contact.support_multiplicity += BigUint::from(1_u8);
        }
    }

    fn receive_current(&mut self, x: i32, y: i32, section: usize) {
        if let Some(contact) = self.contact_mut(x, y) {
            contact.wave_sections.push(section);
        }
    }

    fn transduce(
        self,
        doctrine: &ExactReceiverPrimaryDoctrine,
        wave: &DimensionalWaveSliceReceipt,
    ) -> Result<DisplayFace, Box<dyn Error>> {
        let mut cache = BTreeMap::<TerminalPhaseContact, Rgb8>::new();
        let pixels = self
            .contacts
            .into_iter()
            .map(|contact| {
                let Some(contact) = contact else {
                    return Ok(Rgb8 {
                        red: 0,
                        green: 0,
                        blue: 0,
                    });
                };
                if let Some(color) = cache.get(&contact) {
                    return Ok(*color);
                }
                let mut population = ExactReceiverPhasePopulation::default();
                population.add_support(contact.support_multiplicity.clone());
                for section in &contact.wave_sections {
                    let section = wave
                        .sections
                        .get(*section)
                        .ok_or("terminal contact names an absent exact wave section")?;
                    population.receive(section.mode, &section.current);
                }
                let response = doctrine.transduce(&population);
                let color = Rgb8 {
                    red: quantize_unit(&response.primaries[0]),
                    green: quantize_unit(&response.primaries[1]),
                    blue: quantize_unit(&response.primaries[2]),
                };
                cache.insert(contact, color);
                Ok(color)
            })
            .collect::<Result<Vec<_>, Box<dyn Error>>>()?;
        Ok(DisplayFace {
            schema: "holonic-engine.arithmetic-dimensional-display.v2".to_owned(),
            width: self.width,
            height: self.height,
            pixels,
        })
    }
}

fn receiver_primary_doctrine(
    receipt: &DimensionalSliceReceipt,
    wave: &DimensionalWaveSliceReceipt,
) -> Result<ExactReceiverPrimaryDoctrine, Box<dyn Error>> {
    let visible_sections = wave
        .mode_measures
        .iter()
        .map(|mode| mode.visible_sections)
        .sum::<usize>();
    let mean_visible_energy = if visible_sections == 0 {
        Rat::zero()
    } else {
        &wave.total_energy / Rat::from_integer(BigInt::from(u64::try_from(visible_sections)?))
    };
    let aperture = Rat::one() + mean_visible_energy;
    let support_denominator = u64::from(receipt.received_source_dimension.unwrap_or(0))
        .checked_add(2)
        .ok_or("receiver support response overflow")?;
    let support_response = &aperture / integer_rat(support_denominator);
    Ok(ExactReceiverPrimaryDoctrine::new(
        aperture,
        support_response,
    )?)
}

fn render_slice(
    _mount: &ArithmeticDimensionalMount,
    receipt: &DimensionalSliceReceipt,
    wave: &DimensionalWaveSliceReceipt,
    width: u32,
    height: u32,
) -> Result<DisplayFace, Box<dyn Error>> {
    if wave.receiver != receipt.receiver
        || wave.receiver_event != receipt.event
        || wave.receiver_chronology != receipt.chronology
    {
        return Err("the wave receiver receipt differs from the dimensional receiver".into());
    }
    let mut membrane = TerminalPhaseMembrane::new(width, height)?;
    let doctrine = receiver_primary_doctrine(receipt, wave)?;
    let mut positions = BTreeMap::new();
    for (germ, body) in &receipt.germs {
        if let DimensionalGermDisposition::Visible {
            normalized_horizontal,
            normalized_vertical,
            ..
        } = &body.disposition
        {
            if let Some(position) =
                terminal_position(normalized_horizontal, normalized_vertical, width, height)?
            {
                positions.insert(*germ, position);
            }
        }
    }

    // Coordinate zero is receiver testimony, not an absolute world origin.
    if let Some((center_x, _)) = terminal_position(&Rat::zero(), &Rat::zero(), width, height)? {
        draw_support_line(
            &mut membrane,
            center_x,
            0,
            center_x,
            i32::try_from(height.saturating_sub(1))?,
        );
    }
    if let Some((_, center_y)) = terminal_position(&Rat::zero(), &Rat::zero(), width, height)? {
        draw_support_line(
            &mut membrane,
            0,
            center_y,
            i32::try_from(width.saturating_sub(1))?,
            center_y,
        );
    }

    // Draw only source-declared carriers. Screen proximity creates no edge.
    for carrier_receipt in receipt.carriers.values() {
        if !matches!(
            carrier_receipt.disposition,
            holonic_engine::DimensionalCarrierDisposition::Visible
        ) {
            continue;
        }
        let (Some(from), Some(to)) = (
            positions.get(&carrier_receipt.from),
            positions.get(&carrier_receipt.to),
        ) else {
            continue;
        };
        draw_support_line(&mut membrane, from.0, from.1, to.0, to.1);
    }

    // A traveling section is an exact causal phase on one declared source
    // 1-cell. The affine subsegment below is only the monitor's quotient of
    // that `(elapsed, delay)` ratio; it neither updates source standing nor
    // asserts that projected chord length is the carrier's intrinsic metric.
    for (section_ordinal, section) in wave.sections.iter().enumerate() {
        let DimensionalWaveSectionDisposition::Visible(visible) = &section.disposition else {
            continue;
        };
        let VisibleDimensionalWaveSection {
            from_horizontal,
            from_vertical,
            to_horizontal,
            to_vertical,
            elapsed,
            delay,
            ..
        } = visible.as_ref();
        let start_phase = Rat::new(BigInt::from(*elapsed), BigInt::from(*delay));
        let end_phase = Rat::new(
            BigInt::from(elapsed.saturating_add(1).min(*delay)),
            BigInt::from(*delay),
        );
        let point = |phase: &Rat| {
            (
                from_horizontal + (to_horizontal - from_horizontal) * phase,
                from_vertical + (to_vertical - from_vertical) * phase,
            )
        };
        let (start_horizontal, start_vertical) = point(&start_phase);
        let (end_horizontal, end_vertical) = point(&end_phase);
        let (Some(start), Some(end)) = (
            terminal_position(&start_horizontal, &start_vertical, width, height)?,
            terminal_position(&end_horizontal, &end_vertical, width, height)?,
        ) else {
            continue;
        };
        draw_phase_current(
            &mut membrane,
            start.0,
            start.1,
            end.0,
            end.1,
            section_ordinal,
        );
    }

    for (germ, position) in &positions {
        let grade = receipt.germs[germ].source_grade;
        if grade == 0 {
            draw_support_circle(&mut membrane, position.0, position.1, 2);
        } else {
            draw_support_diamond(
                &mut membrane,
                position.0,
                position.1,
                2 + i32::try_from(grade.min(3))?,
            );
        }
    }

    // A collision is a plural receiver fiber. Concentric terminal rings mark
    // multiplicity without spatially separating or identifying its members.
    for bucket in &receipt.projection_buckets {
        if bucket.members.len() < 2 {
            continue;
        }
        let Some((x, y)) = terminal_position(
            &bucket.normalized_horizontal,
            &bucket.normalized_vertical,
            width,
            height,
        )?
        else {
            continue;
        };
        let radius = 3 + i32::try_from(bucket.members.len().min(11))?;
        draw_support_circle(&mut membrane, x, y, radius);
    }
    draw_support_border(&mut membrane);
    membrane.transduce(&doctrine, wave)
}

fn terminal_position(
    horizontal: &Rat,
    vertical: &Rat,
    width: u32,
    height: u32,
) -> Result<Option<(i32, i32)>, Box<dyn Error>> {
    if horizontal.abs() > Rat::one() || vertical.abs() > Rat::one() {
        return Ok(None);
    }
    let horizontal_scale = BigInt::from(width.saturating_sub(1));
    let vertical_scale = BigInt::from(height.saturating_sub(1));
    let x = ((horizontal + Rat::one()) * Rat::from_integer(horizontal_scale) / integer_rat(2))
        .to_integer()
        .to_i32()
        .ok_or("terminal horizontal coordinate overflow")?;
    let y = ((Rat::one() - vertical) * Rat::from_integer(vertical_scale) / integer_rat(2))
        .to_integer()
        .to_i32()
        .ok_or("terminal vertical coordinate overflow")?;
    Ok(Some((x, y)))
}

fn inspect_address(
    mount: &ArithmeticDimensionalMount,
    receipt: &DimensionalSliceReceipt,
    column: u32,
    row: u32,
    width: u32,
    height: u32,
) {
    let target_horizontal =
        integer_rat(2) * Rat::new(column.into(), width.max(2).into()) - Rat::one();
    let target_vertical = Rat::one() - integer_rat(2) * Rat::new(row.into(), height.max(2).into());
    let selected = receipt.projection_buckets.iter().min_by_key(|bucket| {
        let horizontal = &bucket.normalized_horizontal - &target_horizontal;
        let vertical = &bucket.normalized_vertical - &target_vertical;
        &horizontal * &horizontal + &vertical * &vertical
    });
    let Some(bucket) = selected else {
        println!("inspection: receiver section has no visible germ");
        return;
    };
    let values = bucket
        .members
        .iter()
        .map(|germ| {
            let occurrence = &mount.occurrences[&germ.0];
            format!(
                "{}:{}:support={:?}:depth={}:rank={}",
                occurrence.value,
                if occurrence.irreducible {
                    "prime"
                } else if occurrence.prime_power {
                    "prime-power"
                } else {
                    "composite"
                },
                occurrence.squarefree_support,
                occurrence.recognition_depth,
                receipt.germs[germ].local_dimension,
            )
        })
        .collect::<Vec<_>>();
    println!(
        "inspection screen=({column},{row}) exact-address=({},{}) fiber-population={} members=[{}]",
        bucket.normalized_horizontal,
        bucket.normalized_vertical,
        bucket.members.len(),
        values.join("; "),
    );
}

fn write_parameter_sweep(
    directory: &Path,
    mount: &ArithmeticDimensionalMount,
    width: u32,
    height: u32,
) -> Result<(), Box<dyn Error>> {
    create_dir_all(directory)?;
    // The controlled RH/Zeta atlas receives every caused prime-power
    // occurrence co-presently, then lets the exact field conduct for two
    // carrier delays. This is a spectral receiver experiment, distinct from
    // the interactive chronological conditioning above.
    let spectral_law = mount.exact_phase_wave_law_through(WAVE_CARRIER_DELAY, mount.through)?;
    let spectral_world = co_present_spectral_world(mount, &spectral_law, 8)?;
    let law = &spectral_law;
    let standing = spectral_world.standing();
    let phase_count = mount.phase_axes.len();
    let middle = phase_count.saturating_div(2).saturating_sub(1);
    let right = phase_count.saturating_sub(2);
    let mut states = vec![
        ("phase-left", ViewKind::PhaseProduct, 0, 0_i32, Rat::one()),
        (
            "phase-left-cayley-positive",
            ViewKind::PhaseProduct,
            0,
            4,
            Rat::one(),
        ),
        (
            "phase-left-cayley-negative",
            ViewKind::PhaseProduct,
            0,
            -4,
            Rat::one(),
        ),
        (
            "phase-middle",
            ViewKind::PhaseProduct,
            middle,
            0,
            Rat::one(),
        ),
        (
            "phase-middle-cayley",
            ViewKind::PhaseProduct,
            middle,
            4,
            Rat::one(),
        ),
        (
            "phase-middle-dilated",
            ViewKind::PhaseProduct,
            middle,
            4,
            Rat::new(BigInt::from(25), BigInt::from(16)),
        ),
        ("phase-right", ViewKind::PhaseProduct, right, 0, Rat::one()),
        (
            "phase-right-cayley",
            ViewKind::PhaseProduct,
            right,
            4,
            Rat::one(),
        ),
        ("count-depth", ViewKind::CountDepth, middle, 0, Rat::one()),
        (
            "count-valuation",
            ViewKind::CountValuation,
            middle,
            0,
            Rat::one(),
        ),
        ("count-grade", ViewKind::CountGrade, middle, 0, Rat::one()),
    ];
    if std::env::var_os("HOLONIC_MORPHOLOGY_SWEEP").is_some() {
        states = vec![
            (
                "pair-02-03-dilation-25-16",
                ViewKind::PhaseProduct,
                0,
                0,
                Rat::new(BigInt::from(25), BigInt::from(16)),
            ),
            (
                "pair-03-05-dilation-25-16",
                ViewKind::PhaseProduct,
                1,
                0,
                Rat::new(BigInt::from(25), BigInt::from(16)),
            ),
            (
                "pair-05-07-dilation-25-16",
                ViewKind::PhaseProduct,
                2,
                0,
                Rat::new(BigInt::from(25), BigInt::from(16)),
            ),
            (
                "pair-07-11-dilation-25-16",
                ViewKind::PhaseProduct,
                middle,
                0,
                Rat::new(BigInt::from(25), BigInt::from(16)),
            ),
            (
                "pair-11-13-dilation-25-16",
                ViewKind::PhaseProduct,
                4,
                0,
                Rat::new(BigInt::from(25), BigInt::from(16)),
            ),
            (
                "pair-13-17-dilation-25-16",
                ViewKind::PhaseProduct,
                5,
                0,
                Rat::new(BigInt::from(25), BigInt::from(16)),
            ),
            (
                "pair-17-19-dilation-25-16",
                ViewKind::PhaseProduct,
                right,
                0,
                Rat::new(BigInt::from(25), BigInt::from(16)),
            ),
            (
                "middle-dilation-1",
                ViewKind::PhaseProduct,
                middle,
                0,
                Rat::one(),
            ),
            (
                "middle-dilation-5-4",
                ViewKind::PhaseProduct,
                middle,
                0,
                Rat::new(BigInt::from(5), BigInt::from(4)),
            ),
            (
                "middle-dilation-125-64",
                ViewKind::PhaseProduct,
                middle,
                0,
                Rat::new(BigInt::from(125), BigInt::from(64)),
            ),
            (
                "middle-dilation-625-256",
                ViewKind::PhaseProduct,
                middle,
                0,
                Rat::new(BigInt::from(625), BigInt::from(256)),
            ),
            (
                "middle-turn-negative-8",
                ViewKind::PhaseProduct,
                middle,
                -8,
                Rat::new(BigInt::from(25), BigInt::from(16)),
            ),
            (
                "middle-turn-negative-4",
                ViewKind::PhaseProduct,
                middle,
                -4,
                Rat::new(BigInt::from(25), BigInt::from(16)),
            ),
            (
                "middle-turn-positive-4",
                ViewKind::PhaseProduct,
                middle,
                4,
                Rat::new(BigInt::from(25), BigInt::from(16)),
            ),
            (
                "middle-turn-positive-8",
                ViewKind::PhaseProduct,
                middle,
                8,
                Rat::new(BigInt::from(25), BigInt::from(16)),
            ),
        ];
    }
    let mut summary = BufWriter::new(File::create(directory.join("atlas-summary.tsv"))?);
    writeln!(
        summary,
        "state\tview\tphase_pair\tcayley_turns\tdilation\tvisible_germs\tcollapsed_buckets\tenvelope_corners\twave_tick\twave_energy\tvisible_wave_sections\tmode_projected_rate_moments"
    )?;
    for (ordinal, (name, view, pair_cursor, turns, zoom)) in states.into_iter().enumerate() {
        let mut control = InstrumentControl::initial(mount);
        control.view = view;
        control.pair_cursor = pair_cursor;
        control.zoom = zoom;
        let mut atlas = DimensionalReceiverAtlas::new(mount.source.clone())?;
        let mut event = 50_000_000_u64
            .checked_add(
                u64::try_from(ordinal)?
                    .checked_mul(100)
                    .ok_or("sweep event identity overflow")?,
            )
            .ok_or("sweep event identity overflow")?;
        let mut chronology = 1_u64;
        let mut receipt = atlas
            .receive(&DimensionalReceiverRequest {
                event: EventId(event),
                chronology,
                receiver: ReceiverId(
                    RECEIVER
                        .0
                        .checked_add(u64::try_from(ordinal)?)
                        .ok_or("sweep receiver identity overflow")?,
                ),
                deed: DimensionalReceiverDeed::Found(control.founding(mount)?),
            })?
            .receipt;
        if turns != 0 {
            let (prime, _) = control.phase_pair(mount);
            let pair = mount.phase_axes[&prime];
            let ratio = Rat::new(
                BigInt::from(if turns.is_negative() { -1 } else { 1 }),
                BigInt::from(16),
            );
            for _ in 0..turns.unsigned_abs() {
                event = event
                    .checked_add(1)
                    .ok_or("sweep event identity overflow")?;
                chronology = chronology
                    .checked_add(1)
                    .ok_or("sweep receiver chronology overflow")?;
                receipt = atlas
                    .receive(&DimensionalReceiverRequest {
                        event: EventId(event),
                        chronology,
                        receiver: receipt.receiver,
                        deed: DimensionalReceiverDeed::Turn {
                            first: pair.real,
                            second: pair.imaginary,
                            ratio: ratio.clone(),
                        },
                    })?
                    .receipt;
            }
        }
        let wave = law.restrict(standing, &receipt)?;
        let face = render_slice(mount, &receipt, &wave, width, height)?;
        write(directory.join(format!("{name}.ppm")), encode_ppm(&face))?;
        let mut trace = BufWriter::new(File::create(directory.join(format!("{name}.tsv")))?);
        writeln!(
            trace,
            "mode\tcarrier\tfrom\tto\treal\timaginary\tenergy\tticks_until_arrival\tdisposition"
        )?;
        for section in &wave.sections {
            writeln!(
                trace,
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                section.mode.0,
                section.carrier.0,
                section.from.0,
                section.to.0,
                section.current.real,
                section.current.imaginary,
                section.energy,
                section.ticks_until_arrival,
                wave_disposition_text(&section.disposition),
            )?;
        }
        trace.flush()?;
        let mut projection = BufWriter::new(File::create(
            directory.join(format!("{name}-projection.tsv")),
        )?);
        writeln!(projection, "horizontal\tvertical\tmembers")?;
        for bucket in &receipt.projection_buckets {
            writeln!(
                projection,
                "{}\t{}\t{}",
                bucket.normalized_horizontal,
                bucket.normalized_vertical,
                bucket
                    .members
                    .iter()
                    .map(|member| member.0.to_string())
                    .collect::<Vec<_>>()
                    .join(","),
            )?;
        }
        projection.flush()?;
        let mut envelope = BufWriter::new(File::create(
            directory.join(format!("{name}-envelope.tsv")),
        )?);
        writeln!(envelope, "corner\thorizontal\tvertical\tmembers")?;
        for (corner, body) in receipt.projection_envelope.iter().enumerate() {
            writeln!(
                envelope,
                "{}\t{}\t{}\t{}",
                corner,
                body.normalized_horizontal,
                body.normalized_vertical,
                body.members
                    .iter()
                    .map(|member| member.0.to_string())
                    .collect::<Vec<_>>()
                    .join(","),
            )?;
        }
        envelope.flush()?;
        let pair = if view == ViewKind::PhaseProduct {
            let (first, second) = control.phase_pair(mount);
            format!("{first},{second}")
        } else {
            "all".to_owned()
        };
        let mode_moments = wave
            .mode_measures
            .iter()
            .map(|mode| format!("p{}:{}", mode.mode.0, mode.projected_rate_moment))
            .collect::<Vec<_>>()
            .join(",");
        writeln!(
            summary,
            "{}\t{:?}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            name,
            view,
            pair,
            turns,
            control.zoom,
            receipt.visible_germs,
            receipt.collapsed_buckets,
            receipt.projection_envelope.len(),
            wave.wave_tick,
            wave.total_energy,
            wave.mode_measures
                .iter()
                .map(|mode| mode.visible_sections)
                .sum::<usize>(),
            mode_moments,
        )?;
    }
    summary.flush()?;

    let mut temporal_control = InstrumentControl::initial(mount);
    temporal_control.view = ViewKind::PhaseProduct;
    // The earliest finite-place pair exposes the largest projected current
    // support, making causal transport easiest to inspect frame by frame.
    temporal_control.pair_cursor = 0;
    let mut temporal_atlas = DimensionalReceiverAtlas::new(mount.source.clone())?;
    let temporal_receipt = temporal_atlas
        .receive(&DimensionalReceiverRequest {
            event: EventId(60_000_000),
            chronology: 1,
            receiver: ReceiverId(RECEIVER.0 + 1_000),
            deed: DimensionalReceiverDeed::Found(temporal_control.founding(mount)?),
        })?
        .receipt;
    let mut temporal_world = CausalWorld::new(law.clone(), standing.clone());
    let retained_energy = temporal_world.standing().energy.clone();
    let mut temporal_summary =
        BufWriter::new(File::create(directory.join("wave-temporal-summary.tsv"))?);
    writeln!(
        temporal_summary,
        "frame\twave_tick\tenergy\ttraveling_sections\tvisible_sections"
    )?;
    for frame in 0..8_u64 {
        if frame > 0 {
            let transition = temporal_world.receive(&DimensionalWaveEvent {
                event: EventId(61_000_000 + frame),
                impulses: Vec::new(),
            })?;
            if !transition.radiation[0].source_work.is_zero()
                || !transition.radiation[0].exact_energy_residual.is_zero()
                || temporal_world.standing().energy != retained_energy
            {
                return Err("temporal atlas propagation failed exact energy balance".into());
            }
        }
        let wave = law.restrict(temporal_world.standing(), &temporal_receipt)?;
        let face = render_slice(mount, &temporal_receipt, &wave, width, height)?;
        write(
            directory.join(format!("wave-temporal-{frame:02}.ppm")),
            encode_ppm(&face),
        )?;
        writeln!(
            temporal_summary,
            "{}\t{}\t{}\t{}\t{}",
            frame,
            wave.wave_tick,
            wave.total_energy,
            wave.sections.len(),
            wave.mode_measures
                .iter()
                .map(|mode| mode.visible_sections)
                .sum::<usize>(),
        )?;
    }
    temporal_summary.flush()?;
    Ok(())
}

fn write_snapshot(
    directory: &Path,
    mount: &ArithmeticDimensionalMount,
    control: &InstrumentControl,
    receipt: &DimensionalSliceReceipt,
    wave: &DimensionalWaveSliceReceipt,
    face: &DisplayFace,
) -> Result<(), Box<dyn Error>> {
    create_dir_all(directory)?;
    write(directory.join("receiver-slice.ppm"), encode_ppm(face))?;
    let mut trace = BufWriter::new(File::create(directory.join("receiver-slice.tsv"))?);
    writeln!(
        trace,
        "schema\tview\tgerm\tvalue\tsource_cell\tsource_grade\tlocal_dimension\tdisposition"
    )?;
    let description = control.description(mount);
    for (germ, body) in &receipt.germs {
        writeln!(
            trace,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            receipt.schema,
            description,
            germ.0,
            mount.occurrences[&germ.0].value,
            body.source_cell.0,
            body.source_grade,
            body.local_dimension,
            disposition_text(&body.disposition),
        )?;
    }
    trace.flush()?;
    let mut wave_trace = BufWriter::new(File::create(directory.join("receiver-wave.tsv"))?);
    writeln!(
        wave_trace,
        "schema\twave_tick\tmode\tcarrier\tfrom\tto\treal\timaginary\tenergy\tticks_until_arrival\tdisposition"
    )?;
    for section in &wave.sections {
        writeln!(
            wave_trace,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            wave.schema,
            wave.wave_tick,
            section.mode.0,
            section.carrier.0,
            section.from.0,
            section.to.0,
            section.current.real,
            section.current.imaginary,
            section.energy,
            section.ticks_until_arrival,
            wave_disposition_text(&section.disposition),
        )?;
    }
    wave_trace.flush()?;
    Ok(())
}

fn disposition_text(disposition: &DimensionalGermDisposition) -> String {
    match disposition {
        DimensionalGermDisposition::OutsideCausalHorizon => "outside-causal-horizon".to_owned(),
        DimensionalGermDisposition::Visible {
            horizontal,
            vertical,
            normalized_horizontal,
            normalized_vertical,
            depth,
        } => format!(
            "visible:h={horizontal}:v={vertical}:nh={normalized_horizontal}:nv={normalized_vertical}:depth={depth:?}"
        ),
        DimensionalGermDisposition::OutsideAperture {
            normalized_horizontal,
            normalized_vertical,
        } => format!("outside-aperture:{normalized_horizontal},{normalized_vertical}"),
        DimensionalGermDisposition::OutsideSlice {
            constraint,
            departure,
            radius,
        } => format!("outside-slice:{constraint}:departure={departure}:radius={radius}"),
        DimensionalGermDisposition::Unresolved { missing_axes } => {
            format!("unresolved:{missing_axes:?}")
        }
    }
}

fn wave_disposition_text(disposition: &DimensionalWaveSectionDisposition) -> String {
    match disposition {
        DimensionalWaveSectionDisposition::Visible(visible) => {
            format!(
                "visible:phase={}/{}:span2={}:speed2={}",
                visible.elapsed,
                visible.delay,
                visible.projected_span_square,
                visible.projected_speed_square,
            )
        }
        DimensionalWaveSectionDisposition::CarrierOutside => "carrier-outside".to_owned(),
        DimensionalWaveSectionDisposition::EndpointUnresolved => "endpoint-unresolved".to_owned(),
    }
}

fn report(
    mount: &ArithmeticDimensionalMount,
    wave_through: u64,
    control: &InstrumentControl,
    receipt: &DimensionalSliceReceipt,
    wave: &DimensionalWaveSliceReceipt,
    output: &Path,
) {
    let mode_receipts = wave
        .mode_measures
        .iter()
        .map(|mode| {
            format!(
                "p{}:sections={}/{}:energy={}:projected-rate-moment={}",
                mode.mode.0,
                mode.visible_sections,
                mode.traveling_sections,
                mode.energy,
                mode.projected_rate_moment,
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    println!(
        "receiver={} view=\"{}\" source-through={} wave-through={} total-dimension={:?} received-events={} received-cells={} received-dimension={:?} received-f-vector={:?} received-axes={} received-max-local-dimension={} local-ranks={:?} visible={} outside={} unresolved={} future={} collision-buckets={} exact-envelope-corners={} source-carriers={} chronology={} probes={} boundaries={} phase-returns={} projection-cells={} wave-tick={} wave-energy={} traveling-sections={} modes=[{}] output={} controls=\"P pause/run exact propagation; N one physical successor; E re-emit caused prime-power spectrum; H write/report exact receipts; R reset conditioned wave/chart; W/S view; left/right phase pair; up/down exact Cayley turn; A/D finite-place residue; Space gate; Z/X dilate; click inspect; Esc close\"",
        receipt.receiver.0,
        control.description(mount),
        mount.through,
        wave_through,
        receipt.source_dimension,
        receipt.received_source_events,
        receipt.received_source_cells,
        receipt.received_source_dimension,
        receipt.received_source_f_vector,
        receipt.received_coordinate_axes,
        receipt.received_maximum_local_dimension,
        receipt.local_dimension_population,
        receipt.visible_germs,
        receipt.outside_germs,
        receipt.unresolved_germs,
        receipt.future_germs,
        receipt.collapsed_buckets,
        receipt.projection_envelope.len(),
        mount.source.carriers().len(),
        mount.chronology_carriers.len(),
        mount.probe_carriers.len(),
        mount.boundary_carriers.len(),
        mount.phase_return_carriers.len(),
        receipt.projection_cells,
        wave.wave_tick,
        wave.total_energy,
        wave.sections.len(),
        mode_receipts,
        output.display(),
    );
}

fn integer_rat(value: u64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn quantize_unit(value: &Rat) -> u8 {
    if !value.is_positive() {
        return 0;
    }
    if value >= &Rat::one() {
        return u8::MAX;
    }
    let scaled = value * integer_rat(u64::from(u8::MAX));
    (scaled.numer() / scaled.denom())
        .to_u8()
        .expect("an exact unit response fits one terminal octet")
}

fn draw_support_line(
    membrane: &mut TerminalPhaseMembrane,
    mut x0: i32,
    mut y0: i32,
    x1: i32,
    y1: i32,
) {
    let dx = (x1 - x0).abs();
    let sx = if x0 < x1 { 1 } else { -1 };
    let dy = -(y1 - y0).abs();
    let sy = if y0 < y1 { 1 } else { -1 };
    let mut error = dx + dy;
    loop {
        membrane.receive_support(x0, y0);
        if x0 == x1 && y0 == y1 {
            break;
        }
        let twice = 2 * error;
        if twice >= dy {
            error += dy;
            x0 += sx;
        }
        if twice <= dx {
            error += dx;
            y0 += sy;
        }
    }
}

fn draw_phase_current(
    membrane: &mut TerminalPhaseMembrane,
    mut x0: i32,
    mut y0: i32,
    x1: i32,
    y1: i32,
    section: usize,
) {
    let dx = (x1 - x0).abs();
    let sx = if x0 < x1 { 1 } else { -1 };
    let dy = -(y1 - y0).abs();
    let sy = if y0 < y1 { 1 } else { -1 };
    let mut error = dx + dy;
    loop {
        // The current is the exact finite-volume population of this causal
        // carrier phase. No screen-space brightness ramp is invented.
        membrane.receive_current(x0, y0, section);
        if x0 == x1 && y0 == y1 {
            break;
        }
        let twice = 2 * error;
        if twice >= dy {
            error += dy;
            x0 += sx;
        }
        if twice <= dx {
            error += dx;
            y0 += sy;
        }
    }
}

fn draw_support_circle(
    membrane: &mut TerminalPhaseMembrane,
    center_x: i32,
    center_y: i32,
    radius: i32,
) {
    let mut x = radius;
    let mut y = 0;
    let mut error = 1 - radius;
    while x >= y {
        for (dx, dy) in [
            (x, y),
            (y, x),
            (-y, x),
            (-x, y),
            (-x, -y),
            (-y, -x),
            (y, -x),
            (x, -y),
        ] {
            membrane.receive_support(center_x + dx, center_y + dy);
        }
        y += 1;
        if error < 0 {
            error += 2 * y + 1;
        } else {
            x -= 1;
            error += 2 * (y - x) + 1;
        }
    }
}

fn draw_support_diamond(
    membrane: &mut TerminalPhaseMembrane,
    center_x: i32,
    center_y: i32,
    radius: i32,
) {
    draw_support_line(
        membrane,
        center_x,
        center_y - radius,
        center_x + radius,
        center_y,
    );
    draw_support_line(
        membrane,
        center_x + radius,
        center_y,
        center_x,
        center_y + radius,
    );
    draw_support_line(
        membrane,
        center_x,
        center_y + radius,
        center_x - radius,
        center_y,
    );
    draw_support_line(
        membrane,
        center_x - radius,
        center_y,
        center_x,
        center_y - radius,
    );
}

fn draw_support_border(membrane: &mut TerminalPhaseMembrane) {
    let right = i32::try_from(membrane.width.saturating_sub(1)).unwrap_or(i32::MAX);
    let bottom = i32::try_from(membrane.height.saturating_sub(1)).unwrap_or(i32::MAX);
    draw_support_line(membrane, 0, 0, right, 0);
    draw_support_line(membrane, right, 0, right, bottom);
    draw_support_line(membrane, right, bottom, 0, bottom);
    draw_support_line(membrane, 0, bottom, 0, 0);
}
