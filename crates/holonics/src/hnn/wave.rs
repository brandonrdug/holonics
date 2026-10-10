//! **A matched wave at a loaded ring's port, and the ring that continues across its stream** (second
//! rung of the acoustic line; the
//! [record](../../../../research/records/2026-10-09_A_MATCHED_WAVE_ENTERS_A_LOADED_RING_AND_ITS_STATE_CROSSES_ITS_OWN_SECTION.md);
//! #148, #73, #386).
//!
//! [definition; agent-inferred, October 9] **A wave is not a code.** THE_MACHINE guard 9 keeps an
//! exterior *code* (a byte, a code point, a sample read as an alphabet's symbol, a joint angle)
//! out of the field: only an `Encoded` passage, whose classes the field's own key location
//! founded, enters it. A sampled sound read as a *pressure* is a different quantity: an exact
//! amplitude with a power pairing, the incident wave `a` of a source matched to a ring's storage
//! port, whose reflected wave `b = a − (2/Y) ω` returns to the source, and the power that
//! crosses is `(Y/4)(a² − b²)`. It is admitted at a port by passivity (the ring's certified
//! operator, [`crate::hnn::ring::ResonatorMaterial::certify`]), and by nothing else:
//!
//! ```text
//! MatchedWave { Y, h, a_0, a_1, … }            exact amplitudes, the port's admittance, the exact step
//! M ω = 2C w + h a − h K u ,  M = 2C + (h/Y) I + h D + (h²/2) K       (the owner's tick, hnn::ring)
//! u′ = u + h ω ,  w′ = 2ω − w ,  b = a − (2/Y) ω
//! E′ − E = (h Y/4)(a² − b²) − h ω D ω ,   E = ½ (K u² + C w²)         (ResonatorStep::closes)
//! ```
//!
//! [`MatchedWave`] is a separate type: it is built from exact amplitudes and a declared port and
//! step, never from an [`crate::hnn::encoding::Encoded`], and no conversion either way exists
//! (structural, `E0277` and `E0308` below). A sample as a symbol keeps having no path into the
//! field; a sample as a wave amplitude has a path to a *port*, where the ring's own dynamics make
//! the symbols (see [`crate::hnn::dynamic_section`]). The calibration of a recording to
//! amplitudes (a gain, an origin, an exact step) is the boundary chart's and declares nothing of
//! meaning; the type carries only the exact numbers and the port they were matched to.
//!
//! [definition] **The matched source is not the World.** `hnn::word::world_boundary` returns an
//! actual co-clock World's wave at an unloaded source port and books `hY(|b|² − |a|²)/4 = −W_World`
//! against that World's state (`admit_source_boundary` refuses a loaded ring). A recording is a
//! non-participating source: its incident wave comes from the chart, not from a state that the
//! reflection would change, and the reflected wave is absorbed by the matched source. The
//! power that crosses is the same pairing, booked at the boundary per tick
//! ([`ReceivedTick::boundary_work`]); the World's join is not changed.
//!
//! [definition] **The ring continues across the stream** ([`WavePort`]). The mode state `(u, w)` of
//! the ring is carried from tick to tick and from wave to wave: it is the quotient of the past
//! sufficient for the ring's response to its admitted future (a Kalman realization of its impulse
//! response), never a record of the samples. The port holds the operands, the driven coordinate,
//! that state and its clock, and nothing that grows. `hnn::word` drops a loaded ring's mode state
//! at the word's end; this owner is a continuing port outside any word and is not joined to a
//! resident (owed). The chunking of a stream changes nothing: `s_((j+1)g) = Tᵍ s_(jg) + Σ_a T^(g−1−a) B x_(jg+a)`.
//!
//! [definition; hypotheses] The ring is unpumped, linear and on the exact law (no lattice): the
//! consumer equation above is the unpumped one, and the pump's subharmonic locks and the sheet
//! symbol are the owed pumped port. The wave drives one real coordinate (a mono pressure drives the
//! real force of a node; the quadrature stays at rest for an isotropic node). Each tick's balance is
//! checked before the state is committed, and a refused tick leaves the port as it was.
//!
//! The computational object is the helical pair interaction. Of the winding guide's six general
//! objects this owner touches the **tube** (the port is the boundary of a longitudinal span: the
//! wave is consumed as a pairing, reflected at the boundary, on its clock `h`), **cell holonomy**
//! (the state carried across the cells of the stream) and **continuation** (the level the ring lifts
//! from is its state; the stream is a section of it). The helix and the placement are
//! `hnn::dynamic_section`'s reading of this state; the pair, a lock of one ring against another,
//! stays attached through that reading's arrival word and is not built here.
//!
//! | Law | Lean | Rust |
//! |---|---|---|
//! | the executed tick closes with every term, the port term the wave's `(hY/4)(a² − b²)` | `HNN/Ring.ring_tick_executed_energy_balance` | [`ReceivedTick::closes`], `ResonatorStep::closes` |
//! | the matched port, the wave booked as boundary work, the continuing state | owed (#62) | [`MatchedWave`], [`WavePort`] |
//! | a wave is not a code | structural (`compile_fail`) | [`MatchedWave`] |
//!
//! # Guard 9, the second half: a wave is not an `Encoded`
//!
//! A `MatchedWave` is never forged (structural, `E0451`), is never made from an `Encoded`, and
//! never becomes one (`E0277`); each type is refused where the other goes (`E0308`):
//!
//! ```compile_fail,E0451
//! use holonics::hnn::wave::MatchedWave;
//! use holonics::ratio::Rat;
//! fn forge(admittance: Rat, hop: Rat) -> MatchedWave {
//!     MatchedWave { admittance, hop, samples: Vec::new() }
//! }
//! ```
//!
//! ```compile_fail,E0277
//! use holonics::hnn::encoding::Encoded;
//! use holonics::hnn::wave::MatchedWave;
//! fn from_a_code(encoded: Encoded) -> MatchedWave {
//!     encoded.into()
//! }
//! ```
//!
//! ```compile_fail,E0277
//! use holonics::hnn::encoding::Encoded;
//! use holonics::hnn::wave::MatchedWave;
//! fn into_a_code(wave: MatchedWave) -> Encoded {
//!     wave.into()
//! }
//! ```
//!
//! ```compile_fail,E0308
//! use holonics::hnn::encoding::Encoded;
//! use holonics::hnn::wave::MatchedWave;
//! fn ingest(_: &Encoded) {}
//! fn a_wave_where_a_code_goes(wave: &MatchedWave) {
//!     ingest(wave)
//! }
//! ```
//!
//! ```compile_fail,E0308
//! use holonics::hnn::encoding::Encoded;
//! use holonics::hnn::wave::WavePort;
//! fn a_code_where_a_wave_goes(port: &mut WavePort, encoded: &Encoded) {
//!     let _ = port.receive(encoded);
//! }
//! ```
//!
//! The lawful form compiles and runs: a matched wave of exact amplitudes at a declared port, every
//! tick closing its balance, the state carried.
//!
//! ```
//! use holonics::hnn::ring::{ResonatorMaterial, ResonatorOperands};
//! use holonics::hnn::wave::{MatchedWave, WavePort};
//! use holonics::ratio::linear::ExactRatMatrix;
//! use holonics::ratio::{integer, rat};
//! fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     let identity = ExactRatMatrix::identity(2)?;
//!     let material = ResonatorMaterial::new(
//!         identity.clone(),
//!         identity.scaled(&integer(2)),
//!         ExactRatMatrix::zero(2, 2)?,
//!         None,
//!     )?;
//!     let operands = ResonatorOperands::at_cut(0, &material, &integer(2), &integer(1), None)?;
//!     let mut port = WavePort::at_rest(operands, 0)?;
//!     let wave = MatchedWave::new(integer(2), integer(1), vec![integer(3), rat(-1, 2), integer(0)])?;
//!     for tick in port.receive(&wave)? {
//!         assert!(tick?.closes());
//!     }
//!     assert_eq!(port.ticks(), 3);
//!     Ok(())
//! }
//! ```

use num_traits::{Signed, Zero};

use crate::hnn::HnnError;
use crate::hnn::ring::{ResonatorOperands, ResonatorRemainders, ResonatorStep};
use crate::ratio::linear::vector::dot;
use crate::ratio::{Rat, integer};

/// [definition; agent-inferred, October 9] **A matched wave**: the incident wave amplitudes of a
/// source matched to a port of admittance `Y`, on an exact step `h`, one amplitude per tick
/// (module header). The fields are private and nothing converts an
/// [`crate::hnn::encoding::Encoded`] into one or one into it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatchedWave {
    admittance: Rat,
    hop: Rat,
    samples: Vec<Rat>,
}

impl MatchedWave {
    /// A matched wave at the port's admittance and the exact step; both are refused unless
    /// positive. The amplitudes are exact rationals (an integer PCM needs no quantization).
    pub fn new(admittance: Rat, hop: Rat, samples: Vec<Rat>) -> Result<Self, HnnError> {
        if !admittance.is_positive() || !hop.is_positive() {
            return Err(HnnError::NonpositiveDeclaration);
        }
        Ok(Self {
            admittance,
            hop,
            samples,
        })
    }

    /// The admittance `Y` of the port the source is matched to.
    pub fn admittance(&self) -> &Rat {
        &self.admittance
    }

    /// The exact step `h` between amplitudes: the wave's clock in the ring's time.
    pub fn hop(&self) -> &Rat {
        &self.hop
    }

    /// The incident amplitudes, in tick order.
    pub fn samples(&self) -> &[Rat] {
        &self.samples
    }

    pub fn len(&self) -> usize {
        self.samples.len()
    }

    pub fn is_empty(&self) -> bool {
        self.samples.is_empty()
    }
}

/// [definition] **One received tick**: the incident amplitude `a`, the reflected amplitude `b`, the
/// energy the incident and the reflected waves carry through the port, the net work booked at the
/// boundary, and the owner's executed step.
#[derive(Clone, Debug, PartialEq)]
pub struct ReceivedTick {
    /// The port's clock before the tick: the index of the amplitude consumed.
    pub tick: usize,
    /// `a`, the incident amplitude on the driven coordinate.
    pub incident: Rat,
    /// `b = a − (2/Y) ω` on the driven coordinate.
    pub reflected: Rat,
    /// `(hY/4) Σ a²` over the ring's coordinates.
    pub incident_energy: Rat,
    /// `(hY/4) Σ b²` over the ring's coordinates.
    pub reflected_energy: Rat,
    /// The net energy the source gives the ring through the port: incident less reflected.
    pub boundary_work: Rat,
    /// The owner's executed tick (its state, rate, remainders and balance terms).
    pub step: ResonatorStep,
}

impl ReceivedTick {
    /// **The consumer equation, every tick**: the owner's step closes
    /// ([`ResonatorStep::closes`]) with no pump, integration, chart or split term (the unpumped
    /// exact law), the booked work is the incident less the reflected energy, and the stored
    /// energy changes by that work less the ring's dissipation,
    /// `E′ − E = (hY/4)(a² − b²) − h ω D ω`.
    pub fn closes(&self) -> bool {
        let step = &self.step;
        step.closes()
            && step.pump.is_zero()
            && step.integration.is_zero()
            && step.chart.is_zero()
            && step.split.is_zero()
            && self.boundary_work == &self.incident_energy - &self.reflected_energy
            && &step.after - &step.before == &self.boundary_work - &step.dissipation
    }
}

/// [definition; agent-inferred, October 9] **A ring continuing across a matched wave's stream**
/// (module header): the operands of one unpumped, linear, exact ring, the coordinate the wave
/// drives, the mode state `(u, w)` and the port's clock. Nothing that grows with the stream.
#[derive(Clone, Debug)]
pub struct WavePort {
    operands: ResonatorOperands,
    coordinate: usize,
    state: [Vec<Rat>; 2],
    tick: usize,
}

impl WavePort {
    /// **A port at rest**: the ring's operands and the real coordinate the wave drives. Refused
    /// when the coordinate is outside the ring's width, or the ring is pumped, scheduled,
    /// nonlinear or on a lattice (the consumer equation is the unpumped exact one).
    pub fn at_rest(operands: ResonatorOperands, coordinate: usize) -> Result<Self, HnnError> {
        let width = operands.width();
        if coordinate >= width {
            return Err(HnnError::Shape {
                what: "the driven coordinate (inside the ring's realified width)",
                expected: width,
                found: coordinate,
            });
        }
        let material = operands.material();
        if material.pump().is_some() || operands.schedule().is_some() {
            return Err(HnnError::Resonator {
                ring: operands.ring(),
                what: "a matched wave drives an unpumped ring; the pumped port is owed",
            });
        }
        if material.saturation().is_some() || !operands.charts().is_empty() {
            return Err(HnnError::Resonator {
                ring: operands.ring(),
                what: "a matched wave drives a linear ring on the exact law",
            });
        }
        let rest = vec![Rat::zero(); width];
        Ok(Self {
            operands,
            coordinate,
            state: [rest.clone(), rest],
            tick: 0,
        })
    }

    /// The ring's operands.
    pub fn operands(&self) -> &ResonatorOperands {
        &self.operands
    }

    /// The coordinate the wave drives.
    pub fn coordinate(&self) -> usize {
        self.coordinate
    }

    /// The port's clock: the amplitudes consumed so far.
    pub fn ticks(&self) -> usize {
        self.tick
    }

    /// The mode state `[u, w]` the next amplitude meets: the carried quotient.
    pub fn state(&self) -> [&[Rat]; 2] {
        [&self.state[0], &self.state[1]]
    }

    /// The driven coordinate's phase point `(w, u)`, the plane
    /// [`crate::hnn::dynamic_section::SectionReader`] reads.
    pub fn phase_point(&self) -> [Rat; 2] {
        [
            self.state[1][self.coordinate].clone(),
            self.state[0][self.coordinate].clone(),
        ]
    }

    /// The stored energy `E = ½ (w C w + u K u)` of the carried state.
    pub fn stored_energy(&self) -> Result<Rat, HnnError> {
        self.operands.energy_at(
            self.operands.phase_at(self.tick),
            &self.state[0],
            &self.state[1],
        )
    }

    /// **Receive a matched wave**: an iterator that consumes one amplitude per `next`, in order,
    /// carrying the state. Refused unless the wave is matched to this port (its admittance and
    /// step are the operands'). Ticks not drawn are not consumed; the port's clock says where it is.
    pub fn receive<'a>(&'a mut self, wave: &'a MatchedWave) -> Result<Receiving<'a>, HnnError> {
        if wave.admittance != *self.operands.admittance() || wave.hop != *self.operands.hop() {
            return Err(HnnError::Wave {
                what: "the wave is not matched to this port: its admittance or its step differs",
            });
        }
        Ok(Receiving {
            port: self,
            wave,
            next: 0,
        })
    }

    /// One amplitude: the owner's step, its balance checked, and only then the state committed.
    fn consume(&mut self, incident: &Rat) -> Result<ReceivedTick, HnnError> {
        let mut drive = vec![Rat::zero(); self.operands.width()];
        drive[self.coordinate] = incident.clone();
        let step = self.operands.step(
            self.tick,
            &drive,
            [&self.state[0], &self.state[1]],
            &ResonatorRemainders::default(),
            None,
        )?;
        let quarter = self.operands.hop() * self.operands.admittance() / integer(4);
        let incident_energy = &quarter * dot(&drive, &drive);
        let reflected_energy = &quarter * dot(&step.output, &step.output);
        let received = ReceivedTick {
            tick: self.tick,
            incident: incident.clone(),
            reflected: step.output[self.coordinate].clone(),
            boundary_work: &incident_energy - &reflected_energy,
            incident_energy,
            reflected_energy,
            step,
        };
        if !received.closes() {
            return Err(HnnError::Wave {
                what: "the executed tick's port balance does not close",
            });
        }
        self.state = received.step.state.clone();
        self.tick += 1;
        Ok(received)
    }
}

/// The ticks of one matched wave received by a port, drawn lazily ([`WavePort::receive`]).
#[derive(Debug)]
pub struct Receiving<'a> {
    port: &'a mut WavePort,
    wave: &'a MatchedWave,
    next: usize,
}

impl Iterator for Receiving<'_> {
    type Item = Result<ReceivedTick, HnnError>;

    fn next(&mut self) -> Option<Self::Item> {
        let sample = self.wave.samples.get(self.next)?;
        let received = self.port.consume(sample);
        // A refused tick ends the reception: the port stays where it was.
        self.next = if received.is_ok() {
            self.next + 1
        } else {
            self.wave.samples.len()
        };
        Some(received)
    }
}
