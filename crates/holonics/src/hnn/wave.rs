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
//! [definition; hypotheses] The ring is **passive**, unpumped and linear, on the exact law
//! ([`WavePort::at_rest`]) or with its state carried on a declared lattice ([`WavePort::on_lattice`]). Passive: `C ⪰ 0` and `D ⪰ 0` are the owner's (`ResonatorMaterial::new`), and
//! [`WavePort::at_rest`] requires `K ⪰ 0`, decided exactly by the inertia owner, so that the stored
//! energy `E = ½ (w C w + u K u)` is nonnegative and the net work the source gives from rest is
//! nonnegative (`Σ boundary_work ≥ E ≥ 0`). The loaded-solve certificate `2C + hD + (h²/2)K ⪰ 0`
//! alone does not give that: `C = I`, `K = −I`, `D = 0`, `h = Y = 1` is certified, its balances close,
//! and a wave of amplitudes `1, 0` is repaid with more than it brought (incident `1/4`, reflected
//! `13/20`, `E = −2/5`). A signed stiffness (a boost) has its own owner, the signature path; this port
//! is the passive one. The consumer equation above is the unpumped one, and the pump's subharmonic
//! locks and the sheet symbol are the owed pumped port.
//!
//! [definition] **The boundary work is over the whole port vector.** The ring's coordinates are coupled
//! by `K` (and `C`, `D`), so a wave on one coordinate is reflected on all of them:
//! `b = a − (2/Y) ω` is a vector, and the work booked is `(hY/4)(|a|² − |b|²)` with both norms over the
//! full vector ([`ReceivedTick::reflected`]), not over the driven coordinate. (`C = I`,
//! `K = [[2, 1], [1, 2]]`, `h = Y = 1`, input `(1, 0)` reflects `b = (31/63, 4/63)`: the work is
//! `748/3969`, where the driven coordinate alone would give `752/3969`.) The wave drives one real coordinate (a mono pressure drives the
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
//! | the port on a lattice: the state split by error feedback, its remainders carried, every tick closing with its chart and split terms within their bounds | `HNN/Ring.ring_tick_executed_energy_balance`, `feedback_tick`; the port's own statement owed (#62) | [`WavePort::on_lattice`] |
//!
//! [definition; agent-inferred, October 10; the
//! [bank record](../../../../research/records/2026-10-10_A_BANK_OF_RINGS_SOUNDS_ITS_EMISSION_ON_A_BOUNDED_LATTICE.md)]
//! **The port on a lattice** ([`WavePort::on_lattice`]). On the exact law the carried state's
//! denominators grow with every tick (the factor `145` per tick on the replica's bank), so its bits
//! grow linearly with the stream. The bounded realization is the ring owner's own lattice step:
//! the solve stays exact, and the rate, displacement and velocity images are each split at the
//! declared lattice `2^(−L)` by error feedback (`hnn::chart::carry`, `x + r′ = y + r`), with the
//! remainders carried by the port from tick to tick, never released mid-stream. Every carried state
//! entry then lies on the lattice. Each tick's balance gains the chart and split terms, each within
//! its certified bound (`ResonatorStep::closes`), and the port books them:
//! `E′ − E = W_port − hωDω + chart + split`.
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
use crate::hnn::constitution::Lattice;
use crate::hnn::contact::symmetric;
use crate::hnn::ring::{ResonatorOperands, ResonatorRemainders, ResonatorStep};
use crate::ratio::linear::inertia::inertia;
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

/// [definition] **One received tick**: the incident amplitude `a` on the driven coordinate, the
/// reflected wave `b` on **every** coordinate of the port, the energy the incident and the reflected
/// waves carry through the port (both over the full vector), the net work booked at the boundary, and
/// the owner's executed step.
#[derive(Clone, Debug, PartialEq)]
pub struct ReceivedTick {
    /// The port's clock before the tick: the index of the amplitude consumed.
    pub tick: usize,
    /// `a`, the incident amplitude on the driven coordinate.
    pub incident: Rat,
    /// The coordinate the wave drives.
    pub coordinate: usize,
    /// `b = a − (2/Y) ω`, the whole reflected wave: every coordinate of the port reflects, not only
    /// the driven one.
    pub reflected: Vec<Rat>,
    /// `(hY/4) Σ a²` over the ring's coordinates.
    pub incident_energy: Rat,
    /// `(hY/4) Σ b²` over the ring's coordinates.
    pub reflected_energy: Rat,
    /// The net energy the source gives the ring through the port: incident less reflected.
    pub boundary_work: Rat,
    /// The owner's executed tick (its state, rate, remainders and balance terms).
    pub step: ResonatorStep,
    /// The lattice exponent `L` the state was carried on, or `None` under the exact law.
    pub lattice: Option<u32>,
}

impl ReceivedTick {
    /// The reflected amplitude on the driven coordinate: one entry of [`ReceivedTick::reflected`].
    pub fn driven_reflected(&self) -> &Rat {
        &self.reflected[self.coordinate]
    }

    /// **The consumer equation, every tick**: the owner's step closes
    /// ([`ResonatorStep::closes`]) with no pump or integration term (the unpumped law), the booked
    /// work is the incident less the reflected energy, and the stored energy changes by that work
    /// less the ring's dissipation, `E′ − E = (hY/4)(a² − b²) − h ω D ω`, plus, on a lattice, the
    /// chart and split terms within their certified bounds; under the exact law both are zero.
    pub fn closes(&self) -> bool {
        let step = &self.step;
        step.closes()
            && self.reflected == step.output
            && step.pump.is_zero()
            && step.integration.is_zero()
            && (self.lattice.is_some() || (step.chart.is_zero() && step.split.is_zero()))
            && self.boundary_work == &self.incident_energy - &self.reflected_energy
            && &step.after - &step.before
                == &self.boundary_work - &step.dissipation + &step.chart + &step.split
    }

    /// The ring's emission `e = b − a`: the reflected wave less the direct reflection of the
    /// incident amplitude on the driven coordinate, `−(2/Y) ω`, what the ring itself sends back.
    pub fn emission(&self) -> Vec<Rat> {
        let mut out = self.reflected.clone();
        out[self.coordinate] = &out[self.coordinate] - &self.incident;
        out
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
    lattice: Option<Lattice>,
    remainders: ResonatorRemainders,
}

impl WavePort {
    /// **A port at rest**: the ring's operands and the real coordinate the wave drives. Refused
    /// when the coordinate is outside the ring's width, the ring is pumped, scheduled, nonlinear
    /// or on a lattice (the consumer equation is the unpumped exact one), or its stiffness `K` is
    /// not positive semidefinite (the port is the passive one; module header).
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
        // Passive: C and D are positive semidefinite by the owner; K must be too, or the stored
        // energy is not nonnegative and the port can be repaid more than it brought (module header).
        let (_, stiffness, _) = material.forms();
        if inertia(&symmetric(stiffness)?).negative != 0 {
            return Err(HnnError::Resonator {
                ring: operands.ring(),
                what: "a matched wave drives a passive ring: its stiffness K must be positive semidefinite (a signed stiffness has its own owner)",
            });
        }
        let rest = vec![Rat::zero(); width];
        Ok(Self {
            operands,
            coordinate,
            state: [rest.clone(), rest.clone()],
            tick: 0,
            lattice: None,
            remainders: ResonatorRemainders {
                rate: rest.clone(),
                state: [rest.clone(), rest],
            },
        })
    }

    /// **A port at rest whose state is carried on `lattice`** (module header): the same admission
    /// as [`Self::at_rest`] (an exact solve, no chart), with every tick's rate and state split at
    /// `2^(−L)` by error feedback and the remainders carried by the port.
    pub fn on_lattice(
        operands: ResonatorOperands,
        coordinate: usize,
        lattice: Lattice,
    ) -> Result<Self, HnnError> {
        let mut port = Self::at_rest(operands, coordinate)?;
        port.lattice = Some(lattice);
        Ok(port)
    }

    /// The lattice the state is carried on, `None` under the exact law.
    pub fn lattice(&self) -> Option<Lattice> {
        self.lattice
    }

    /// The remainders the next tick meets (all zero under the exact law).
    pub fn remainders(&self) -> &ResonatorRemainders {
        &self.remainders
    }

    /// [definition; agent-inferred, October 10; the bank record §7] **A key seated at the port**:
    /// the carried state replaced by `state`, as one action at the port that sets the ring's initial
    /// configuration for the epoch it opens, returning the work it books, `E(state) − E(before)`.
    /// On a lattice the key must lie on it, and the carried remainders are cleared: they were the
    /// rounding of the trajectory the key replaces. Refused for a state of another width.
    pub fn seat(&mut self, state: [Vec<Rat>; 2]) -> Result<Rat, HnnError> {
        let width = self.operands.width();
        if state[0].len() != width || state[1].len() != width {
            return Err(HnnError::Shape {
                what: "a seated key has the ring's realified width",
                expected: width,
                found: state[0].len().min(state[1].len()),
            });
        }
        if let Some(lattice) = self.lattice
            && !state.iter().flatten().all(|x| lattice.contains(x))
        {
            return Err(HnnError::Wave {
                what: "a key seated at a port on a lattice lies on that lattice",
            });
        }
        let before = self.stored_energy()?;
        self.state = state;
        if self.lattice.is_some() {
            let rest = vec![Rat::zero(); width];
            self.remainders = ResonatorRemainders {
                rate: rest.clone(),
                state: [rest.clone(), rest],
            };
        }
        Ok(self.stored_energy()? - before)
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
            &self.remainders,
            self.lattice.as_ref(),
        )?;
        let quarter = self.operands.hop() * self.operands.admittance() / integer(4);
        let incident_energy = &quarter * dot(&drive, &drive);
        let reflected_energy = &quarter * dot(&step.output, &step.output);
        let received = ReceivedTick {
            tick: self.tick,
            incident: incident.clone(),
            coordinate: self.coordinate,
            reflected: step.output.clone(),
            boundary_work: &incident_energy - &reflected_energy,
            incident_energy,
            reflected_energy,
            step,
            lattice: self.lattice.map(|lattice| lattice.exponent()),
        };
        if !received.closes() {
            return Err(HnnError::Wave {
                what: "the executed tick's port balance does not close",
            });
        }
        self.state = received.step.state.clone();
        if self.lattice.is_some() {
            self.remainders = received.step.remainders().clone();
        }
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
