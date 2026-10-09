//! **Frames located by loop closure: a source's period is a located navigator's closed cycle**
//! (THE_REBUILD U6; the
//! [record](../../../../../research/records/2026-10-09_A_TONES_PERIOD_IS_LOCATED_NOT_DECLARED.md);
//! the [encoder record](../../../../../research/records/2026-10-09_THE_HOLONIC_ENCODER_EXPLODES_A_SOURCE_INTO_CO_PRESENT_FRAMES_AND_AN_AXIS_EXPOSES_WITHOUT_AUTHORING_WHEN_NO_RELABELLING_MOVES_IT.md),
//! §5, owed join 1; #386, #73, #148).
//!
//! [definition; agent-inferred, October 9] **The frame family** ([`FrameFamily`]) is the machine's
//! declared set of carry helices ([`CarryHelix`]: closing rings of pairwise coprime periods,
//! cascaded as an odometer, the last ring the receiving ring). It is declared once for every
//! source, as the rings of a field are; it is not declared from a source and carries no source's
//! period. A passage over `|A|` classes is located on each frame by the existing loop closure
//! ([`TransportLocation::locate`]): the frame **carries** the passage when its fibre is one gauge
//! class, and the located transport `(A, λ)` then steps the frame's lift,
//!
//! ```text
//! ℓ_0 = key,   ℓ_(k+1) = ℓ_k + A(λ(c(ℓ_k)))      on ℤ/D,  D = ∏ d_g,  c(ℓ) = ⌊ℓ / D_low⌋
//! ```
//!
//! a deterministic map of a finite set, so the lift from a key on a cycle returns
//! ([`LocatedTransport::cycle`]): its first return is the cycle's length `n`, and the joint clock
//! turns `Σ_(k<n) A = w · D` whole times, the cycle's winding `w` (helix = circle + carry; the
//! carry is kept, never reduced away, as the scalar quotient `z^g = 1` would).
//!
//! [definition; agent-inferred] **The period is the located cycle.** A source's period is the
//! cycle length every carrying frame reads at the key that regenerates the read passage
//! ([`FrameLocation::period`]). Nothing is computed on the samples: the family is not a list of
//! candidate periods (a ring's period is a frame's own, and the cycle of 7 on the rings `(2, 5)`,
//! or of 12 on `(3, 4)`, is no ring's period), and the only reading of the located navigator is
//! its own first return. Frames that do not carry the passage hold their reading, typed:
//!
//! | reading | meaning |
//! |---|---|
//! | [`FrameReading::Narrow`] | the passage's classes exceed the receiving ring's cells (no injective labels) |
//! | [`FrameReading::Empty`] | no survivor: the frame's navigators cannot generate the passage |
//! | [`FrameReading::Plural`] | several gauge classes: the passage underdetermines the navigator (a periodic passage carries only one cycle of information) |
//! | [`FrameReading::Open`] | one gauge class, but the key's lift is on no closed cycle |
//! | [`FrameReading::One`] | one gauge class with its key's closed cycle |
//!
//! No frame carrying the passage refuses ([`FrameRefusal::Unlocated`]); carrying frames that read
//! different cycles refuse ([`FrameRefusal::Disagree`]). A period is never invented.
//!
//! [proved-derived] **Relabelling.** Location reads only the equality of occurrences
//! (`transport`, "The relabelling law"), so for every permutation `π` of the classes each frame's
//! reading, its cycle and its winding on `π∘x` are those on `x`.
//!
//! [definition] The computational object is the helical pair interaction. Of the winding guide's
//! six general objects this owner touches the **helix** (the frames and their lifts, circle plus
//! carry) and **faces and placement** (the receiving cell read at the lift). The pair, the cell
//! holonomy, the tube and the tower thread stay attached through the located transport and the
//! encoding that consumes it.
//!
//! **What this does not do.** The family carries a passage only when it is an orbit of one of its
//! navigators (a quantized sawtooth is the odometer's own receiving digit); many periodic
//! passages are `Empty` or `Plural` on every frame and are held, not located. It founds no chart
//! by itself: the carrying frame's [`FrameCycle::location`] is the input of
//! `hnn::encoding::PassageChart::located`, and the consumer's squares `D E = ρ`,
//! `E T_c = U_c E` are `hnn::encoding::Encoded::through`'s.
//!
//! | Law | Lean | Rust |
//! |---|---|---|
//! | frames of coprime periods read one lifted clock; the lift is circle plus carry | `HNN/Prediction.joint_residue_determines_position`; `Geometry/PhaseCarry.winding_add` | [`CarryHelix`] |
//! | the frame carries the passage iff the loop-closure fibre is one gauge class | `Keys.fibre_cons` | [`TransportLocation::fibre`], [`FrameReading`] |
//! | the located cycle: first return of the lift, `Σ A = w · D` | owed (#62) | [`LocatedTransport::cycle`], [`FrameCycle`] |
//! | a period is the cycle every carrying frame reads; none or disagreeing refuses | owed (#62) | [`FrameLocation::period`], [`FrameRefusal`] |

use thiserror::Error;

use super::transport::{CarryHelix, Cycle, LocatedTransport, TransportFibre, TransportLocation};
use crate::compression::CompressionError;

/// [definition; agent-inferred, October 9] **The machine's frame family** (module header): carry
/// helices declared before any source is read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrameFamily {
    frames: Vec<CarryHelix>,
}

impl FrameFamily {
    /// A family of the declared frames; refused when it declares none.
    pub fn new(frames: Vec<CarryHelix>) -> Result<Self, CompressionError> {
        if frames.is_empty() {
            return Err(CompressionError::Helix {
                reason: "a frame family declares at least one frame",
            });
        }
        Ok(Self { frames })
    }

    /// **The two-ring frames of a declared ring bound**: every ordered pair of pairwise coprime
    /// ring periods `(d_0, d_1)` with `2 ≤ d_0, d_1 ≤ bound` that the helix law admits
    /// ([`CarryHelix::new`]), ring 0 the hidden ring and ring 1 the receiving ring. The bound is a
    /// ring size, the family's own capacity; it is not a period of any source.
    pub fn pairs(bound: u64) -> Result<Self, CompressionError> {
        let mut frames = Vec::new();
        for hidden in 2..=bound {
            for receiving in 2..=bound {
                if let Ok(helix) = CarryHelix::new(vec![hidden, receiving]) {
                    frames.push(helix);
                }
            }
        }
        Self::new(frames)
    }

    /// The declared frames.
    pub fn frames(&self) -> &[CarryHelix] {
        &self.frames
    }

    /// **Locate a read set on every frame** (module header): `classes` classes over `passages`
    /// (their codes are classes below `classes`, read for equality only). Each frame returns its
    /// typed reading; the first passage's key fibre gives the key whose closed cycle is read.
    /// Refused with a read set of no passage, or a code at or past `classes`
    /// ([`TransportLocation::locate`]).
    pub fn locate(
        &self,
        classes: usize,
        passages: &[Vec<usize>],
    ) -> Result<FrameLocation, CompressionError> {
        let Some(first) = passages.first() else {
            return Err(CompressionError::Helix {
                reason: "a frame location reads at least one passage",
            });
        };
        let mut readings = Vec::with_capacity(self.frames.len());
        for helix in &self.frames {
            if classes as u64 > helix.cells() {
                readings.push((
                    helix.clone(),
                    FrameReading::Narrow {
                        classes,
                        cells: helix.cells(),
                    },
                ));
                continue;
            }
            let location = TransportLocation::locate(helix.clone(), classes, passages)?;
            let reading = match location.fibre() {
                TransportFibre::Empty => FrameReading::Empty,
                TransportFibre::Plural { classes: gauge } => {
                    FrameReading::Plural { classes: gauge }
                }
                TransportFibre::One(transport) => {
                    let keys = transport.keys(first);
                    let closed = keys
                        .first()
                        .and_then(|&key| transport.cycle(key).map(|cycle| (key, cycle)));
                    match closed {
                        Some((key, cycle)) => FrameReading::One(FrameCycle {
                            location,
                            transport,
                            keys,
                            key,
                            cycle,
                        }),
                        None => FrameReading::Open(transport),
                    }
                }
            };
            readings.push((helix.clone(), reading));
        }
        Ok(FrameLocation { classes, readings })
    }
}

/// [definition] **A carrying frame's location**: the location whose fibre is one gauge class (the
/// input of `PassageChart::located`), its located transport, the keys that regenerate the first
/// passage, the least of them and its closed cycle.
#[derive(Clone, Debug)]
pub struct FrameCycle {
    location: TransportLocation,
    transport: LocatedTransport,
    keys: Vec<u64>,
    key: u64,
    cycle: Cycle,
}

impl FrameCycle {
    /// The location (loop closure over the read set), whose one gauge class founds the chart.
    pub fn location(&self) -> &TransportLocation {
        &self.location
    }

    /// The located transport: the fibre's one member.
    pub fn transport(&self) -> &LocatedTransport {
        &self.transport
    }

    /// The keys whose regenerated passage is the first passage read.
    pub fn keys(&self) -> &[u64] {
        &self.keys
    }

    /// The least such key, where the cycle is read.
    pub fn key(&self) -> u64 {
        self.key
    }

    /// The key's closed cycle: its length and its whole windings.
    pub fn cycle(&self) -> Cycle {
        self.cycle
    }
}

/// [definition] **One frame's reading of a passage** (module header, the table).
#[derive(Clone, Debug)]
pub enum FrameReading {
    /// The classes exceed the receiving ring's cells.
    Narrow { classes: usize, cells: u64 },
    /// No survivor.
    Empty,
    /// Several gauge classes.
    Plural { classes: usize },
    /// One gauge class whose least key's lift is on no closed cycle.
    Open(LocatedTransport),
    /// One gauge class with its key's closed cycle.
    One(FrameCycle),
}

/// [definition] **The readings counted**: how the family's frames read the passage.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FrameTally {
    pub narrow: usize,
    pub empty: usize,
    pub plural: usize,
    pub open: usize,
    pub one: usize,
}

/// [definition] **A period located**: the cycle length every carrying frame read, and each such
/// frame's ring periods with the cycle's winding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocatedPeriod {
    pub length: u64,
    pub frames: Vec<(Vec<u64>, u64)>,
}

/// Why no period is located. Typed; a period is never invented.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum FrameRefusal {
    /// No frame of the family carries the passage as one gauge class with a closed cycle.
    #[error("no frame of the family carries the passage as one closed gauge class ({tally:?})")]
    Unlocated { tally: FrameTally },
    /// The carrying frames read different cycles.
    #[error("the carrying frames read different cycles: {lengths:?}")]
    Disagree { lengths: Vec<u64> },
}

/// [definition] **A passage located on a frame family** (module header): the classes read and each
/// frame's typed reading, in the family's order.
#[derive(Clone, Debug)]
pub struct FrameLocation {
    classes: usize,
    readings: Vec<(CarryHelix, FrameReading)>,
}

impl FrameLocation {
    /// The classes the passage was read over.
    pub fn classes(&self) -> usize {
        self.classes
    }

    /// Each frame with its reading.
    pub fn readings(&self) -> &[(CarryHelix, FrameReading)] {
        &self.readings
    }

    /// The frames that carry the passage with a closed cycle.
    pub fn carrying(&self) -> impl Iterator<Item = (&CarryHelix, &FrameCycle)> + '_ {
        self.readings
            .iter()
            .filter_map(|(helix, reading)| match reading {
                FrameReading::One(cycle) => Some((helix, cycle)),
                _ => None,
            })
    }

    /// How the frames read the passage, counted.
    pub fn tally(&self) -> FrameTally {
        let mut tally = FrameTally {
            narrow: 0,
            empty: 0,
            plural: 0,
            open: 0,
            one: 0,
        };
        for (_, reading) in &self.readings {
            match reading {
                FrameReading::Narrow { .. } => tally.narrow += 1,
                FrameReading::Empty => tally.empty += 1,
                FrameReading::Plural { .. } => tally.plural += 1,
                FrameReading::Open(_) => tally.open += 1,
                FrameReading::One(_) => tally.one += 1,
            }
        }
        tally
    }

    /// **The located period** (module header): the one cycle length the carrying frames read.
    /// Refused with [`FrameRefusal::Unlocated`] when no frame carries the passage, and with
    /// [`FrameRefusal::Disagree`] when the carrying frames read different cycles.
    pub fn period(&self) -> Result<LocatedPeriod, FrameRefusal> {
        let mut lengths: Vec<u64> = self
            .carrying()
            .map(|(_, carrying)| carrying.cycle().length)
            .collect();
        lengths.sort_unstable();
        lengths.dedup();
        match lengths.len() {
            0 => Err(FrameRefusal::Unlocated {
                tally: self.tally(),
            }),
            1 => Ok(LocatedPeriod {
                length: lengths[0],
                frames: self
                    .carrying()
                    .map(|(helix, carrying)| (helix.periods().to_vec(), carrying.cycle().winding))
                    .collect(),
            }),
            _ => Err(FrameRefusal::Disagree { lengths }),
        }
    }
}
