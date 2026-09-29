//! **Holonic Encoding: a passage chart's minimal realization, founded by closing the receiving
//! forms under the field's own transports** (THE_REBUILD U6; the
//! [pin](../../../../research/records/2026-09-29_HOLONIC_ENCODING_FOR_THE_FIELD_PINNED_BEFORE_ITS_RUN.md);
//! `docs/HNN_FORMULA.md`, "Holonic Encoding"; the September 11
//! [encoding record](../../../../research/records/2026-09-11_HOLONIC_ENCODING_RETAINS_TRANSFORMATION_GRAIN_ACROSS_MODALITIES.md);
//! Lean `HNN/Encoding`; #73, #63).
//!
//! [definition; agent-inferred] **The passage chart** ([`PassageChart`]): a finite chart `ℚ^n`,
//! the admitted transports `T_a` (known: made of the field's own objects, the rings' rotor steps,
//! their reflectors and selective clock), the injection `B e_u` of each exterior cell `u`, the
//! receiving forms `ρ_c` (the coupling the decoder reads) and the openings `x_0`.
//!
//! [proved-derived; formal-checked for the laws, `HNN/Encoding` and `Compression/Landmark/Context/Birth`]
//! **The founding** ([`Encoding::found`]) is the minimal realization, founded twice by the one owner
//! of the closure, `receiver::population::birth::Closure` (no second copy of its algebra):
//!
//! ```text
//! R  = the least T_a-invariant span of the openings           (Closure over T_aᵀ: its "forms" are
//!                                                               the reached states r_j)
//! M_a = T_a on R's coordinates                                 (the reach closure's U_aᵀ)
//! ρ'_c(c) = ρ_c(Σ_j c_j r_j)                                   the receiving forms read on R
//! ψ_i = the least M_a*-invariant span of the ρ'                (Closure over M_a)
//! E x = (ψ_i(coordinates_R x))_i,  E T_a = U_a E,  D E = ρ,  J e_u = E B e_u
//! ```
//!
//! Its dimension is the emission's observable dimension on the reached orbit: `R` is reachable by
//! construction, and on it `E` keeps exactly what the receiving forms separate under the admitted
//! transports (the Hankel rank; the identification is owed in #62, "Birth"). Birth alone closes
//! observability on the whole chart, so its dimension can exceed the Hankel rank by forms silent on
//! the reached orbit; the reached restriction removes them.
//!
//! [definition] **Its returns.** The founded constituents ([`Constituent`]) with their ports (the
//! chart states each reads) and incidence (the constituents its transports join); `U_a`; `D`; the
//! founded injection `J`; and the **Preimage Fibre**: the reached directions `E` merges
//! ([`Encoding::fibre`]) and the exterior cells no reached state separates ([`Encoding::cells`]: the
//! cells with one founded injection share a class, and a cell whose injection lies outside the
//! reached span is unfounded). No representative is chosen.
//!
//! [definition] **The consumers' equations, checked exactly** ([`Encoding::squares`]) on every
//! reached basis state `r_j`, every admitted transport and every founded cell:
//!
//! ```text
//! D E r_j = ρ r_j                                  the static reading
//! E (T_a r_j) = U_a E r_j                          continuing conduct
//! E (T_a r_j + B e_u) = U_a E r_j + J e_u          the injection square (the moment's one-step law)
//! ```
//!
//! [definition; agent-inferred] **The field's port chart** ([`found_ports`]). On the exterior chart
//! the field knows no transport but the identity, so the founding of a passage reaches exactly the
//! passage's cells, each its own constituent, and the cells the passage never separates are one
//! plural fibre. Each constituent is **placed** on each ring at the ring's phase class at its first
//! arrival, read on the field's own selective clock while the chart is founded (the winding guide's
//! placement; a cell's port reads only the cells before its first arrival, so the chart is a causal
//! function of the founding passage). The plural fibre sits at the least port outside each ring's
//! lock: it carries no founded transport and steps no ring by its lock. No codec value enters: the
//! codec supplies the exterior alphabet and its decoder, and the rings' own clocks place what the
//! passage founds (the governing law "No catered machinery").
//!
//! [definition] The computational object is the helical pair interaction. Of the winding guide's six
//! general objects this owner touches four: the **helix** (the rings' rotor steps and the selective
//! clock, on which the source enters and constituents are placed), the **pair** (the offset moment
//! the injection square carries, through the moment chart), **faces and placement** (`D`, the
//! constituents' ports and each constituent's placement on a ring) and the **tower thread** (the
//! carry chain the selective clock reads, which the crib's chart carries across rings). The cell
//! holonomy and the tube stay attached through `Field::holarchy` and the word.
//!
//! | Lean | Rust |
//! |---|---|
//! | `Compression/Landmark/Context/Birth.{founding_intertwines, encode_reads, encode_iterate, founded_reads_iterate, silent_invariant}` | [`Encoding::found`] through `birth::Closure` |
//! | `HNN/Encoding.injection_square` | [`Encoding::squares`] (the injection square) |
//! | `HNN/Encoding.encoding_reduced_recurrence` | [`Encoding::reduced_moment`] |
//! | `HNN/Encoding.encoding_separator` | [`Encoding::fibre`], [`Encoding::separator`] |

use std::collections::BTreeMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, ToPrimitive, Zero};
use thiserror::Error;

use crate::hnn::HnnError;
use crate::hnn::field::{Current, Field, PortChart, PortChartKind, ring_digit};
use crate::holarchy::terrain::{Grating, MoireClass, TerrainError};
use crate::holon::HolonError;
use crate::holon::contact::menu::{MenuError, PortPermutation};
use crate::holon::restriction::PreimageFibre;
use crate::navigator::Navigator;
use crate::ratio::Rat;
use crate::ratio::linear::vector::{dot, matrix};
use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};
use crate::receiver::population::{BirthError, Closure, TransportBirth};

/// Every refusal of the encoding. Bad input is a typed return, never a panic.
#[derive(Debug, Error, PartialEq)]
pub enum EncodingError {
    #[error("the passage chart is not declared: {reason}")]
    Chart { reason: &'static str },
    #[error("the receiving forms read nothing on the reached orbit")]
    Blind,
    #[error("the state lies outside the reached span")]
    Unreached,
    #[error("the {square} square fails at reached state {state}")]
    Square { square: &'static str, state: usize },
    #[error(transparent)]
    Birth(#[from] BirthError),
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    #[error(transparent)]
    Holon(#[from] HolonError),
    #[error(transparent)]
    Menu(#[from] MenuError),
    /// Boxed: the HNN's refusals are wide.
    #[error(transparent)]
    Hnn(Box<HnnError>),
    /// Boxed: a terrain's refusals are wide.
    #[error(transparent)]
    Terrain(Box<TerrainError>),
}

impl From<HnnError> for EncodingError {
    fn from(error: HnnError) -> Self {
        Self::Hnn(Box::new(error))
    }
}

impl From<TerrainError> for EncodingError {
    fn from(error: TerrainError) -> Self {
        Self::Terrain(Box::new(error))
    }
}

fn chart_refusal(reason: &'static str) -> EncodingError {
    EncodingError::Chart { reason }
}

/// `e_i ∈ ℚ^n`.
fn unit(n: usize, i: usize) -> Vec<Rat> {
    let mut vector = vec![Rat::zero(); n];
    vector[i] = Rat::one();
    vector
}

/// **An independent subset of the vectors, in order**: the pivot columns of the matrix whose
/// columns they are (`ExactRatMatrix::image_basis`); zero vectors are dropped.
fn independent(chart: usize, vectors: &[Vec<Rat>]) -> Result<Vec<Vec<Rat>>, EncodingError> {
    let nonzero: Vec<&Vec<Rat>> = vectors
        .iter()
        .filter(|vector| vector.iter().any(|value| !value.is_zero()))
        .collect();
    if nonzero.is_empty() {
        return Ok(Vec::new());
    }
    let columns = matrix(chart, nonzero.len(), |row, column| nonzero[column][row].clone())?;
    Ok(columns.image_basis()?)
}

/// **Close an independent family** under the adjoints of `transports` with the one owner of the
/// closure: the family's last member is the separator, the rest are held (independent, so the
/// separator lies outside their span).
fn close(
    chart: usize,
    transports: &[ExactRatMatrix],
    mut family: Vec<Vec<Rat>>,
) -> Result<Closure, EncodingError> {
    let separator = family
        .pop()
        .ok_or_else(|| chart_refusal("the family to close is empty"))?;
    Ok(Closure::found(chart, transports, &family, &separator)?)
}

// -------------------------------------------------------------------------------------------
// the passage chart

/// [definition] **A passage chart** (module header): the chart's dimension, the admitted
/// transports `T_a` (`n × n`), the injection `B e_u` of each exterior cell (`n`-vectors, one per
/// cell; empty for an autonomous chart), the receiving forms `ρ_c` and the openings `x_0`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassageChart {
    chart: usize,
    transports: Vec<ExactRatMatrix>,
    injection: Vec<Vec<Rat>>,
    coupling: Vec<Vec<Rat>>,
    openings: Vec<Vec<Rat>>,
}

impl PassageChart {
    /// **Declare a passage chart**; refused unless the chart has a dimension, at least one
    /// admitted transport is a map of it, and every injection column, receiving form and opening
    /// reads it.
    pub fn new(
        chart: usize,
        transports: Vec<ExactRatMatrix>,
        injection: Vec<Vec<Rat>>,
        coupling: Vec<Vec<Rat>>,
        openings: Vec<Vec<Rat>>,
    ) -> Result<Self, EncodingError> {
        if chart == 0 {
            return Err(chart_refusal("it declares no dimension"));
        }
        if transports.is_empty()
            || transports
                .iter()
                .any(|transport| transport.rows() != chart || transport.columns() != chart)
        {
            return Err(chart_refusal(
                "it admits at least one transport, each a map of the chart",
            ));
        }
        if coupling.is_empty()
            || injection
                .iter()
                .chain(&coupling)
                .chain(&openings)
                .any(|vector| vector.len() != chart)
        {
            return Err(chart_refusal(
                "the receiving forms read at least one class, and every vector reads the chart",
            ));
        }
        Ok(Self {
            chart,
            transports,
            injection,
            coupling,
            openings,
        })
    }

    /// The chart's dimension `n`.
    pub fn chart(&self) -> usize {
        self.chart
    }

    /// The admitted transports `T_a`.
    pub fn transports(&self) -> &[ExactRatMatrix] {
        &self.transports
    }

    /// The injection columns `B e_u`.
    pub fn injection(&self) -> &[Vec<Rat>] {
        &self.injection
    }

    /// The receiving forms `ρ_c`.
    pub fn coupling(&self) -> &[Vec<Rat>] {
        &self.coupling
    }

    /// The openings `x_0`.
    pub fn openings(&self) -> &[Vec<Rat>] {
        &self.openings
    }

    /// **The moiré's chart** (the gratings' joint port torus, its tick and the declared class's
    /// coupling, read through `birth::TransportBirth::moire`), opened at the gratings' phases.
    pub fn moire(gratings: &[Grating], class: MoireClass) -> Result<Self, EncodingError> {
        let rates: Vec<(u64, u64)> = gratings
            .iter()
            .map(|grating| (grating.numerator(), grating.denominator()))
            .collect();
        let birth = TransportBirth::moire(&rates, class, 0)?;
        // Ring 0 least significant, as the chart's own index reads the torus.
        let index = gratings.iter().rev().fold(0usize, |state, grating| {
            state * grating.denominator() as usize + grating.phase() as usize
        });
        Self::new(
            birth.chart(),
            birth.transports().to_vec(),
            Vec::new(),
            birth.coupling().to_vec(),
            vec![unit(birth.chart(), index)],
        )
    }

    /// **A copy terrain's chart**: a closing rotor ring (`navigator::Navigator::rotor`) of period
    /// `L = stored.len()` whose nodes hold cells of an exterior chart of `alphabet` codes, node `j`
    /// holding `stored[j]`. Its tick is the rotor's map: node `j` receives the cell of node `P(j) =
    /// j + 1`, so the reading node `0` reads `stored[t mod L]` at tick `t`. Its chart is
    /// `ℚ^L ⊗ ℚ^|A|`, node-major.
    pub fn copy(stored: &[usize], alphabet: usize) -> Result<Self, EncodingError> {
        let period = stored.len();
        if alphabet == 0 || stored.iter().any(|&cell| cell >= alphabet) {
            return Err(chart_refusal(
                "a copy ring stores cells of its exterior chart",
            ));
        }
        let rotor = Navigator::rotor(period as u64, 0, Rat::one())?;
        let step = rotor
            .map()
            .ok_or_else(|| chart_refusal("a rotor's transport is its port map"))?
            .clone();
        let chart = period * alphabet;
        let images = step.images();
        let tick = matrix(chart, chart, |row, column| {
            let (node, cell) = (row / alphabet, row % alphabet);
            let (from, read) = (column / alphabet, column % alphabet);
            if read == cell && from == images[node] {
                Rat::one()
            } else {
                Rat::zero()
            }
        })?;
        let coupling = (0..alphabet).map(|cell| unit(chart, cell)).collect();
        let mut opening = vec![Rat::zero(); chart];
        for (node, &cell) in stored.iter().enumerate() {
            opening[node * alphabet + cell] = Rat::one();
        }
        Self::new(chart, vec![tick], Vec::new(), coupling, vec![opening])
    }

    /// **The rotor crib's chart on ring `ring`** of a declared field
    /// (`holarchy::terrain::rotor_crib`'s machine): a state is the current cell `x` (a port of the
    /// ring) and the phase classes of rings `0 … ring`, which carry the ring's own position and the
    /// carries into it. Its tick produces the next cell by the ring's reflector machine
    /// `S⁻¹ W_(key + taken) S x` (`compression::ReflectorMachine::stage`) and steps the phases by
    /// the field's selective law on `x` (`Field::selective_step`). The coupling reads `x`.
    pub fn crib(
        field: &Field,
        ring: usize,
        key: u64,
        board: &PortPermutation,
        configurations: &[u64],
        start: usize,
    ) -> Result<Self, EncodingError> {
        let rings = field.rings();
        if ring >= rings.len() || configurations.len() != rings.len() {
            return Err(chart_refusal(
                "a crib reads a ring of the field under a configuration of every ring",
            ));
        }
        let machine = field.ring(ring).machine()?;
        let d = field.ring(ring).period() as usize;
        if start >= d || d > field.alphabet() {
            return Err(chart_refusal(
                "a crib's cells are ports of its ring, inside the exterior chart",
            ));
        }
        let periods: Vec<usize> = (0..=ring)
            .map(|h| field.ring(h).period() as usize)
            .collect();
        let states: usize = d * periods.iter().product::<usize>();
        let index = |x: usize, phases: &[usize]| -> usize {
            x + d
                * phases
                    .iter()
                    .zip(&periods)
                    .rev()
                    .fold(0usize, |state, (&phase, &period)| state * period + phase)
        };
        let decode = |mut state: usize| -> (usize, Vec<usize>) {
            let x = state % d;
            state /= d;
            let phases = periods
                .iter()
                .map(|&period| {
                    let phase = state % period;
                    state /= period;
                    phase
                })
                .collect();
            (x, phases)
        };
        let configuration = |h: usize| (configurations[h] % periods[h] as u64) as usize;
        let inverse = board.inverse();
        let mut tick = vec![vec![Rat::zero(); states]; states];
        for state in 0..states {
            let (x, phases) = decode(state);
            // The stage's position: the key plus the ring's ticks since the configuration.
            let taken = (phases[ring] + d - configuration(ring)) % d;
            let stage = machine.stage(&BigUint::from(key + taken as u64))?;
            let next = inverse.apply(stage.apply(board.apply(x)?)?)?;
            let mut lift: Vec<BigInt> = (0..rings.len())
                .map(|h| BigInt::from(if h <= ring { phases[h] } else { 0 }))
                .collect();
            field.selective_step(&mut lift, x)?;
            let stepped: Vec<usize> = (0..=ring)
                .map(|h| {
                    (&lift[h] % BigInt::from(periods[h]))
                        .to_usize()
                        .expect("a phase class below its period")
                })
                .collect();
            tick[index(next, &stepped)][state] = Rat::one();
        }
        let tick = ExactRatMatrix::shaped(states, states, tick)?;
        let coupling = (0..d)
            .map(|cell| {
                (0..states)
                    .map(|state| {
                        if decode(state).0 == cell {
                            Rat::one()
                        } else {
                            Rat::zero()
                        }
                    })
                    .collect()
            })
            .collect();
        let opening_phases: Vec<usize> = (0..=ring).map(configuration).collect();
        Self::new(
            states,
            vec![tick],
            Vec::new(),
            coupling,
            vec![unit(states, index(start, &opening_phases))],
        )
    }

    /// **A source ring's moment chart** (`hnn::moment`): the rotating-frame counts
    /// `m[j, x]` of the cells `x` that arrived `j` ticks of ring `ring`'s clock ago, `ℚ^(d_g) ⊗
    /// ℚ^|A|`. Its admitted transports are the rotor's advances by `0`, `1` and `2` ticks (a cell
    /// steps a ring by its lock and one carry at most, Lean `HNN/Moment.advance_le_two`); a cell
    /// enters at node `0`, `B e_x = e_0 ⊗ e_x`, so the one-step law is `m′ = P^t m + B e_x` (the
    /// source moment's `moment (l ++ [u]) = U (moment l) + I E(u)`). The coupling reads the
    /// classes at node `0`; the openings are the injections.
    pub fn moment(field: &Field, ring: usize) -> Result<Self, EncodingError> {
        let d = field
            .rings()
            .get(ring)
            .ok_or_else(|| chart_refusal("the moment's ring is a ring of the field"))?
            .period() as usize;
        let a = field.alphabet();
        let chart = d * a;
        let advance = |ticks: usize| {
            matrix(chart, chart, |row, column| {
                let (node, cell) = (row / a, row % a);
                let (from, read) = (column / a, column % a);
                if read == cell && node == (from + ticks) % d {
                    Rat::one()
                } else {
                    Rat::zero()
                }
            })
        };
        let transports = (0..3).map(advance).collect::<Result<Vec<_>, _>>()?;
        let injection: Vec<Vec<Rat>> = (0..a).map(|cell| unit(chart, cell)).collect();
        let coupling = (0..a).map(|cell| unit(chart, cell)).collect();
        Self::new(chart, transports, injection.clone(), coupling, injection)
    }

    /// **The exterior chart of a founding passage** ([`found_ports`]): `ℚ^|A|`, the identity its only
    /// transport (the field knows no transport on the exterior chart), each cell injected as its
    /// one-hot, read by its class, opened at the cells the passage reaches in first-arrival order.
    pub fn exterior(alphabet: usize, arrivals: &[usize]) -> Result<Self, EncodingError> {
        if arrivals.iter().any(|&cell| cell >= alphabet) {
            return Err(chart_refusal("a reached cell lies inside the exterior chart"));
        }
        let cells: Vec<Vec<Rat>> = (0..alphabet).map(|cell| unit(alphabet, cell)).collect();
        Self::new(
            alphabet,
            vec![ExactRatMatrix::identity(alphabet)?],
            cells.clone(),
            cells,
            arrivals.iter().map(|&cell| unit(alphabet, cell)).collect(),
        )
    }
}

// -------------------------------------------------------------------------------------------
// the encoding

/// [definition] **One founded constituent** (module header): its index among the founded forms,
/// its ports (the chart states it reads: the supports of the reached states its form weighs) and
/// its incidence (`(a, j)` for every constituent `j` that `U_a` joins to it, `U_(a,ij) ≠ 0`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constituent {
    pub index: usize,
    pub ports: Vec<usize>,
    pub incidence: Vec<(usize, usize)>,
}

/// [definition] **What the squares' check read** ([`Encoding::squares`]): the reached states, the
/// admitted transports and the founded cells over which every square held exactly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Squares {
    pub states: usize,
    pub transports: usize,
    pub cells: usize,
}

/// [definition] **The founded encoding** (module header): the reach closure (the reached states
/// `r_j`), the observe closure (the founded forms `ψ_i` on `R`'s coordinates), `D`, `U_a`, the
/// transports on `R`'s coordinates `M_a`, the founded injection `J`, and the left inverse that reads
/// a chart state's coordinates on `R`.
#[derive(Clone, Debug, PartialEq)]
pub struct Encoding {
    chart: usize,
    reach: Closure,
    observe: Closure,
    readout: ExactRatMatrix,
    transports: Vec<ExactRatMatrix>,
    reached_transports: Vec<ExactRatMatrix>,
    injection: Vec<Option<Vec<Rat>>>,
    pivots: Vec<usize>,
    left: ExactRatMatrix,
}

impl Encoding {
    /// **Found the minimal realization of a passage chart** (module header): reach, then observe,
    /// each by `birth::Closure`; refused when the openings reach nothing or the receiving forms read
    /// nothing on the reached span.
    pub fn found(passage: &PassageChart) -> Result<Self, EncodingError> {
        let n = passage.chart;
        let openings = independent(n, &passage.openings)?;
        if openings.is_empty() {
            return Err(chart_refusal("the openings reach nothing"));
        }
        let transposed = passage
            .transports
            .iter()
            .map(ExactRatMatrix::transpose)
            .collect::<Result<Vec<_>, _>>()?;
        // The reached span: the openings closed under T_a (the closure's adjoint of T_aᵀ is T_a).
        let reach = close(n, &transposed, openings)?;
        let k = reach.dimension();
        // T_a on R's coordinates: T_a r_i = Σ_j U_(a,ij) r_j, so c′ = U_aᵀ c.
        let reached_transports = (0..passage.transports.len())
            .map(|a| Ok(reach.transport(a)?.transpose()?))
            .collect::<Result<Vec<_>, EncodingError>>()?;
        let restricted: Vec<Vec<Rat>> = passage
            .coupling
            .iter()
            .map(|form| reach.forms().iter().map(|state| dot(form, state)).collect())
            .collect();
        let forms = independent(k, &restricted)?;
        if forms.is_empty() {
            return Err(EncodingError::Blind);
        }
        let observe = close(k, &reached_transports, forms)?;
        let readout = observe.readout(&restricted)?;
        let transports = (0..passage.transports.len())
            .map(|a| observe.transport(a))
            .collect::<Result<Vec<_>, _>>()?;
        // The left inverse on R: k independent coordinates of the reached states.
        let states = ExactRatMatrix::new(reach.forms().to_vec())?;
        let pivots = states.rank_factorization()?.pivot_columns;
        let square = matrix(k, k, |row, column| {
            reach.forms()[column][pivots[row]].clone()
        })?;
        let left = square.inverse()?;
        let mut encoding = Self {
            chart: n,
            reach,
            observe,
            readout,
            transports,
            reached_transports,
            injection: Vec::new(),
            pivots,
            left,
        };
        encoding.injection = passage
            .injection
            .iter()
            .map(|column| match encoding.encode(column) {
                Ok(encoded) => Ok(Some(encoded)),
                Err(EncodingError::Unreached) => Ok(None),
                Err(other) => Err(other),
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(encoding)
    }

    /// The chart's dimension `n`.
    pub fn chart(&self) -> usize {
        self.chart
    }

    /// `dim R`, the reached span's dimension.
    pub fn reached(&self) -> usize {
        self.reach.dimension()
    }

    /// **The founded dimension**: the minimal realization's, `dim` of the founded forms on `R`.
    pub fn dimension(&self) -> usize {
        self.observe.dimension()
    }

    /// The reached states `r_j`, a basis of `R` (the reach closure's, in rung order).
    pub fn reached_states(&self) -> &[Vec<Rat>] {
        self.reach.forms()
    }

    /// The founded forms `ψ_i` on `R`'s coordinates.
    pub fn forms(&self) -> &[Vec<Rat>] {
        self.observe.forms()
    }

    /// The reach and observe closures' rungs (`dim` at each rung, from the opening).
    pub fn rungs(&self) -> (&[usize], &[usize]) {
        (self.reach.rungs(), self.observe.rungs())
    }

    /// **`U_a`**, the founded transport of admitted transport `a`.
    pub fn transport(&self, a: usize) -> Option<&ExactRatMatrix> {
        self.transports.get(a)
    }

    /// **`D`**, with `D E = ρ` on `R`.
    pub fn readout(&self) -> &ExactRatMatrix {
        &self.readout
    }

    /// **`J e_u = E B e_u`**, the founded injection of exterior cell `u`; `None` where `B e_u` lies
    /// outside the reached span (the cell is unfounded).
    pub fn injection(&self, cell: usize) -> Option<&[Rat]> {
        self.injection.get(cell).and_then(|column| column.as_deref())
    }

    /// **A chart state's coordinates on `R`**: `c` with `x = Σ_j c_j r_j`, read by the left inverse
    /// on `R`'s pivot coordinates and checked by reconstructing `x` exactly; refused outside `R`.
    pub fn coordinates(&self, state: &[Rat]) -> Result<Vec<Rat>, EncodingError> {
        if state.len() != self.chart {
            return Err(chart_refusal("a state reads the chart"));
        }
        let picked: Vec<Rat> = self.pivots.iter().map(|&p| state[p].clone()).collect();
        let coordinates = self.left.apply(&picked)?;
        let mut rebuilt = vec![Rat::zero(); self.chart];
        for (coefficient, basis) in coordinates.iter().zip(self.reach.forms()) {
            if coefficient.is_zero() {
                continue;
            }
            for (entry, value) in rebuilt.iter_mut().zip(basis) {
                if !value.is_zero() {
                    *entry += coefficient * value;
                }
            }
        }
        if rebuilt != state {
            return Err(EncodingError::Unreached);
        }
        Ok(coordinates)
    }

    /// **`E x`** for a reached chart state; refused outside `R`.
    pub fn encode(&self, state: &[Rat]) -> Result<Vec<Rat>, EncodingError> {
        let coordinates = self.coordinates(state)?;
        Ok(self.observe.encode(&coordinates)?)
    }

    /// **The founded constituents** (module header): each founded form with its ports and incidence.
    pub fn constituents(&self) -> Vec<Constituent> {
        let states = self.reach.forms();
        self.observe
            .forms()
            .iter()
            .enumerate()
            .map(|(index, form)| {
                let mut ports: Vec<usize> = form
                    .iter()
                    .zip(states)
                    .filter(|(weight, _)| !weight.is_zero())
                    .flat_map(|(_, state)| {
                        state
                            .iter()
                            .enumerate()
                            .filter(|(_, value)| !value.is_zero())
                            .map(|(port, _)| port)
                    })
                    .collect();
                ports.sort_unstable();
                ports.dedup();
                let incidence = self
                    .transports
                    .iter()
                    .enumerate()
                    .flat_map(|(a, transport)| {
                        (0..transport.columns())
                            .filter(move |&j| {
                                !transport.get(index, j).map_or(true, |value| value.is_zero())
                            })
                            .map(move |j| (a, j))
                    })
                    .collect();
                Constituent {
                    index,
                    ports,
                    incidence,
                }
            })
            .collect()
    }

    /// **The Preimage Fibre on the reached span**: a basis of the reached directions `E` merges,
    /// `ker E ∩ R`, as chart states (empty when `E` is injective on `R`).
    pub fn fibre(&self) -> Result<Vec<Vec<Rat>>, EncodingError> {
        let forms = ExactRatMatrix::shaped(
            self.dimension(),
            self.reached(),
            self.observe.forms().to_vec(),
        )?;
        Ok(forms
            .kernel_basis()?
            .into_iter()
            .map(|coordinates| {
                let mut state = vec![Rat::zero(); self.chart];
                for (coefficient, basis) in coordinates.iter().zip(self.reach.forms()) {
                    for (entry, value) in state.iter_mut().zip(basis) {
                        *entry += coefficient * value;
                    }
                }
                state
            })
            .collect())
    }

    /// **A separator** (Lean `HNN/Encoding.encoding_separator`): for a receiving form `σ` on the
    /// chart that does not factor through `E` on `R`, a reached direction `v` with `E v = 0` and
    /// `σ v ≠ 0`; `None` when `σ` factors (it is constant on every fibre of `E` over `R`).
    pub fn separator(&self, form: &[Rat]) -> Result<Option<Vec<Rat>>, EncodingError> {
        if form.len() != self.chart {
            return Err(chart_refusal("a receiving form reads the chart"));
        }
        Ok(self
            .fibre()?
            .into_iter()
            .find(|direction| !dot(form, direction).is_zero()))
    }

    /// **The exterior cells by their founded injection** (the Preimage Fibre on the cells): each
    /// class of cells with one founded injection, in the order of the cells' codes, then the
    /// unfounded cells (`None`: no reached state separates them) as one plural fibre.
    pub fn cells(&self) -> Vec<PreimageFibre<Option<Vec<Rat>>, Vec<usize>>> {
        let mut founded: BTreeMap<Vec<Rat>, Vec<usize>> = BTreeMap::new();
        let mut order: Vec<Vec<Rat>> = Vec::new();
        let mut unfounded = Vec::new();
        for (cell, column) in self.injection.iter().enumerate() {
            match column {
                Some(encoded) => {
                    let members = founded.entry(encoded.clone()).or_default();
                    if members.is_empty() {
                        order.push(encoded.clone());
                    }
                    members.push(cell);
                }
                None => unfounded.push(cell),
            }
        }
        let mut fibres: Vec<_> = order
            .into_iter()
            .map(|encoded| {
                let members = founded.remove(&encoded).unwrap_or_default();
                PreimageFibre::new(Some(encoded), members)
            })
            .collect();
        if !unfounded.is_empty() {
            fibres.push(PreimageFibre::new(None, unfounded));
        }
        fibres
    }

    /// **The consumers' equations, checked exactly** (module header) on every reached basis state,
    /// every admitted transport and every founded cell: `D E = ρ`, `E T_a = U_a E` and the injection
    /// square. Each chart-side image is read back through [`Encoding::coordinates`], so a transport
    /// that leaves `R` is refused rather than read.
    pub fn squares(&self, passage: &PassageChart) -> Result<Squares, EncodingError> {
        if passage.chart != self.chart || passage.transports.len() != self.transports.len() {
            return Err(chart_refusal("the squares read the passage the encoding was founded on"));
        }
        let mut cells = 0;
        for (j, state) in self.reach.forms().iter().enumerate() {
            let encoded = self.encode(state)?;
            let read = self.readout.apply(&encoded)?;
            let reading: Vec<Rat> = passage.coupling.iter().map(|form| dot(form, state)).collect();
            if read != reading {
                return Err(EncodingError::Square {
                    square: "reading D E = ρ",
                    state: j,
                });
            }
            for (a, (transport, founded)) in
                passage.transports.iter().zip(&self.transports).enumerate()
            {
                let moved = transport.apply(state)?;
                let conducted = founded.apply(&encoded)?;
                if self.encode(&moved)? != conducted {
                    return Err(EncodingError::Square {
                        square: "conduct E T = U E",
                        state: j,
                    });
                }
                for (column, injected) in passage.injection.iter().zip(&self.injection) {
                    let Some(injected) = injected else {
                        continue;
                    };
                    if a == 0 && j == 0 {
                        cells += 1;
                    }
                    let driven: Vec<Rat> = moved.iter().zip(column).map(|(x, b)| x + b).collect();
                    let expected: Vec<Rat> =
                        conducted.iter().zip(injected).map(|(x, b)| x + b).collect();
                    if self.encode(&driven)? != expected {
                        return Err(EncodingError::Square {
                            square: "injection E(T x + B e_u) = U E x + J e_u",
                            state: j,
                        });
                    }
                }
            }
        }
        Ok(Squares {
            states: self.reached(),
            transports: self.transports.len(),
            cells,
        })
    }

    /// **The reduced recurrence** (Lean `HNN/Encoding.encoding_reduced_recurrence`): the encoded
    /// moment of a driven passage `(a_k, u_k)`, `z_k = U_(a_k) z_(k−1) + J e_(u_k)` from `z = 0`,
    /// run in the founded chart alone; refused at an unfounded cell.
    pub fn reduced_moment(&self, passage: &[(usize, usize)]) -> Result<Vec<Rat>, EncodingError> {
        let mut state = vec![Rat::zero(); self.dimension()];
        for &(a, cell) in passage {
            let transport = self
                .transports
                .get(a)
                .ok_or_else(|| chart_refusal("an admitted transport of the passage"))?;
            let injected = self.injection(cell).ok_or(EncodingError::Unreached)?;
            state = transport
                .apply(&state)?
                .into_iter()
                .zip(injected)
                .map(|(x, b)| x + b)
                .collect();
        }
        Ok(state)
    }

    /// The transports on `R`'s coordinates, `M_a`.
    pub fn reached_transports(&self) -> &[ExactRatMatrix] {
        &self.reached_transports
    }
}

// -------------------------------------------------------------------------------------------
// the port chart

/// [definition] **A founded port chart with its receipt** ([`found_ports`]): the chart, the
/// exterior encoding it read, the constituents in first-arrival order (each a class of exterior
/// cells), the plural fibre, and each constituent's placement on every ring.
#[derive(Clone, Debug, PartialEq)]
pub struct FoundedPorts {
    pub chart: PortChart,
    pub encoding: Encoding,
    pub constituents: Vec<Vec<usize>>,
    pub fibre: Vec<usize>,
    pub placements: Vec<Vec<usize>>,
    /// The constituent of each exterior cell; `None` in the plural fibre.
    pub constituent_of: Vec<Option<usize>>,
}

impl FoundedPorts {
    /// **The recurrence of each constituent** over a passage: its cells' count, in first-arrival
    /// order, and the plural fibre's count last.
    pub fn recurrence(&self, passage: &[usize]) -> Vec<u64> {
        let mut counts = vec![0u64; self.constituents.len() + 1];
        for &cell in passage {
            match self.constituent_of.get(cell).copied().flatten() {
                Some(constituent) => counts[constituent] += 1,
                None => counts[self.constituents.len()] += 1,
            }
        }
        counts
    }
}

/// **The field's founded port chart on a founding passage** (module header, "The field's port
/// chart"): the exterior chart's founding ([`PassageChart::exterior`], [`Encoding::found`]); each
/// constituent placed on every ring at the ring's phase class at its first arrival, read on the
/// field's own selective clock (`Field::step_at_ports`) from its declared initial configuration
/// while the chart is founded; the plural fibre at the least port outside each ring's lock.
pub fn found_ports(field: &Field, passage: &[usize]) -> Result<FoundedPorts, EncodingError> {
    let alphabet = field.alphabet();
    let mut arrivals = Vec::new();
    let mut seen = vec![false; alphabet];
    for &cell in passage {
        if cell >= alphabet {
            return Err(HnnError::CellOutside {
                code: cell,
                alphabet,
            }
            .into());
        }
        if !seen[cell] {
            seen[cell] = true;
            arrivals.push(cell);
        }
    }
    if arrivals.is_empty() {
        return Err(chart_refusal("the founding passage reaches no cell"));
    }
    let chart = PassageChart::exterior(alphabet, &arrivals)?;
    let encoding = Encoding::found(&chart)?;
    // The constituents: the cells of one founded injection, ordered by their first arrival.
    let mut constituent_of: Vec<Option<usize>> = vec![None; alphabet];
    let mut constituents: Vec<Vec<usize>> = Vec::new();
    let mut fibre = Vec::new();
    let classes = encoding.cells();
    let mut class_of: Vec<Option<usize>> = vec![None; alphabet];
    for (index, class) in classes.iter().enumerate() {
        match &class.native {
            Some(_) => {
                for &cell in &class.members {
                    class_of[cell] = Some(index);
                }
            }
            None => fibre = class.members.clone(),
        }
    }
    let mut numbered: BTreeMap<usize, usize> = BTreeMap::new();
    for &cell in &arrivals {
        let class = class_of[cell].ok_or(EncodingError::Unreached)?;
        let next = numbered.len();
        let constituent = *numbered.entry(class).or_insert(next);
        if constituent == constituents.len() {
            constituents.push(classes[class].members.clone());
        }
        constituent_of[cell] = Some(constituent);
    }
    for (constituent, members) in constituents.iter().enumerate() {
        for &cell in members {
            constituent_of[cell] = Some(constituent);
        }
    }
    // Placement at first arrival on the field's own clock.
    let rings = field.rings();
    let mut lift: Vec<BigInt> = Current::at_rest(field).lift().to_vec();
    let mut placements: Vec<Option<Vec<usize>>> = vec![None; constituents.len()];
    for &cell in passage {
        let constituent = constituent_of[cell].ok_or(EncodingError::Unreached)?;
        if placements[constituent].is_none() {
            let phases = rings
                .iter()
                .zip(&lift)
                .map(|(ring, tau)| Ok(ring_digit(&ring.clock_at(tau)?) as usize))
                .collect::<Result<Vec<_>, HnnError>>()?;
            placements[constituent] = Some(phases);
        }
        let ports = placements[constituent]
            .as_ref()
            .expect("placed at its first arrival");
        field.step_at_ports(&mut lift, |g| ports[g])?;
    }
    let placements: Vec<Vec<usize>> = placements
        .into_iter()
        .map(|placed| placed.expect("every constituent arrives in the founding passage"))
        .collect();
    // The plural fibre: the least port outside each ring's lock (port 0 when the lock is every port).
    let dormant: Vec<usize> = rings
        .iter()
        .map(|ring| {
            (0..ring.period() as usize)
                .find(|&port| !ring.fits(port))
                .unwrap_or(0)
        })
        .collect();
    let ports: Vec<Vec<usize>> = (0..rings.len())
        .map(|g| {
            (0..alphabet)
                .map(|cell| match constituent_of[cell] {
                    Some(constituent) => placements[constituent][g],
                    None => dormant[g],
                })
                .collect()
        })
        .collect();
    let chart = PortChart::founded(
        ports,
        PortChartKind::Founded {
            passage: passage.len() as u64,
            constituents: constituents.len() as u64,
            fibre: fibre.len() as u64,
        },
    );
    Ok(FoundedPorts {
        chart,
        encoding,
        constituents,
        fibre,
        placements,
        constituent_of,
    })
}
