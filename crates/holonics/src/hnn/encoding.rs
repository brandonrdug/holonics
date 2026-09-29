//! **Holonic Encoding: a passage chart's minimal realization, founded by closing the receiving
//! forms under the passage's own transports** (THE_REBUILD U6; the
//! [pin](../../../../research/records/2026-09-29_HOLONIC_ENCODING_FOR_THE_FIELD_PINNED_BEFORE_ITS_RUN.md)
//! and the [pin of the passage's own transports](../../../../research/records/2026-09-29_THE_PASSAGES_OWN_TRANSPORTS_PINNED_BEFORE_ITS_RUNS.md);
//! `docs/HNN_FORMULA.md`, "Holonic Encoding"; the September 11
//! [encoding record](../../../../research/records/2026-09-11_HOLONIC_ENCODING_RETAINS_TRANSFORMATION_GRAIN_ACROSS_MODALITIES.md);
//! Lean `HNN/Encoding`; #73, #148, #63).
//!
//! [definition; agent-inferred] **The passage chart** ([`PassageChart`]): a finite chart `ℚ^n`,
//! its admitted transports `T_a` (known), the injection `B e_u` of each exterior cell `u`, the
//! receiving forms `ρ_c` (the coupling the decoder reads) and the openings `x_0`. The terrains'
//! charts declare the field's own objects as transports (the rings' rotor steps, their reflectors
//! and selective clock); a passage's own chart declares none ([`PassageChart::passage`]).
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
//! Its dimension is the rank of the chart's Hankel map on the reached span: `R` is reachable by
//! construction, and on it `E` merges exactly the directions every reading `ρ T_w` merges
//! (Lean `HNN/Encoding.{hankel_identification, forms_span_kernel}`). Birth alone closes
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
//! [definition; agent-inferred, U6] **The passage's own transports** ([`ContextClasses`],
//! [`PassageChart::passage`]; Brandon: "a source word is its address"). A passage's **context
//! classes** are the contexts `p` (the words ending somewhere in it) with one set of end positions,
//! reached from the opening (the empty context) by the cells' **right actions** `T_u e_p = e_(pu)`
//! (Nerode's right congruence of the passage; a closed cycle's positions are read modulo its
//! period, so its ends add no edge). The receiving forms are the one-cell continuation counts
//! `ρ_c(p) = N(pc)` in the passage, so `T_u* ρ_s = ρ_(us)`, and the founding is the passage's
//! **Hankel realization**, `E p = (N(p s_i))_i` with `E T_u = U_u E` and `D E = ρ`, its dimension the
//! rank of the count Hankel matrix `[N(ps)]`. The **unconditioned tick** `T = Σ_u T_u` (the right
//! action of any next cell, [`PassageChart::unconditioned`]) is the passage's own clock: opened at a
//! context that fixes the phase, its founding is the emission's shift realization, the rotor's.
//! No transport is declared; the passage's cells are its only data.
//!
//! [definition; agent-inferred, U6] **The charged founding** ([`found_passage`]; the second clause).
//! Founded exactly, a finite passage's realization is an index: its rank is the passage's length
//! (every position is a context class of its own prefix). So a class is kept only where it shortens
//! the charged code, by the population's laws: the reach closure's ladder from the opening, one rung
//! a cell's right action on the classes born at the rung before; each class a rung reaches is
//! **born** only when `merge_cost_mass_iff` read from the birth's side accepts it
//! (`receiver::population::birth_price`): the founding passage's KT code over the founded classes'
//! own continuations, plus the newborn's draw from the reserved mass `2^(−ℓ)`, `ℓ = 2 log₂(|A_R| + 1)`
//! (its address in the ladder: its cell among the `|A_R|` reached cells or a stop, and its own stop),
//! falls. [agent-inferred] Why this charge: it is the ladder's own prefix code, decodable without
//! the passage, and it prices a class by what it adds to the description, as the restaurant prices
//! a merge. A class not born stays in its parent's class (its Preimage Fibre). The **founded
//! machine** reads a cell from a class: the class of the cell's right action, escaping to the
//! parent where the context never met the cell, then the deepest born class containing it. No
//! vocabulary, segmentation, window, depth or frequency rank is declared: the ladder stops when a
//! rung founds nothing, and within a rung the proposal is ordered by the price's gain, never
//! accepted by it. Birth's closure then founds the machine's minimal realization, which merges the
//! classes no reading separates.
//!
//! [definition; agent-inferred] **The field's port chart** ([`found_ports`]). The founded classes
//! are the field's step codes: each is **placed** on each ring at the ring's phase class at its
//! first arrival, read on the field's own selective clock as the founded machine reads the founding
//! passage (the winding guide's placement; a class's port reads only the cells before its first
//! arrival, so the chart is a causal function of the founding passage), and a ring ticks when a
//! founded class placed at its notch recurs. The codes the passage never met are one plural fibre at
//! the least port outside each ring's lock. No codec value enters: the codec supplies the exterior
//! alphabet and its decoder (the governing law "No catered machinery").
//!
//! [definition] The computational object is the helical pair interaction. Of the winding guide's six
//! general objects this owner touches: **faces and placement** (`D`, the founded forms, each class's
//! placement on a ring), the **helix** (the transports' windings: the passage's right actions and
//! the rings' selective clock on which the founded classes are placed) and the **tower thread** (the
//! founded classes coarsening: a class not born restricts to its parent). The pair (the offset
//! moment the injection square carries), the cell holonomy and the tube stay attached through the
//! moment chart, `Field::holarchy` and the word.
//!
//! | Lean | Rust |
//! |---|---|
//! | `Compression/Landmark/Context/Birth.{founding_intertwines, encode_reads, encode_iterate, founded_reads_iterate, silent_invariant}` | [`Encoding::found`] through `birth::Closure` |
//! | `HNN/Encoding.{hankel_identification, forms_span_kernel, hankel_rank_eq}` | [`Encoding::dimension`] against the count Hankel rank (`hnn::tests::encoding`) |
//! | `HNN/Encoding.continuation_intertwines` | [`PassageChart::passage`] (`T_u* ρ_s = ρ_(us)`) |
//! | `HNN/Encoding.injection_square` | [`Encoding::squares`] (the injection square) |
//! | `HNN/Encoding.encoding_reduced_recurrence` | [`Encoding::reduced_moment`], `hnn::field::FoundedMachine` |
//! | `HNN/Encoding.encoding_separator` | [`Encoding::fibre`], [`Encoding::separator`] |
//! | `Compression/Landmark/Context/Merge.merge_cost_mass_iff` | [`found_passage`] through `receiver::population::birth_price` |

use std::collections::BTreeMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, ToPrimitive, Zero};
use thiserror::Error;

use crate::compression::landmark::context::ratio_code_length;
use crate::hnn::HnnError;
use crate::hnn::field::{Current, Field, FoundedMachine, PortChart, PortChartKind, ring_digit};
use crate::holarchy::terrain::{Grating, MoireClass, TerrainError};
use crate::holon::HolonError;
use crate::holon::contact::menu::{MenuError, PortPermutation};
use crate::holon::restriction::PreimageFibre;
use crate::navigator::Navigator;
use crate::ratio::Rat;
use crate::ratio::algebraic::ExactInterval;
use crate::ratio::linear::vector::{dot, matrix};
use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};
use crate::receiver::population::{
    BirthError, Closure, KtTables, PopulationError, TransportBirth, birth_price, partition_code,
};

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
    /// Boxed: the population's refusals are wide (the priced birth).
    #[error(transparent)]
    Population(Box<PopulationError>),
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

    /// **The passage's own chart** (module header, "The passage's own transports"): its reached
    /// context classes, each reached cell's right action `T_u e_p = e_(pu)` (a transport per reached
    /// cell, in first-arrival order), the injection `B e_u = e_[u]` (the one-cell context), the
    /// one-cell continuation counts `ρ_c(p) = N(pc)` and the opening at the empty context. Dense:
    /// for a passage whose classes are few (a closed cycle, a terrain's emission); a text passage is
    /// founded through [`found_passage`] instead.
    pub fn passage(classes: &ContextClasses) -> Result<Self, EncodingError> {
        let n = classes.len();
        let letters = classes.letters().len();
        let transports = (0..letters)
            .map(|letter| {
                matrix(n, n, |row, column| {
                    if classes.next(column, letter) == Some(row) {
                        Rat::one()
                    } else {
                        Rat::zero()
                    }
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let injection = (0..letters)
            .map(|letter| {
                let class = classes
                    .next(ContextClasses::OPENING, letter)
                    .ok_or_else(|| chart_refusal("a reached cell follows the empty context"))?;
                Ok(unit(n, class))
            })
            .collect::<Result<Vec<_>, EncodingError>>()?;
        Self::new(
            n,
            transports,
            injection,
            classes.continuations(),
            vec![unit(n, ContextClasses::OPENING)],
        )
    }

    /// **The passage's unconditioned tick** (module header): one transport `T = Σ_u T_u`, the right
    /// action of any next cell, the passage's own clock, the same receiving forms, opened at the
    /// class `opening` (a context that fixes the phase, where the tick is the emission's shift).
    pub fn unconditioned(classes: &ContextClasses, opening: usize) -> Result<Self, EncodingError> {
        let n = classes.len();
        if opening >= n {
            return Err(chart_refusal(
                "the opening is a context class of the passage",
            ));
        }
        let letters = classes.letters().len();
        let tick = matrix(n, n, |row, column| {
            let into = (0..letters)
                .filter(|&letter| classes.next(column, letter) == Some(row))
                .count();
            Rat::from_integer(BigInt::from(into))
        })?;
        Self::new(
            n,
            vec![tick],
            Vec::new(),
            classes.continuations(),
            vec![unit(n, opening)],
        )
    }

    /// **The founded machine's chart** (module header, "The charged founding"): the born classes,
    /// each reached cell's action on them (`T_u e_z = e_(machine(z, u))`), the injection at the
    /// class each cell reaches from the opening, each class's own continuation counts as the
    /// receiving forms (the founded receiver's face reads them), and the opening class.
    pub fn founded(founding: &PassageFounding) -> Result<Self, EncodingError> {
        let n = founding.classes.len();
        let letters = founding.letters.len();
        let transports = (0..letters)
            .map(|letter| {
                matrix(n, n, |row, column| {
                    if founding.next[column][letter] == row {
                        Rat::one()
                    } else {
                        Rat::zero()
                    }
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let injection = (0..letters)
            .map(|letter| unit(n, founding.next[PassageFounding::OPENING][letter]))
            .collect();
        let coupling = (0..letters)
            .map(|letter| {
                founding
                    .counts
                    .iter()
                    .map(|row| Rat::from_integer(BigInt::from(row[letter])))
                    .collect()
            })
            .collect();
        Self::new(
            n,
            transports,
            injection,
            coupling,
            vec![unit(n, PassageFounding::OPENING)],
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
// the passage's context classes

/// [definition; agent-inferred, U6] **A passage's reached context classes** (module header, "The
/// passage's own transports"): the contexts with one set of end positions, reached from the empty
/// context by the cells' right actions; each class's ends, its right action on each reached cell
/// (the class of the contexts it holds followed by the cell), and its **parent**, the least class
/// strictly containing its ends (its shorter contexts). The classes of a finite word are its index:
/// they are read while a passage is founded ([`found_passage`]) and never kept as standing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContextClasses {
    cells: Vec<usize>,
    cyclic: bool,
    letters: Vec<usize>,
    letter_of: BTreeMap<usize, usize>,
    ends: Vec<Vec<usize>>,
    next: Vec<Vec<Option<usize>>>,
    parent: Vec<Option<usize>>,
}

impl ContextClasses {
    /// The opening class, the empty context (it ends at every position).
    pub const OPENING: usize = 0;

    /// **A word's classes**: its positions `0 … n`, position `e` the context of the first `e`
    /// cells. Refused on an empty passage.
    pub fn linear(cells: &[usize]) -> Result<Self, EncodingError> {
        Self::build(cells, false)
    }

    /// **A closed cycle's classes**: its positions `ℤ/P` for the cycle's `P` cells, so its ends add
    /// no edge effects. Refused on an empty cycle.
    pub fn cycle(cells: &[usize]) -> Result<Self, EncodingError> {
        Self::build(cells, true)
    }

    /// The subset construction from the opening, each class's ends bucketed by the next cell, and
    /// the parents read from the laminar family (two classes that share an end are nested, so the
    /// classes holding one position form a chain by size).
    fn build(cells: &[usize], cyclic: bool) -> Result<Self, EncodingError> {
        if cells.is_empty() {
            return Err(chart_refusal("a passage holds at least one cell"));
        }
        let n = cells.len();
        let mut letters = Vec::new();
        let mut letter_of: BTreeMap<usize, usize> = BTreeMap::new();
        for &cell in cells {
            if let std::collections::btree_map::Entry::Vacant(entry) = letter_of.entry(cell) {
                entry.insert(letters.len());
                letters.push(cell);
            }
        }
        let read: Vec<usize> = cells.iter().map(|cell| letter_of[cell]).collect();
        let positions = if cyclic { n } else { n + 1 };
        let root: Vec<usize> = (0..positions).collect();
        let mut index: BTreeMap<Vec<usize>, usize> = BTreeMap::new();
        index.insert(root.clone(), Self::OPENING);
        let mut ends = vec![root];
        let mut next: Vec<Vec<Option<usize>>> = vec![vec![None; letters.len()]];
        let mut queue = std::collections::VecDeque::from([Self::OPENING]);
        while let Some(class) = queue.pop_front() {
            let mut buckets: Vec<Vec<usize>> = vec![Vec::new(); letters.len()];
            for &end in &ends[class] {
                if end < n {
                    buckets[read[end]].push(if cyclic { (end + 1) % n } else { end + 1 });
                }
            }
            for (letter, mut bucket) in buckets.into_iter().enumerate() {
                if bucket.is_empty() {
                    continue;
                }
                bucket.sort_unstable();
                let target = match index.get(&bucket) {
                    Some(&target) => target,
                    None => {
                        let target = ends.len();
                        index.insert(bucket.clone(), target);
                        ends.push(bucket);
                        next.push(vec![None; letters.len()]);
                        queue.push_back(target);
                        target
                    }
                };
                next[class][letter] = Some(target);
            }
        }
        let mut order: Vec<usize> = (0..ends.len()).collect();
        order.sort_by_key(|&class| (ends[class].len(), class));
        let mut chains: Vec<Vec<usize>> = vec![Vec::new(); positions];
        let mut place = vec![0usize; ends.len()];
        for &class in &order {
            place[class] = chains[ends[class][0]].len();
            for &end in &ends[class] {
                chains[end].push(class);
            }
        }
        let parent = (0..ends.len())
            .map(|class| chains[ends[class][0]].get(place[class] + 1).copied())
            .collect();
        Ok(Self {
            cells: cells.to_vec(),
            cyclic,
            letters,
            letter_of,
            ends,
            next,
            parent,
        })
    }

    /// The count of classes.
    pub fn len(&self) -> usize {
        self.ends.len()
    }

    /// Never empty: the opening is a class.
    pub fn is_empty(&self) -> bool {
        self.ends.is_empty()
    }

    /// The reached cells, in first-arrival order (the transports' index).
    pub fn letters(&self) -> &[usize] {
        &self.letters
    }

    /// The letter (first-arrival index) of an exterior cell the passage reached.
    pub fn letter(&self, cell: usize) -> Option<usize> {
        self.letter_of.get(&cell).copied()
    }

    /// **The right action** of a reached cell on a class: the class of its contexts followed by the
    /// cell, none where no context of the class is followed by it.
    pub fn next(&self, class: usize, letter: usize) -> Option<usize> {
        self.next.get(class)?.get(letter).copied().flatten()
    }

    /// The parent: the least class strictly containing the class's ends; none at the opening.
    pub fn parent(&self, class: usize) -> Option<usize> {
        self.parent.get(class).copied().flatten()
    }

    /// A class's end positions, ascending.
    pub fn ends(&self, class: usize) -> &[usize] {
        &self.ends[class]
    }

    /// **The class a word reaches from the opening**, none where the word never occurs.
    pub fn read(&self, cells: &[usize]) -> Option<usize> {
        cells.iter().try_fold(Self::OPENING, |class, &cell| {
            self.next(class, self.letter(cell)?)
        })
    }

    /// `N(pc)`: the occurrences of a class's contexts followed by a reached cell.
    pub fn count(&self, class: usize, letter: usize) -> u64 {
        self.next(class, letter)
            .map_or(0, |target| self.ends[target].len() as u64)
    }

    /// **The receiving forms** `ρ_c(p) = N(pc)`, one per reached cell, over the classes.
    pub fn continuations(&self) -> Vec<Vec<Rat>> {
        (0..self.letters.len())
            .map(|letter| {
                (0..self.len())
                    .map(|class| Rat::from_integer(BigInt::from(self.count(class, letter))))
                    .collect()
            })
            .collect()
    }

    /// **The length of a class's longest context**: its contexts extended to the left while every
    /// occurrence agrees (at most the passage's length on a cycle).
    pub fn longest(&self, class: usize) -> usize {
        let n = self.cells.len();
        let ends = &self.ends[class];
        let mut length = 0usize;
        while length < n {
            let mut agreed: Option<usize> = None;
            let mut extends = true;
            for &end in ends {
                let before = if self.cyclic {
                    (end + 2 * n - length - 1) % n
                } else if end > length {
                    end - length - 1
                } else {
                    extends = false;
                    break;
                };
                match agreed {
                    None => agreed = Some(self.cells[before]),
                    Some(cell) if cell == self.cells[before] => {}
                    Some(_) => {
                        extends = false;
                        break;
                    }
                }
            }
            if !extends {
                break;
            }
            length += 1;
        }
        length
    }

    /// **A class's longest context**, its cells (read at its first end).
    pub fn word(&self, class: usize) -> Vec<usize> {
        let length = self.longest(class);
        let n = self.cells.len();
        let end = self.ends[class][0];
        (0..length)
            .map(|k| {
                let at = if self.cyclic {
                    (end + n * (length / n + 1) - length + k) % n
                } else {
                    end - length + k
                };
                self.cells[at]
            })
            .collect()
    }

    /// **One founded machine's step** (module header, "The charged founding"): the right action of
    /// a reached cell on the class, escaping to the parent where no context of the class met it,
    /// then the deepest class `born` holds that contains it.
    fn machine_step(&self, born: &[bool], class: usize, letter: usize) -> usize {
        let mut from = class;
        let mut reached = loop {
            if let Some(target) = self.next(from, letter) {
                break target;
            }
            match self.parent(from) {
                Some(parent) => from = parent,
                // The opening meets every reached cell.
                None => break Self::OPENING,
            }
        };
        while !born[reached] {
            reached = self.parent(reached).unwrap_or(Self::OPENING);
        }
        reached
    }
}

// -------------------------------------------------------------------------------------------
// the charged founding

/// [definition] **A founded class's receipt**: its longest context (its expansion: its contexts
/// are the suffixes of it at least `shortest` cells long, a plural fibre of words with one set of
/// ends), the occurrences of its contexts in the founding passage, and the cells the founded
/// machine read at it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoundedClass {
    pub word: Vec<usize>,
    pub shortest: usize,
    pub occurrences: u64,
    pub visits: u64,
}

/// [definition] **One rung of the charged ladder**: the classes it reached, the classes born, and
/// the prices left undecided (their bounds overlapped; not born).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rung {
    pub candidates: usize,
    pub born: usize,
    pub undecided: usize,
}

/// [definition; agent-inferred, U6] **The charged founding of a passage** (module header, "The
/// charged founding"): the reached cells, the founded classes in the order the machine first reads
/// them (the opening first), the machine `next[z][u]` over the reached cells, each class's own
/// continuation counts, the ladder's rungs, the passage's KT code at the opening alone and over the
/// founded classes, the classes' description, and the born classes the final machine never read
/// (returned to their parents: nothing read them, so no code moved).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassageFounding {
    passage: usize,
    alphabet: usize,
    letters: Vec<usize>,
    letter_of: BTreeMap<usize, usize>,
    classes: Vec<FoundedClass>,
    next: Vec<Vec<usize>>,
    counts: Vec<Vec<u64>>,
    rungs: Vec<Rung>,
    code: [ExactInterval; 2],
    description: ExactInterval,
    returned: usize,
}

impl PassageFounding {
    /// The opening class (the empty context).
    pub const OPENING: usize = 0;

    /// The founding passage's length.
    pub fn passage(&self) -> usize {
        self.passage
    }

    /// The exterior chart `|A|`.
    pub fn alphabet(&self) -> usize {
        self.alphabet
    }

    /// The reached cells, in first-arrival order.
    pub fn letters(&self) -> &[usize] {
        &self.letters
    }

    /// The founded classes, the opening first.
    pub fn classes(&self) -> &[FoundedClass] {
        &self.classes
    }

    /// `next[z][u]`: the class the machine reaches from class `z` on reached cell `u`.
    pub fn next(&self) -> &[Vec<usize>] {
        &self.next
    }

    /// Each class's continuation counts over the reached cells.
    pub fn counts(&self) -> &[Vec<u64>] {
        &self.counts
    }

    /// The ladder's rungs.
    pub fn rungs(&self) -> &[Rung] {
        &self.rungs
    }

    /// `−log₂ W` of the founding passage at the opening alone and over the founded classes.
    pub fn code(&self) -> &[ExactInterval; 2] {
        &self.code
    }

    /// The founded classes' description, `(2K − 1) log₂(|A_R| + 1)` bits, enclosed.
    pub fn description(&self) -> &ExactInterval {
        &self.description
    }

    /// The born classes the final machine never read, returned to their parents.
    pub fn returned(&self) -> usize {
        self.returned
    }

    /// **One cell's founded step** from class `state`: the class it reaches, or none for a cell the
    /// founding passage never met (the plural fibre, after which the machine stands at the opening).
    /// Refused outside the exterior chart.
    pub fn step(&self, state: &mut usize, cell: usize) -> Result<Option<usize>, EncodingError> {
        if cell >= self.alphabet {
            return Err(HnnError::CellOutside {
                code: cell,
                alphabet: self.alphabet,
            }
            .into());
        }
        let row = self.next.get(*state).ok_or(EncodingError::Unreached)?;
        match self.letter_of.get(&cell) {
            Some(&letter) => {
                *state = row[letter];
                Ok(Some(*state))
            }
            None => {
                *state = Self::OPENING;
                Ok(None)
            }
        }
    }
}

/// The founded machine's run over the passage (its letters): each born class's continuation counts
/// over the reached cells and the fibre (the fibre never read here).
fn machine_counts(
    classes: &ContextClasses,
    born: &[bool],
    read: &[usize],
    symbols: usize,
) -> BTreeMap<usize, Vec<u64>> {
    let mut counts: BTreeMap<usize, Vec<u64>> = born
        .iter()
        .enumerate()
        .filter(|(_, born)| **born)
        .map(|(class, _)| (class, vec![0u64; symbols]))
        .collect();
    let mut state = ContextClasses::OPENING;
    for &letter in read {
        if let Some(row) = counts.get_mut(&state) {
            row[letter] += 1;
        }
        state = classes.machine_step(born, state, letter);
    }
    counts
}

fn blocks(counts: &BTreeMap<usize, Vec<u64>>) -> Vec<Vec<u64>> {
    counts.values().cloned().collect()
}

/// **The charged founding of a passage** (module header, "The charged founding"): the passage's
/// context classes, the reach ladder from the opening with each reached class born only where the
/// population's priced birth accepts it (`receiver::population::birth_price`, over the KT faces of
/// `|A_R| + 1` classes, the reached cells and the fibre, at the charge `(|A_R| + 1)²`), the born
/// classes the final machine never reads returned to their parents, and the machine read over the
/// founded classes. Refused on an empty passage or a cell outside the exterior chart.
pub fn found_passage(cells: &[usize], alphabet: usize) -> Result<PassageFounding, EncodingError> {
    if let Some(&cell) = cells.iter().find(|&&cell| cell >= alphabet) {
        return Err(HnnError::CellOutside {
            code: cell,
            alphabet,
        }
        .into());
    }
    let classes = ContextClasses::linear(cells)?;
    let letters = classes.letters().len();
    let symbols = letters + 1;
    let mut tables = KtTables::new(symbols).map_err(population)?;
    let charge = BigUint::from(symbols).pow(2);
    let read: Vec<usize> = cells
        .iter()
        .map(|&cell| classes.letter(cell).ok_or(EncodingError::Unreached))
        .collect::<Result<_, _>>()?;
    let mut born = vec![false; classes.len()];
    born[ContextClasses::OPENING] = true;
    let mut counts = machine_counts(&classes, &born, &read, symbols);
    let opening_code = partition_code(&mut tables, &blocks(&counts)).map_err(population)?;
    let mut rungs = Vec::new();
    let mut frontier = vec![ContextClasses::OPENING];
    while !frontier.is_empty() {
        let mut candidates: Vec<usize> = Vec::new();
        for &class in &frontier {
            for letter in 0..letters {
                if let Some(target) = classes.next(class, letter)
                    && !born[target]
                    && !candidates.contains(&target)
                {
                    candidates.push(target);
                }
            }
        }
        // First-arrival order: blind to the codec's values.
        candidates.sort_by_key(|&class| (classes.ends(class)[0], class));
        let mut undecided = 0usize;
        let mut proposed: Vec<(Rat, usize)> = Vec::new();
        let before = blocks(&counts);
        for &class in &candidates {
            born[class] = true;
            let after = machine_counts(&classes, &born, &read, symbols);
            born[class] = false;
            let price =
                birth_price(&mut tables, &before, &blocks(&after), &charge).map_err(population)?;
            match price.accepted {
                Some(true) => proposed.push((price.gain.lower, class)),
                None => undecided += 1,
                Some(false) => {}
            }
        }
        // The proposal: the largest gain first (its enclosure's lower end, exact), ties in
        // first-arrival order; each is decided again against the classes born before it.
        proposed.sort_by(|a, b| b.0.cmp(&a.0));
        let mut newborn = Vec::new();
        for (_, class) in proposed {
            let before = blocks(&counts);
            born[class] = true;
            let after = machine_counts(&classes, &born, &read, symbols);
            let price =
                birth_price(&mut tables, &before, &blocks(&after), &charge).map_err(population)?;
            match price.accepted {
                Some(true) => {
                    counts = after;
                    newborn.push(class);
                }
                None => {
                    born[class] = false;
                    undecided += 1;
                }
                Some(false) => born[class] = false,
            }
        }
        rungs.push(Rung {
            candidates: candidates.len(),
            born: newborn.len(),
            undecided,
        });
        frontier = newborn;
    }
    // A born class the final machine never reads is returned to its parent: nothing read it, so the
    // run and every other class's counts are unchanged.
    let mut returned = 0usize;
    loop {
        let unread: Vec<usize> = counts
            .iter()
            .filter(|(class, row)| {
                **class != ContextClasses::OPENING && row.iter().all(|&count| count == 0)
            })
            .map(|(class, _)| *class)
            .collect();
        if unread.is_empty() {
            break;
        }
        for class in unread {
            born[class] = false;
            returned += 1;
        }
        counts = machine_counts(&classes, &born, &read, symbols);
    }
    let code = partition_code(&mut tables, &blocks(&counts)).map_err(population)?;
    // The founded classes in the order the machine first reads them, the opening first.
    let mut order: Vec<usize> = vec![ContextClasses::OPENING];
    let mut state = ContextClasses::OPENING;
    for &letter in &read {
        state = classes.machine_step(&born, state, letter);
        if !order.contains(&state) {
            order.push(state);
        }
    }
    let index_of: BTreeMap<usize, usize> = order
        .iter()
        .enumerate()
        .map(|(index, &class)| (class, index))
        .collect();
    let next = order
        .iter()
        .map(|&class| {
            (0..letters)
                .map(|letter| index_of[&classes.machine_step(&born, class, letter)])
                .collect()
        })
        .collect();
    let founded_counts: Vec<Vec<u64>> = order
        .iter()
        .map(|class| counts[class][..letters].to_vec())
        .collect();
    let founded = order
        .iter()
        .zip(&founded_counts)
        .map(|(&class, row)| FoundedClass {
            word: classes.word(class),
            shortest: classes
                .parent(class)
                .map_or(0, |parent| classes.longest(parent) + 1),
            occurrences: classes.ends(class).len() as u64,
            visits: row.iter().sum(),
        })
        .collect::<Vec<_>>();
    let symbols_word = BigUint::from(symbols);
    let description = ratio_code_length(
        &BigUint::one(),
        &symbols_word.pow(u32::try_from(2 * order.len() - 1).unwrap_or(u32::MAX)),
    )
    .map_err(|_| chart_refusal("the founded classes' description is a positive ratio"))?;
    Ok(PassageFounding {
        passage: cells.len(),
        alphabet,
        letters: classes.letters().to_vec(),
        letter_of: classes.letter_of.clone(),
        classes: founded,
        next,
        counts: founded_counts,
        rungs,
        code: [opening_code, code],
        description,
        returned,
    })
}

fn population(error: PopulationError) -> EncodingError {
    EncodingError::Population(Box::new(error))
}

// -------------------------------------------------------------------------------------------
// the port chart

/// [definition] **A founded port chart with its receipt** ([`found_ports`]): the chart, the charged
/// founding it read, Birth's closure on the founded machine's chart, the founded classes of each
/// step code (the classes the closure keeps as one constituent), each constituent's placement on
/// every ring, the constituents the founding passage never reached (placed at the fibre's port),
/// and the exterior codes it never met (the plural fibre).
#[derive(Clone, Debug, PartialEq)]
pub struct FoundedPorts {
    pub chart: PortChart,
    pub founding: PassageFounding,
    pub encoding: Encoding,
    pub constituents: Vec<Vec<usize>>,
    pub placements: Vec<Vec<usize>>,
    pub unplaced: Vec<usize>,
    pub fibre: Vec<usize>,
}

impl FoundedPorts {
    /// **The recurrence of each step code** over a passage read from the opening: the cells that
    /// reach each constituent, the plural fibre's last.
    pub fn recurrence(&self, passage: &[usize]) -> Result<Vec<u64>, EncodingError> {
        let machine = self.chart.machine().ok_or(EncodingError::Unreached)?;
        let mut counts = vec![0u64; machine.fibre() + 1];
        let mut state = machine.opening();
        for &cell in passage {
            counts[machine.step(&mut state, cell)?] += 1;
        }
        Ok(counts)
    }
}

/// **The field's founded port chart on a founding passage** (module header, "The field's port
/// chart"): the charged founding ([`found_passage`]); Birth's closure on its machine's chart
/// ([`PassageChart::founded`], [`Encoding::found`]), whose constituents are the step codes; each
/// constituent placed on every ring at the ring's phase class at its first arrival, read on the
/// field's own selective clock (`Field::step_at_ports`) from its declared initial configuration as
/// the founded machine reads the founding passage; the fibre (and a constituent the passage never
/// reached) at the least port outside each ring's lock.
pub fn found_ports(field: &Field, passage: &[usize]) -> Result<FoundedPorts, EncodingError> {
    let alphabet = field.alphabet();
    let founding = found_passage(passage, alphabet)?;
    let chart = PassageChart::founded(&founding)?;
    let encoding = Encoding::found(&chart)?;
    // The constituents: the founded classes with one founded configuration `E e_z`, in first
    // arrival (the founded classes are in the machine's first-arrival order).
    let classes = founding.classes.len();
    let mut constituent_of = vec![0usize; classes];
    let mut images: BTreeMap<Vec<Rat>, usize> = BTreeMap::new();
    let mut constituents: Vec<Vec<usize>> = Vec::new();
    for class in 0..classes {
        let image = encoding.encode(&unit(classes, class))?;
        let next = constituents.len();
        let id = *images.entry(image).or_insert(next);
        if id == constituents.len() {
            constituents.push(Vec::new());
        }
        constituents[id].push(class);
        constituent_of[class] = id;
    }
    // The machine on the constituents: `E T_u = U_u E` carries one constituent to one.
    let fibre_step = constituents.len();
    let mut next = vec![vec![fibre_step; alphabet]; constituents.len()];
    for (id, members) in constituents.iter().enumerate() {
        for (letter, &code) in founding.letters.iter().enumerate() {
            let steps: std::collections::BTreeSet<usize> = members
                .iter()
                .map(|&class| constituent_of[founding.next[class][letter]])
                .collect();
            let step = match steps.len() {
                1 => *steps.first().expect("one step"),
                _ => {
                    return Err(chart_refusal(
                        "the classes of one constituent step to one constituent",
                    ));
                }
            };
            next[id][code] = step;
        }
    }
    let opening = constituent_of[PassageFounding::OPENING];
    let machine = FoundedMachine::new(next, opening)?;
    // Placement at first arrival on the field's own clock.
    let rings = field.rings();
    let mut lift: Vec<BigInt> = Current::at_rest(field).lift().to_vec();
    let mut placements: Vec<Option<Vec<usize>>> = vec![None; constituents.len()];
    let mut state = opening;
    for &cell in passage {
        let step = machine.step(&mut state, cell)?;
        if placements[step].is_none() {
            let phases = rings
                .iter()
                .zip(&lift)
                .map(|(ring, tau)| Ok(ring_digit(&ring.clock_at(tau)?) as usize))
                .collect::<Result<Vec<_>, HnnError>>()?;
            placements[step] = Some(phases);
        }
        let ports = placements[step]
            .clone()
            .expect("placed at its first arrival");
        field.step_at_ports(&mut lift, |g| ports[g])?;
    }
    // The fibre, and a constituent the founding passage never reached: the least port outside each
    // ring's lock (port 0 when the lock is every port).
    let dormant: Vec<usize> = rings
        .iter()
        .map(|ring| {
            (0..ring.period() as usize)
                .find(|&port| !ring.fits(port))
                .unwrap_or(0)
        })
        .collect();
    let unplaced: Vec<usize> = (0..constituents.len())
        .filter(|&id| placements[id].is_none())
        .collect();
    let placements: Vec<Vec<usize>> = placements
        .into_iter()
        .map(|placed| placed.unwrap_or_else(|| dormant.clone()))
        .collect();
    let ports: Vec<Vec<usize>> = (0..rings.len())
        .map(|g| {
            placements
                .iter()
                .map(|placed| placed[g])
                .chain(std::iter::once(dormant[g]))
                .collect()
        })
        .collect();
    let injection = machine.next()[opening].clone();
    let fibre: Vec<usize> = (0..alphabet)
        .filter(|code| !founding.letter_of.contains_key(code))
        .collect();
    let chart = PortChart::passage(
        ports,
        injection,
        machine,
        PortChartKind::Passage {
            passage: passage.len() as u64,
            classes: constituents.len() as u64,
            fibre: fibre.len() as u64,
        },
    );
    Ok(FoundedPorts {
        chart,
        founding,
        encoding,
        constituents,
        placements,
        unplaced,
        fibre,
    })
}
