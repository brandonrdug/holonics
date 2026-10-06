//! **Holonic Encoding: a passage chart's minimal realization, founded by closing the receiving
//! forms under the chart's declared transports** (THE_REBUILD U6; the
//! [pin](../../../../research/records/2026-09-29_HOLONIC_ENCODING_FOR_THE_FIELD_PINNED_BEFORE_ITS_RUN.md);
//! `docs/HNN_FORMULA.md`, "Holonic Encoding"; the September 11
//! [encoding record](../../../../research/records/2026-09-11_HOLONIC_ENCODING_RETAINS_TRANSFORMATION_GRAIN_ACROSS_MODALITIES.md);
//! Lean `HNN/Encoding`; #73, #148, #63).
//!
//! [definition; agent-inferred] **The passage chart** ([`PassageChart`]): a finite chart `ℚ^n`,
//! its admitted transports `T_a` (known), the injection `B e_u` of each exterior cell `u`, the
//! receiving forms `ρ_c` (the coupling the decoder reads) and the openings `x_0`. The terrains'
//! charts declare the field's own objects as transports (the rings' rotor steps, their reflectors
//! and selective clock, a source ring's moment chart).
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
//! [historical; retired September 29] The passage's own transports (a passage's context classes
//! under the cells' right actions), the charged founding priced by KT continuation counts, the
//! founded machine, the first-arrival placement of founded classes as the field's step codes and the
//! founded `E_0` were retired from the native path by the
//! [lessons record](../../../../research/records/2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md)
//! (§2, §4): the founding was a suffix-automaton context model priced by counts, the byte-tree line
//! re-entering through the encoding, and it bypassed deposition, Birth's own trigger and key
//! location. Their code is at `96d8940b`; the Hankel identification of a passage chart stays in Lean
//! `HNN/Encoding` as mathematics. No chart founded from a passage reaches the field: every field
//! reads its declared port chart (`hnn::field::PortChart`).
//!
//! [definition; agent-inferred, October 5; THE_MACHINE guard 9] **The one source type**
//! ([`Encoded`]). The field reads a source only as a passage of [`PortCell`]s, classes of an
//! encoding's chart that inject into every source ring's ports (`|A| ≤ d_g`, else
//! [`EncodingError::Fold`]: no residue chart), carried with `D`, the Preimage Fibre, the boundary's
//! labels and, on the located route, the located advances as the lift's digits
//! ([`LocatedAdvances`], each digit at its period's width). Only this module builds one:
//!
//! ```text
//! Encoded::identity(truth, field)       a known truth's classes as themselves; D = I, fibre ∅
//! Encoded::through(E, chart, field, x)  chart = PassageChart::located(location, read set):
//!                                       the field's own key location, one gauge class;
//!                                       squares D E = ρ, E T_c = U_c E checked; u ↦ c = λ⁻¹(u)
//! ```
//!
//! The located chart is read in the receiving cells (`LocatedTransport::chart`: `T_c e_ℓ =
//! e_(ℓ + A(λ(c)))`, `ρ_c` the indicator of cell `c`), so for every permutation `π` of the exterior
//! codes the chart, the founded encoding and the encoded cells of `π∘x` equal those of `x`, and only
//! the labels are carried, `λ_(π∘x) = π∘λ_x` [proved-derived; implemented-exact on twelve
//! permutations, `compression::keys::transport::tests`]. `Encoding::found` founds any declared chart
//! as mathematics; [`Encoded::through`] refuses every chart the field did not locate (the byte
//! chart, bare matrices, the moment chart over exterior codes) with [`EncodingError::Unencoded`],
//! so exterior data waits for its encoding.
//!
//! [definition] The computational object is the helical pair interaction. Of the winding guide's six
//! general objects this owner touches **faces and placement** (`D`, the founded forms) and the
//! **helix** (the declared transports' windings: the rings' rotor steps and selective clock). The
//! pair (the offset moment the injection square carries), the cell holonomy, the tube and the tower
//! thread stay attached through the moment chart, `Field::holarchy` and the word.
//!
//! | Lean | Rust |
//! |---|---|
//! | `Compression/Landmark/Context/Birth.{founding_intertwines, encode_reads, encode_iterate, founded_reads_iterate, silent_invariant}` | [`Encoding::found`] through `birth::Closure` |
//! | `HNN/Encoding.{hankel_identification, forms_span_kernel, hankel_rank_eq}` | [`Encoding::dimension`] against the emission's Hankel rank on the terrains' declared charts (`hnn::tests::encoding`) |
//! | `HNN/Encoding.injection_square` | [`Encoding::squares`] (the injection square) |
//! | `HNN/Encoding.encoding_reduced_recurrence` | [`Encoding::reduced_moment`] |
//! | `HNN/Encoding.encoding_separator` | [`Encoding::fibre`], [`Encoding::separator`] |
//! | the relabelling law on the located route (the chart and encoded cells of `π∘x` are those of `x`): owed (#62) | [`PassageChart::located`], [`Encoded::through`] |
//! | the identity's injection `|A| ≤ d_g` (no fold): a runtime law | [`Encoded::identity`] |

use std::collections::BTreeMap;
use std::sync::Arc;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, ToPrimitive, Zero};
use thiserror::Error;

use crate::compression::CompressionError;
use crate::compression::keys::transport::{TransportFibre, TransportLocation};
use crate::hnn::HnnError;
use crate::hnn::field::Field;
use crate::holarchy::terrain::{Grating, KnownTruth, MoireClass, TerrainError};
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
    /// THE_MACHINE guard 9: an exterior passage whose chart nothing the field located reads, or a
    /// cell the located labels do not read. Exterior data waits for its encoding.
    #[error("the exterior passage has no founded encoding")]
    Unencoded,
    /// The location's fibre holds several gauge classes: the read set does not determine the
    /// classes, so it founds no encoding.
    #[error("the located fibre holds {classes} gauge classes, not one")]
    Plural { classes: usize },
    /// The classes do not inject into a source ring's ports: `|A| > d_g` would fold them (no
    /// residue chart).
    #[error("{classes} classes fold onto source ring {ring}'s {period} ports")]
    Fold {
        classes: usize,
        ring: usize,
        period: u64,
    },
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
    /// Boxed: a compression law's refusals are wide.
    #[error(transparent)]
    Compression(Box<CompressionError>),
}

impl From<CompressionError> for EncodingError {
    fn from(error: CompressionError) -> Self {
        Self::Compression(Box::new(error))
    }
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
/// cell; empty for an autonomous chart), the receiving forms `ρ_c` and the openings `x_0`; and,
/// for a chart the field's own key location built ([`PassageChart::located`]) and for no other, what
/// located it (module header, "The one source type").
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassageChart {
    chart: usize,
    transports: Vec<ExactRatMatrix>,
    injection: Vec<Vec<Rat>>,
    coupling: Vec<Vec<Rat>>,
    openings: Vec<Vec<Rat>>,
    located: Option<LocatedChart>,
}

/// [definition] **What located a chart** ([`PassageChart::located`]): per class of the chart (a
/// cell of the receiving ring) its exterior label `λ(c)`, the boundary's decoder, and its located
/// advance's digits.
#[derive(Clone, Debug, PartialEq, Eq)]
struct LocatedChart {
    labels: Vec<Option<usize>>,
    advances: LocatedAdvances,
}

/// [definition; agent-inferred, October 5] **The located advances as the lift's digits**
/// (`compression::keys::transport`, the odometer chart): the helix's ring periods `d_g`, ring 0
/// least significant, and per class `c` (a receiving cell) the digits `a_g(c) < d_g` of
/// `A(λ(c)) = Σ_g a_g(c) ∏_(h<g) d_h`, `None` at an unlabelled cell. Read only; built only by
/// [`PassageChart::located`].
///
/// [definition; agent-inferred, October 5] **Exact width.** Each digit is held at its period's own
/// width (`u64`, the width `CarryHelix` declares its periods in), never narrowed. A ring's advance
/// under a located transport is `a_g(c) + carry_g ≤ (d_g − 1) + 1 = d_g`, and its carry out is
/// `⌊(τ_g + a_g(c) + carry_g) / d_g⌋ ∈ {0, 1}` (the odometer, `CarryHelix::step_digits`): its
/// declared bound is the ring's period, not the selective step's two ticks, so a consumer stepping
/// rings by these digits keeps each tick count, section flux and winding at least at that width.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocatedAdvances {
    periods: Vec<u64>,
    digits: Vec<Option<Vec<u64>>>,
}

impl LocatedAdvances {
    /// The helix's ring periods `d_g`, ring 0 least significant.
    pub fn periods(&self) -> &[u64] {
        &self.periods
    }

    /// The digits `a_g(c)` of a class's located advance, ring 0 first; `None` at an unlabelled cell.
    pub fn digits(&self, cell: PortCell) -> Option<&[u64]> {
        self.digits.get(cell.class).and_then(|digits| digits.as_deref())
    }
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
            located: None,
        })
    }

    /// **The located chart** (module header, "The one source type"): the field's own key location
    /// over a read set (`compression::keys::transport::TransportLocation`) founds the chart when its
    /// fibre is one gauge class. Its chart is the member's (`LocatedTransport::chart`, read in the
    /// receiving cells, never the labels), opened at each passage's least key with the fewest patches
    /// (the located code's keys); the member's labels and advances are kept as what located it.
    /// Refused with [`EncodingError::Unencoded`] on an empty fibre or a passage cell outside the
    /// location's classes, and with [`EncodingError::Plural`] on a plural fibre.
    pub fn located(
        location: &TransportLocation,
        passages: &[Vec<usize>],
    ) -> Result<Self, EncodingError> {
        let member = match location.fibre() {
            TransportFibre::Empty => return Err(EncodingError::Unencoded),
            TransportFibre::Plural { classes } => return Err(EncodingError::Plural { classes }),
            TransportFibre::One(member) => member,
        };
        if passages.is_empty() {
            return Err(chart_refusal("a located chart opens at its passages' keys"));
        }
        if passages.iter().flatten().any(|&code| code >= member.classes()) {
            return Err(EncodingError::Unencoded);
        }
        let helix = member.helix();
        let keys: Vec<u64> = passages
            .iter()
            .map(|passage| {
                (0..helix.period())
                    .min_by_key(|&key| member.patches(passage, key))
                    .expect("a helix has a lift")
            })
            .collect();
        let (n, transports, coupling, openings) = member.chart(&keys)?;
        let mut chart = Self::new(n, transports, Vec::new(), coupling, openings)?;
        let labels = member.labels().to_vec();
        let digits = labels
            .iter()
            .map(|label| label.map(|class| member.digits(class)))
            .collect();
        chart.located = Some(LocatedChart {
            labels,
            advances: LocatedAdvances {
                periods: helix.periods().to_vec(),
                digits,
            },
        });
        Ok(chart)
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
            field.step_class(&mut lift, x, None)?;
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
// the one source type

/// [definition; agent-inferred, October 5] **One occurrence's class of the encoding's chart**
/// (THE_MACHINE guard 9): a class that injects into every source ring's ports, so its port on ring
/// `g` is the class itself, `class < d_g` (no fold, no residue). It is read ([`PortCell::class`])
/// and never built outside `hnn::encoding`: no exterior code becomes one (structural, `E0451` on a
/// forged cell, `E0308` where a code is passed for a cell, `E0277` on `From<usize>`):
///
/// ```compile_fail,E0451
/// use holonics::hnn::encoding::PortCell;
/// fn forge(code: usize) -> PortCell {
///     PortCell { class: code }
/// }
/// ```
///
/// ```compile_fail,E0308
/// use holonics::hnn::encoding::PortCell;
/// fn port(_: PortCell) {}
/// fn byte(code: usize) {
///     port(code)
/// }
/// ```
///
/// ```compile_fail,E0277
/// use holonics::hnn::encoding::PortCell;
/// fn convert(code: usize) -> PortCell {
///     code.into()
/// }
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PortCell {
    class: usize,
}

impl PortCell {
    /// The class, which is its port on every source ring the encoded passage was checked against.
    pub fn class(self) -> usize {
        self.class
    }
}

/// [definition] The chart an encoded passage carries, shared by every passage one encoding produced.
#[derive(Debug, PartialEq)]
struct EncodedChart {
    classes: usize,
    sources: Vec<(usize, u64)>,
    decoder: ExactRatMatrix,
    fibre: Vec<Vec<Rat>>,
    labels: Vec<Option<usize>>,
    advances: Option<LocatedAdvances>,
    founded: Option<Founded>,
}

/// [definition; agent-inferred, October 5] **The located route's founded encoding, read at the
/// consuming calls**: the encoding `E` with its `U_a` and `D`, the located chart's receiving forms
/// `ρ_c` on `ℚ^D` and, per class, the index `a` of its transport `T_a` (the labelled cells in cell
/// order, `LocatedTransport::chart`). The field checks `D E = ρ` and `E T_a = U_a E` on the lift it
/// actually steps ([`Encoded::check_step`]).
#[derive(Debug, PartialEq)]
struct Founded {
    encoding: Encoding,
    coupling: Vec<Vec<Rat>>,
    transport: Vec<Option<usize>>,
}

/// [definition; agent-inferred, October 5] **The one source type** (THE_MACHINE guard 9; module
/// header): a passage whose every occurrence is a class of an encoding's chart ([`PortCell`]),
/// carried with the chart's class count, the source rings its classes inject into, the decoder `D`
/// and the Preimage Fibre of the encoding that produced it, the boundary's labels (class to exterior
/// code) and, on the located route, the located advances as the lift's digits. Its fields are
/// private, and only `hnn::encoding` constructs one, in two ways: [`Encoded::identity`] (a known
/// truth's declared identity) and [`Encoded::through`] (a located chart's founded encoding).
///
/// [definition] **Structural guarantees**, each a `compile_fail` doctest checked with its error code
/// (gate 1 runs them with `RUSTC_BOOTSTRAP=1`): an `Encoded` is never forged (`E0451`); an exterior
/// code list or one-hot cells are refused where `&Encoded` goes (`E0308`); no `From<usize>`,
/// `From<Vec<_>>`, `From<Faces>` or `From<Released>` exists (`E0277`), so a release is never fed back
/// as the next source cell. The refusals (the fold, an unlocated chart, an unread cell) are runtime
/// laws, each pinned by a test (`hnn::tests::encoding`, `compression::keys::transport::tests`).
///
/// ```compile_fail,E0451
/// use holonics::hnn::encoding::Encoded;
/// fn forge(other: &Encoded) -> Encoded {
///     Encoded { cells: Vec::new(), ..other.clone() }
/// }
/// ```
///
/// ```compile_fail,E0308
/// use holonics::hnn::encoding::Encoded;
/// fn ingest(_: &Encoded) {}
/// fn bytes(codes: &[usize]) {
///     ingest(codes)
/// }
/// ```
///
/// ```compile_fail,E0308
/// use holonics::hnn::encoding::Encoded;
/// use holonics::ratio::Rat;
/// fn ingest(_: &Encoded) {}
/// fn one_hot(cells: &[Vec<(usize, Rat)>]) {
///     ingest(cells)
/// }
/// ```
///
/// ```compile_fail,E0277
/// use holonics::hnn::encoding::Encoded;
/// fn convert(codes: Vec<usize>) -> Encoded {
///     codes.into()
/// }
/// ```
///
/// ```compile_fail,E0277
/// use holonics::hnn::encoding::Encoded;
/// fn convert(code: usize) -> Encoded {
///     code.into()
/// }
/// ```
///
/// ```compile_fail,E0277
/// use holonics::hnn::encoding::Encoded;
/// use holonics::hnn::ratio::Faces;
/// fn feed_back(faces: Faces) -> Encoded {
///     faces.into()
/// }
/// ```
///
/// ```compile_fail,E0277
/// use holonics::hnn::encoding::Encoded;
/// use holonics::hnn::word::Released;
/// fn feed_back(released: Released) -> Encoded {
///     released.into()
/// }
/// ```
///
/// The lawful form compiles and runs: a known truth's identity on campaign 1's field, whose source
/// ring of period 5 holds the four classes, taken where `&Encoded` goes.
///
/// ```
/// use holonics::hnn::encoding::Encoded;
/// use holonics::hnn::field::{Field, FieldDeclaration};
/// use holonics::holarchy::terrain::{CyclicLaw, KnownTruth};
/// fn ingest(encoded: &Encoded) -> usize {
///     encoded.cells().iter().map(|cell| cell.class()).max().unwrap_or(0)
/// }
/// fn main() -> Result<(), Box<dyn std::error::Error>> {
///     let field = Field::declare(FieldDeclaration::campaign_one(1 << 17))?;
///     let truth = KnownTruth::cyclic(CyclicLaw::Line, 4, 1, 2, 48)?;
///     for encoded in Encoded::identity(&truth, &field)? {
///         assert!(ingest(&encoded) < 4);
///     }
///     Ok(())
/// }
/// ```
#[derive(Clone, Debug, PartialEq)]
pub struct Encoded {
    cells: Vec<PortCell>,
    chart: Arc<EncodedChart>,
}

/// The source rings of a field with their periods; refused unless `classes ≤ d_g` on each (no fold).
fn holding_sources(field: &Field, classes: usize) -> Result<Vec<(usize, u64)>, EncodingError> {
    field
        .sources()
        .iter()
        .map(|&ring| {
            let period = field.ring(ring).period();
            if u64::try_from(classes).is_ok_and(|classes| classes <= period) {
                Ok((ring, period))
            } else {
                Err(EncodingError::Fold {
                    classes,
                    ring,
                    period,
                })
            }
        })
        .collect()
}

impl Encoded {
    /// **The declared identity encoding of a known truth** (THE_MACHINE guard 9): each passage of
    /// the terrain's own read set, each class its own port cell; `D` the identity on `ℚ^|A|`, the
    /// Preimage Fibre empty, each class's label itself, and no located advance. Refused with
    /// [`EncodingError::Fold`] unless the terrain's classes inject into every source ring's ports,
    /// `|A| ≤ d_g`: no fold, no residue. A `KnownTruth` is built only by a terrain's generator
    /// (`holarchy::terrain::known`), so a cut file never takes this route.
    pub fn identity(truth: &KnownTruth, field: &Field) -> Result<Vec<Self>, EncodingError> {
        let classes = truth.classes();
        let sources = holding_sources(field, classes)?;
        let chart = Arc::new(EncodedChart {
            classes,
            sources,
            decoder: ExactRatMatrix::identity(classes)?,
            fibre: Vec::new(),
            labels: (0..classes).map(Some).collect(),
            advances: None,
            founded: None,
        });
        Ok(truth
            .passages()
            .iter()
            .map(|passage| Self {
                cells: passage.iter().map(|&class| PortCell { class }).collect(),
                chart: Arc::clone(&chart),
            })
            .collect())
    }

    /// **Exterior passages through a founded encoding** (THE_MACHINE guard 9): the chart must be
    /// one the field's own key location built ([`PassageChart::located`]) and the encoding's squares
    /// `D E = ρ`, `E T_c = U_c E` must hold on every reached state ([`Encoding::squares`]). Each
    /// occurrence's code `u` becomes the class `c = λ⁻¹(u)` the located labels read it at, a cell of
    /// the receiving ring; `D` is the encoding's readout and the Preimage Fibre its merged reached
    /// directions ([`Encoding::fibre`]); the located advances ride along as the lift's digits.
    /// Refused with [`EncodingError::Unencoded`] when the chart was not located (the byte chart, a
    /// declared chart, a terrain's chart) or a code is read by no label; with
    /// [`EncodingError::Fold`] unless the chart's classes inject into every source ring's ports.
    ///
    /// [proved-derived; agent-inferred, October 5] **Relabelling.** The located chart is read in the
    /// receiving cells (`LocatedTransport::chart`), so for every permutation `π` of the exterior
    /// codes, the encoding of `π∘x` equals the encoding of `x`, its encoded cells are equal, and only
    /// the labels are carried, `λ_(π∘x) = π∘λ_x`; the located code length is unchanged
    /// (`compression::keys::transport::tests`, the located route).
    pub fn through(
        encoding: &Encoding,
        chart: &PassageChart,
        field: &Field,
        passages: &[Vec<usize>],
    ) -> Result<Vec<Self>, EncodingError> {
        let located = chart.located.as_ref().ok_or(EncodingError::Unencoded)?;
        encoding.squares(chart)?;
        let classes = located.labels.len();
        let sources = holding_sources(field, classes)?;
        let class_of: BTreeMap<usize, usize> = located
            .labels
            .iter()
            .enumerate()
            .filter_map(|(class, label)| label.map(|code| (code, class)))
            .collect();
        let mut rank = 0;
        let transport = located
            .labels
            .iter()
            .map(|label| {
                label.map(|_| {
                    rank += 1;
                    rank - 1
                })
            })
            .collect();
        let shared = Arc::new(EncodedChart {
            classes,
            sources,
            decoder: encoding.readout().clone(),
            fibre: encoding.fibre()?,
            labels: located.labels.clone(),
            advances: Some(located.advances.clone()),
            founded: Some(Founded {
                encoding: encoding.clone(),
                coupling: chart.coupling.clone(),
                transport,
            }),
        });
        passages
            .iter()
            .map(|passage| {
                let cells = passage
                    .iter()
                    .map(|code| {
                        class_of
                            .get(code)
                            .map(|&class| PortCell { class })
                            .ok_or(EncodingError::Unencoded)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Self {
                    cells,
                    chart: Arc::clone(&shared),
                })
            })
            .collect()
    }

    /// **The passage cut at an occurrence** (a request and its section): both halves keep the
    /// encoding that produced them; refused past the passage's end.
    pub fn split_at(self, at: usize) -> Result<(Self, Self), EncodingError> {
        if at > self.cells.len() {
            return Err(chart_refusal("an encoded passage is cut within it"));
        }
        let Self { mut cells, chart } = self;
        let tail = cells.split_off(at);
        Ok((
            Self {
                cells,
                chart: Arc::clone(&chart),
            },
            Self { cells: tail, chart },
        ))
    }

    /// **A part of the passage** (the cells a moment has not yet taken, a crib, a window): the
    /// occurrences in `range`, keeping the encoding that produced them; refused past the passage.
    pub fn part(&self, range: std::ops::Range<usize>) -> Result<Self, EncodingError> {
        let cells = self
            .cells
            .get(range)
            .ok_or_else(|| chart_refusal("an encoded passage's part lies within it"))?;
        Ok(Self {
            cells: cells.to_vec(),
            chart: Arc::clone(&self.chart),
        })
    }

    /// The occurrences' classes, in order.
    pub fn cells(&self) -> &[PortCell] {
        &self.cells
    }

    /// The occurrences' classes as the chart's indices, in order (the field's slots read them).
    pub fn classes_read(&self) -> impl Iterator<Item = usize> + '_ {
        self.cells.iter().map(|cell| cell.class)
    }

    /// **The located advance of occurrence `at`**: its class's digits `a_g(c)`, ring 0 first, on
    /// the located route; `None` for an identity (the field's lock fit steps it) or past the
    /// passage.
    pub fn advance(&self, at: usize) -> Option<&[u64]> {
        let cell = *self.cells.get(at)?;
        self.chart.advances.as_ref()?.digits(cell)
    }

    /// **The squares at the consumer** (module header; the located route only): at the lift `ℓ` the
    /// field read before occurrence `at` and the lift `ℓ′` its step reached, both on `ℚ^D`,
    /// `D E e_ℓ = ρ e_ℓ` and `E e_ℓ′ = U_a E e_ℓ` for the occurrence's transport `a`. An identity
    /// has nothing to check. Refused with [`EncodingError::Square`] (state: the occurrence) when
    /// either fails, with [`EncodingError::Unreached`] when a lift leaves the reached span, and with
    /// [`EncodingError::Unencoded`] at an unlabelled class.
    pub fn check_step(&self, at: usize, before: u64, after: u64) -> Result<(), EncodingError> {
        let Some(founded) = &self.chart.founded else {
            return Ok(());
        };
        let class = self
            .cells
            .get(at)
            .ok_or_else(|| chart_refusal("the occurrence lies within the passage"))?
            .class;
        let n = founded.encoding.chart();
        let (before, after) = (
            usize::try_from(before).map_err(|_| EncodingError::Unreached)?,
            usize::try_from(after).map_err(|_| EncodingError::Unreached)?,
        );
        if before >= n || after >= n {
            return Err(EncodingError::Unreached);
        }
        let encoded = founded.encoding.encode(&unit(n, before))?;
        let read = founded.encoding.readout().apply(&encoded)?;
        let reading: Vec<Rat> = founded
            .coupling
            .iter()
            .map(|form| form[before].clone())
            .collect();
        if read != reading {
            return Err(EncodingError::Square {
                square: "reading D E = ρ at the consuming step",
                state: at,
            });
        }
        let a = founded
            .transport
            .get(class)
            .copied()
            .flatten()
            .ok_or(EncodingError::Unencoded)?;
        let transport = founded
            .encoding
            .transport(a)
            .ok_or_else(|| chart_refusal("a located class's transport is founded"))?;
        if founded.encoding.encode(&unit(n, after))? != transport.apply(&encoded)? {
            return Err(EncodingError::Square {
                square: "conduct E T = U E at the consuming step",
                state: at,
            });
        }
        Ok(())
    }

    /// The occurrence count.
    pub fn len(&self) -> usize {
        self.cells.len()
    }

    /// Whether the passage holds no occurrence.
    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    /// The chart's class count: every class lies below it, and it is at most each source ring's
    /// period.
    pub fn classes(&self) -> usize {
        self.chart.classes
    }

    /// The source rings the classes were checked to inject into, `(ring, d_g)`.
    pub fn sources(&self) -> &[(usize, u64)] {
        &self.chart.sources
    }

    /// **`D`**, the decoder of the encoding that produced the passage: the identity on `ℚ^|A|` for a
    /// known truth, the founded readout (`D E = ρ`, one row per class) on the located route.
    pub fn decoder(&self) -> &ExactRatMatrix {
        &self.chart.decoder
    }

    /// **The Preimage Fibre**: the reached directions the encoding merges (`ker E ∩ R`, as chart
    /// states; empty for a known truth's identity).
    pub fn fibre(&self) -> &[Vec<Rat>] {
        &self.chart.fibre
    }

    /// The exterior code a class decodes to at the boundary, `λ(c)`; `None` at an unlabelled cell.
    pub fn label(&self, cell: PortCell) -> Option<usize> {
        self.chart.labels.get(cell.class).copied().flatten()
    }

    /// The located advances as the lift's digits, on the located route; `None` for an identity.
    pub fn located(&self) -> Option<&LocatedAdvances> {
        self.chart.advances.as_ref()
    }
}
