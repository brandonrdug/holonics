//! **A loaded ring's modes and their future quotient** (campaign 3, first construction; Lean
//! `HNN/ModeQuotient`).
//!
//! [definition] A loaded ring at a fixed publication (Decision 38, [`crate::hnn::ring`]): its
//! material read at the producing cut, its pump at phase `t mod P` of the word's tick `t`. Under the
//! exact law its word-local state `x = (u, w) ∈ ℚ^(2n)` ticks as one linear system per pump phase,
//! driven by the element output `e` and returning the wave `s′` to the ring's next junction:
//!
//! ```text
//! M_t ω = 2Cw + he − hK_t u,   u′ = u + hω,   w′ = 2ω − w,   s′ = e − (2/Y)ω
//! x′ = T_t x + B_t e           s′ = ρ_t x + D_t e
//! ```
//!
//! [`LoadedRing::at_cut`] forms `(T_t, B_t, ρ_t, D_t)` column by column from the owner's exact tick
//! ([`ResonatorOperands::step`] on the unit states and drives), so the law has no second copy here.
//! A lattice chart's executed solve is not the law, and its operands are refused.
//!
//! [definition] **The admitted receivers.** Receiver `0` is the loaded port: it reads `ρ_t` at every
//! phase, the wave the ring returns to the field. A declared [`StateReceiver`] reads the state at the
//! pump phases it names (a cycle receiver, for example, once per cycle). The present family is every
//! receiver that reads at phase `0`, the tick at the cut; the admitted future family is every
//! receiver at every later tick of the pump's cycle. It contains the present one, so
//! `ker F_future ⊆ ker F_now` (Lean `Holarchy/Hearing.HearingLaw.futureNull_le_ker_present`):
//! present silence alone releases nothing.
//!
//! [proved-derived; implemented-exact] **The admitted words are the pump's cycle, read through its
//! period** (Lean `periodic_lift_exact`, `cycle_mul_add`). With `Φ(0) = 1` and `Φ(t+1) = T_t Φ(t)`,
//! periodicity gives `Φ(mP + k) = Φ(k) T_P^m` for `T_P = Φ(P) = T_(P−1)⋯T_0`, so receiver `r`'s
//! reading at tick `t = mP + k` is `ρ_(r,k) Φ(k)` after `m` letters of the one period navigator
//! `T_P`. The requests `(r, t)` and `((r, k), m)` correspond one to one with equal readings, so the
//! kernel of [`FaceMap`] on the navigator `{T_P}` and the phase-offset receivers `ρ_(r,k) Φ(k)`,
//! `k < P`, is exactly the admitted future kernel `K_adm` ([`ModeQuotient::admitted`]). The phase
//! family read over arbitrary words would admit words the pump never runs.
//!
//! [proved-derived; implemented-exact] **One chart for every phase** (Lean `phase_kernel_le_lift`,
//! `shared_chart_le_phase_kernel`).
//! A retention chart `V` that serves every phase closes `V T_t = T̄_t V` and `ρ_(r,t) = ρ̄_(r,t) V`
//! exactly when `ker V` is carried by every `T_t` and read by no `ρ_(r,t)`. The largest such kernel
//! is the kernel `K_rel` of [`FaceMap`] on the phase family (navigators `T_t`, receivers `ρ_(r,t)`,
//! [`ModeQuotient::release`]), whose [`FaceMap::quotient`] checks both squares exactly and whose
//! sources descend as `B̄_t = V B_t`. Every admitted reading is a reading of that family after the
//! cycle's word, so `K_rel ⊆ K_adm ⊆ ker F_now`. A direction of `K_adm` outside `K_rel` is silent to
//! the whole admitted future, but a chart shared by every phase fails a square on it: it is retained
//! with the phase-family reading that separates it. The pumped witness: with `K = 0`, `C = 1` and a
//! half-turn pump, the pair `(u, (h/2)K_0 u)` moves no rate at phase `0` and ticks to
//! `(u, −(h/2)K_0 u)`, which moves none at phase `1`: the cycle never lets the port hear it. The
//! phase-`1` port would hear the pair itself (`2hK_0 u`), and a chart shared by both phases must
//! factor that reading, so one chart cannot drop it. It stores `½⟨u, K_0 u⟩ + (h²/8)|K_0 u|²`; a
//! phase-indexed chart family `V_(t+1) T_t = T̄_t V_t` could drop it, and one chart's release never
//! drops stored energy (below).
//!
//! [proved-derived; implemented-exact] **Every present-silent coordinate is accounted for**
//! ([`ModeQuotient::silent`]). The present blind subspace `N = ker F_now` has a basis adapted to
//! `K_rel ⊆ K_adm ⊆ N`: each direction of `K_rel` is [`Silence::Released`]; each further direction
//! of `K_adm` is [`Silence::SquareFails`] with the shortest phase-family word and reading that
//! separate it (the blind-subspace recursion descended one letter per level); each further direction
//! of `N` is [`Silence::Heard`] with the first tick and receiver of the admitted cycle that read it.
//!
//! [proved-derived; implemented-exact] **The released part stores nothing** (Lean
//! `released_pair_storage_null`). The port is admitted at every phase, so a released `(u, w)` has a
//! zero rate at every phase, its tick is `(u, −w)`, which is released too, and `2Cw = hK_t u`,
//! `−2Cw = hK_t u` give `Cw = 0` and `K_t u = 0`. The storage form `Q_t = diag(K_t, C)` annihilates
//! `K_rel` at every phase: the split `x = x_ret + x_rel` is `Q_t`-orthogonal (so `C`-orthogonal) for
//! every complement, `E_t(x + k) = E_t(x)` for `k ∈ K_rel`, and the storage descends to the retained
//! ring. This holds for every loaded ring whose port is admitted, not only for the fixtures.
//!
//! [proved-derived; implemented-exact] **The descended ring runs** (Lean `descended_run`,
//! `descended_run_reads`; [`ModeQuotient::run`]): `q′ = T̄_t q + B̄_t e`, `s′ = ρ̄_(0,t) q + D_t e`
//! from `q = V x` returns the full ring's wave at every tick for every drive sequence, the equation
//! at the consumer `decode(T_native(encode x)) = T(x)` with `V` the encoder and the port the decoder.
//!
//! | Lean `HNN/ModeQuotient` | Rust |
//! |---|---|
//! | `cycle_mul_add`, `periodic_lift_exact` | [`LoadedRing::cycle`], [`LoadedRing::period`], [`ModeQuotient::admitted`] |
//! | `phase_kernel_le_cycle`, `phase_kernel_le_lift`, `wordMap_cycleWord`, `shared_chart_le_phase_kernel` | [`ModeQuotient::release`], [`ModeQuotient::of`] (the nesting checked) |
//! | `descended_run`, `descended_run_reads` | [`ModeQuotient::run`] |
//! | `released_pair_storage_null` | [`ModeQuotient::released`] (checked at the consumer, `tests/modes.rs`) |
//! | `Compression/Core/FaceMap.{ker_faceMap_invariant, kernelClass_after_word, kernelReceiverQuotient}` | [`FaceMap::quotient`] |
//!
//! [definition; agent-inferred] **Why its own owner.** [`crate::hnn::retention`] releases whole
//! loci at an aeon boundary, structurally, on the field's sparsity; this owner releases directions
//! inside one loaded ring's state by their values (the value kernel that
//! [`crate::hnn::AeonBoundary`] names as campaign 3's). Its objects are the ring's modes and their
//! receivers, not loci, so they sit beside [`crate::hnn::ring`]'s exact tick and the
//! [`FaceMap`] owner they join.
//!
//! [definition] **Scope.** The material and its deposition do not descend here: a learning aeon
//! admits this quotient only once the deposit's covectors are shown to descend on the admitted
//! future. Dormancy across an aeon boundary, founding and far fields are later constructions.

use num_traits::One;

use crate::compression::{CompressionError, FaceMap, Retention};
use crate::hnn::HnnError;
use crate::hnn::ring::{ResonatorOperands, ResonatorRemainders};
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{add, is_zero, matrix, zeros};
use crate::receiver::standing::{NavigatorFamily, ReceiverReading};

// -------------------------------------------------------------------------------------------
// the loaded ring's exact operators

/// [definition] **One pump phase of a loaded ring under the exact law**: `x′ = T x + B e` and
/// `s′ = ρ x + D e` on the state `x = (u, w)` and the drive `e`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoadedPhase {
    /// `T_t`, `2n × 2n`.
    pub transport: ExactRatMatrix,
    /// `B_t`, `2n × n`.
    pub source: ExactRatMatrix,
    /// `ρ_t`, `n × 2n`: the returned wave's state part.
    pub reading: ExactRatMatrix,
    /// `D_t`, `n × n`: the returned wave's drive part.
    pub feedthrough: ExactRatMatrix,
}

/// [definition] **A loaded ring at a fixed publication**: its exact per-phase operators, formed from
/// the owner's tick.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoadedRing {
    ring: usize,
    width: usize,
    phases: Vec<LoadedPhase>,
}

fn unit(extent: usize, index: usize) -> Vec<Rat> {
    let mut vector = zeros(extent);
    vector[index] = Rat::one();
    vector
}

fn from_columns(rows: usize, columns: &[Vec<Rat>]) -> Result<ExactRatMatrix, HnnError> {
    Ok(matrix(rows, columns.len(), |row, column| {
        columns[column][row].clone()
    })?)
}

impl LoadedRing {
    /// **The ring's exact operators at the cut** (module header): each phase's columns are the
    /// owner's exact tick at that phase on a unit state (zero drive) and on a unit drive (zero
    /// state). Refused when a phase's executed solve is a lattice chart, which is not the law.
    pub fn at_cut(operands: &ResonatorOperands) -> Result<Self, HnnError> {
        let ring = operands.ring();
        let n = operands.width();
        let extent = 2 * n;
        let rest = ResonatorRemainders::default();
        let mut phases = Vec::with_capacity(operands.phases());
        for phase in 0..operands.phases() {
            if operands.chart_words(phase).is_some() {
                return Err(HnnError::ModeQuotient {
                    ring,
                    what: "the mode quotient reads the exact law, not a lattice chart's solve",
                });
            }
            // Word tick `phase` lies at pump phase `phase` (`ResonatorOperands::phase_at`).
            let tick = |drive: &[Rat], state: &[Rat]| {
                operands.step(phase, drive, [&state[..n], &state[n..]], &rest, None)
            };
            let (mut transport, mut reading) = (Vec::new(), Vec::new());
            for column in 0..extent {
                let stepped = tick(&zeros(n), &unit(extent, column))?;
                transport.push([stepped.state[0].clone(), stepped.state[1].clone()].concat());
                reading.push(stepped.output);
            }
            let (mut source, mut feedthrough) = (Vec::new(), Vec::new());
            for column in 0..n {
                let stepped = tick(&unit(n, column), &zeros(extent))?;
                source.push([stepped.state[0].clone(), stepped.state[1].clone()].concat());
                feedthrough.push(stepped.output);
            }
            phases.push(LoadedPhase {
                transport: from_columns(extent, &transport)?,
                source: from_columns(extent, &source)?,
                reading: from_columns(n, &reading)?,
                feedthrough: from_columns(n, &feedthrough)?,
            });
        }
        Ok(Self {
            ring,
            width: n,
            phases,
        })
    }

    pub fn ring(&self) -> usize {
        self.ring
    }

    /// `n`, the ring's realified width (the drive's and the wave's extent).
    pub fn width(&self) -> usize {
        self.width
    }

    /// `2n`, the state's extent.
    pub fn extent(&self) -> usize {
        2 * self.width
    }

    /// The pump phases, in order.
    pub fn phases(&self) -> &[LoadedPhase] {
        &self.phases
    }

    /// **The cycle's transport** `Φ(t) = T_(t−1 mod P) ⋯ T_0` over the word's first `t` ticks.
    pub fn cycle(&self, ticks: usize) -> Result<ExactRatMatrix, HnnError> {
        let mut transport = ExactRatMatrix::identity(self.extent())?;
        for tick in 0..ticks {
            transport = self.phases[tick % self.phases.len()]
                .transport
                .multiply(&transport)?;
        }
        Ok(transport)
    }

    /// **The period navigator** `T_P = Φ(P)`.
    pub fn period(&self) -> Result<ExactRatMatrix, HnnError> {
        self.cycle(self.phases.len())
    }
}

// -------------------------------------------------------------------------------------------
// the admitted receivers

/// [definition] **A declared receiver of the ring's state** beside its port: its exact reading of
/// `x = (u, w)` and the pump phases at which it reads.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateReceiver {
    reading: ExactRatMatrix,
    phases: Vec<usize>,
}

impl StateReceiver {
    pub fn new(reading: ExactRatMatrix, phases: Vec<usize>) -> Self {
        Self { reading, phases }
    }

    pub fn reading(&self) -> &ExactRatMatrix {
        &self.reading
    }

    pub fn phases(&self) -> &[usize] {
        &self.phases
    }
}

/// [definition] **What separates a direction**: receiver `receiver` (`0` the port, `j + 1` the
/// `j`-th declared) reading at pump phase `phase` after the word `word` of phase navigators, its
/// last letter acting first.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Separator {
    pub receiver: usize,
    pub phase: usize,
    pub word: Vec<usize>,
}

/// [definition] **The account of one present-silent direction** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Silence {
    /// Read by the admitted cycle at a later tick (`word.len()`, the cycle's word): retained.
    Heard(Separator),
    /// Silent to the whole admitted future, but a chart shared by every phase fails a square on
    /// it: retained, with the phase-family reading that separates it.
    SquareFails(Separator),
    /// In the stable future kernel on which every square closes: released.
    Released,
}

/// [definition] **One present-silent direction** of the adapted basis, with its account.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SilentCoordinate {
    pub direction: Vec<Rat>,
    pub silence: Silence,
}

// -------------------------------------------------------------------------------------------
// the quotient

/// [definition] **A loaded ring's mode quotient** under its admitted receiver family (module
/// header): the admitted future kernel by the period lift, the release by the one chart that closes
/// every phase's squares, the descended operators and the account of every present-silent
/// direction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModeQuotient {
    ring: usize,
    extent: usize,
    phases: usize,
    requests: Vec<(usize, usize)>,
    present: Vec<Vec<Rat>>,
    admitted: FaceMap,
    release: FaceMap,
    retention: Retention,
    sources: Vec<ExactRatMatrix>,
    feedthroughs: Vec<ExactRatMatrix>,
    silent: Vec<SilentCoordinate>,
}

/// Whether `x` lies in the span of the independent `basis`.
fn in_span(basis: &[Vec<Rat>], x: &[Rat]) -> Result<bool, HnnError> {
    if is_zero(x) {
        return Ok(true);
    }
    if basis.is_empty() {
        return Ok(false);
    }
    let mut rows = basis.to_vec();
    rows.push(x.to_vec());
    Ok(ExactRatMatrix::shaped(rows.len(), x.len(), rows)?.rank()? == basis.len())
}

fn receiver_reading(matrix: &ExactRatMatrix) -> Result<ReceiverReading, HnnError> {
    ReceiverReading::declared("mode receiver", matrix.clone())
        .map_err(|refusal| CompressionError::from(refusal).into())
}

impl ModeQuotient {
    /// **The ring's mode quotient** under its port and the declared receivers.
    pub fn of(ring: &LoadedRing, receivers: &[StateReceiver]) -> Result<Self, HnnError> {
        let extent = ring.extent();
        let period = ring.phases().len();
        for receiver in receivers {
            if receiver.reading.columns() != extent || receiver.reading.rows() == 0 {
                return Err(HnnError::Shape {
                    what: "a state receiver reads the ring's state (u, w)",
                    expected: extent,
                    found: receiver.reading.columns(),
                });
            }
            if let Some(&phase) = receiver.phases.iter().find(|&&phase| phase >= period) {
                return Err(HnnError::Shape {
                    what: "a state receiver's phase (the pump's phases)",
                    expected: period,
                    found: phase,
                });
            }
        }
        // Every reading `(r, t)`, phase-major; receiver 0 is the port.
        let mut requests = Vec::new();
        let mut maps: Vec<ExactRatMatrix> = Vec::new();
        for (phase, loaded) in ring.phases().iter().enumerate() {
            requests.push((0, phase));
            maps.push(loaded.reading.clone());
            for (index, receiver) in receivers.iter().enumerate() {
                if receiver.phases.contains(&phase) {
                    requests.push((index + 1, phase));
                    maps.push(receiver.reading.clone());
                }
            }
        }
        let lifted = requests
            .iter()
            .zip(&maps)
            .map(|(&(_, phase), map)| receiver_reading(&map.multiply(&ring.cycle(phase)?)?))
            .collect::<Result<Vec<_>, HnnError>>()?;
        let admitted = FaceMap::new(
            NavigatorFamily::declared(
                "the pump's period",
                vec!["T_P".into()],
                vec![ring.period()?],
            )
            .map_err(CompressionError::from)?,
            lifted,
        )?;
        let release = FaceMap::new(
            NavigatorFamily::declared(
                "the pump's phases",
                (0..period).map(|phase| format!("T_{phase}")).collect(),
                ring.phases().iter().map(|p| p.transport.clone()).collect(),
            )
            .map_err(CompressionError::from)?,
            maps.iter()
                .map(receiver_reading)
                .collect::<Result<Vec<_>, _>>()?,
        )?;
        let retention = release.quotient()?;
        let sources = ring
            .phases()
            .iter()
            .map(|p| retention.retain().multiply(&p.source))
            .collect::<Result<Vec<_>, _>>()?;
        let feedthroughs = ring
            .phases()
            .iter()
            .map(|p| p.feedthrough.clone())
            .collect();
        let present_rows: Vec<Vec<Rat>> = requests
            .iter()
            .zip(&maps)
            .filter(|((_, phase), _)| *phase == 0)
            .flat_map(|(_, map)| map.to_rows())
            .collect();
        let present =
            ExactRatMatrix::shaped(present_rows.len(), extent, present_rows)?.kernel_basis()?;
        let released = release.kernel()?;
        let admitted_kernel = admitted.kernel()?;
        // K_rel ⊆ K_adm ⊆ N (`phase_kernel_le_lift`, `futureNull_le_ker_present`).
        for direction in &released {
            if !in_span(&admitted_kernel, direction)? {
                return Err(HnnError::ModeQuotient {
                    ring: ring.ring(),
                    what: "the one-chart release leaves the admitted future kernel",
                });
            }
        }
        for direction in &admitted_kernel {
            if !in_span(&present, direction)? {
                return Err(HnnError::ModeQuotient {
                    ring: ring.ring(),
                    what: "the admitted future kernel leaves the present blind subspace",
                });
            }
        }
        let mut quotient = Self {
            ring: ring.ring(),
            extent,
            phases: period,
            requests,
            present,
            admitted,
            release,
            retention,
            sources,
            feedthroughs,
            silent: Vec::new(),
        };
        quotient.silent = quotient.account(ring, &maps, released, admitted_kernel)?;
        Ok(quotient)
    }

    /// The adapted basis of `N` over `K_rel ⊆ K_adm`, each direction with its account.
    fn account(
        &self,
        ring: &LoadedRing,
        maps: &[ExactRatMatrix],
        released: Vec<Vec<Rat>>,
        admitted_kernel: Vec<Vec<Rat>>,
    ) -> Result<Vec<SilentCoordinate>, HnnError> {
        let mut chosen: Vec<Vec<Rat>> = Vec::new();
        let mut silent = Vec::new();
        for direction in released {
            chosen.push(direction.clone());
            silent.push(SilentCoordinate {
                direction,
                silence: Silence::Released,
            });
        }
        for direction in admitted_kernel {
            if !in_span(&chosen, &direction)? {
                let separator = self.phase_separator(ring, maps, &direction)?;
                chosen.push(direction.clone());
                silent.push(SilentCoordinate {
                    direction,
                    silence: Silence::SquareFails(separator),
                });
            }
        }
        for direction in self.present.clone() {
            if !in_span(&chosen, &direction)? {
                let separator = self.cycle_separator(ring, maps, &direction)?;
                chosen.push(direction.clone());
                silent.push(SilentCoordinate {
                    direction,
                    silence: Silence::Heard(separator),
                });
            }
        }
        Ok(silent)
    }

    /// The first tick of the admitted cycle, and its first receiver, that read `x`: within
    /// `P (m + 1)` ticks, `m` the lift's stable horizon, when `x ∉ K_adm`.
    fn cycle_separator(
        &self,
        ring: &LoadedRing,
        maps: &[ExactRatMatrix],
        x: &[Rat],
    ) -> Result<Separator, HnnError> {
        let mut state = x.to_vec();
        for tick in 0..self.phases * (self.admitted.stable_at() + 1) {
            let phase = tick % self.phases;
            for (&(receiver, at), map) in self.requests.iter().zip(maps) {
                if at == phase && !is_zero(&map.apply(&state)?) {
                    return Ok(Separator {
                        receiver,
                        phase,
                        word: (0..tick).rev().map(|s| s % self.phases).collect(),
                    });
                }
            }
            state = ring.phases()[phase].transport.apply(&state)?;
        }
        Err(HnnError::ModeQuotient {
            ring: self.ring,
            what: "a direction outside the admitted kernel has no admitted reading",
        })
    }

    /// The shortest phase-family word and reading that separate `x ∉ K_rel`: from the first
    /// horizon `n` with `x ∉ B_n`, some letter carries `x` out of `B_(n−1)`, down to a reading.
    fn phase_separator(
        &self,
        ring: &LoadedRing,
        maps: &[ExactRatMatrix],
        x: &[Rat],
    ) -> Result<Separator, HnnError> {
        let blinds = (0..=self.release.stable_at())
            .map(|horizon| self.release.blind(horizon))
            .collect::<Result<Vec<_>, _>>()?;
        let mut level = None;
        for (horizon, blind) in blinds.iter().enumerate() {
            if !in_span(blind, x)? {
                level = Some(horizon);
                break;
            }
        }
        let mut level = level.ok_or(HnnError::ModeQuotient {
            ring: self.ring,
            what: "a direction outside the release lies in every blind subspace",
        })?;
        let mut state = x.to_vec();
        let mut acting = Vec::new();
        loop {
            for (&(receiver, phase), map) in self.requests.iter().zip(maps) {
                if !is_zero(&map.apply(&state)?) {
                    acting.reverse();
                    return Ok(Separator {
                        receiver,
                        phase,
                        word: acting,
                    });
                }
            }
            if level == 0 {
                return Err(HnnError::ModeQuotient {
                    ring: self.ring,
                    what: "a direction outside the present blind subspace has no reading",
                });
            }
            let below = &blinds[level - 1];
            let mut next = None;
            for (letter, phase) in ring.phases().iter().enumerate() {
                let carried = phase.transport.apply(&state)?;
                if !in_span(below, &carried)? {
                    next = Some((letter, carried));
                    break;
                }
            }
            let (letter, carried) = next.ok_or(HnnError::ModeQuotient {
                ring: self.ring,
                what: "no phase carries a direction out of the next blind subspace",
            })?;
            acting.push(letter);
            state = carried;
            level -= 1;
        }
    }

    pub fn ring(&self) -> usize {
        self.ring
    }

    /// `2n`, the state's extent.
    pub fn extent(&self) -> usize {
        self.extent
    }

    /// The pump phases.
    pub fn phases(&self) -> usize {
        self.phases
    }

    /// **The retention chart** `V`, of full row rank, `ker V = K_rel`.
    pub fn retain(&self) -> &ExactRatMatrix {
        self.retention.retain()
    }

    /// `rank V = 2n − dim K_rel`.
    pub fn retained_rank(&self) -> usize {
        self.retention.extent()
    }

    /// `dim K_rel`.
    pub fn released_rank(&self) -> usize {
        self.extent - self.retention.extent()
    }

    /// A basis of `K_rel`, the directions released.
    pub fn released(&self) -> Result<Vec<Vec<Rat>>, HnnError> {
        Ok(self.release.kernel()?)
    }

    /// A basis of `N = ker F_now`, the directions the present family does not read.
    pub fn present_silent(&self) -> &[Vec<Rat>] {
        &self.present
    }

    /// **The period lift**: [`FaceMap`] on `{T_P}` and the phase-offset receivers `ρ_(r,k) Φ(k)`,
    /// in the order of [`ModeQuotient::requests`]; its kernel is `K_adm`.
    pub fn admitted(&self) -> &FaceMap {
        &self.admitted
    }

    /// **The phase family**: [`FaceMap`] on `{T_t}` and the readings `ρ_(r,t)`, in the order of
    /// [`ModeQuotient::requests`]; its kernel is `K_rel`.
    pub fn release(&self) -> &FaceMap {
        &self.release
    }

    /// The readings `(receiver, phase)`, phase-major, receiver `0` the port.
    pub fn requests(&self) -> &[(usize, usize)] {
        &self.requests
    }

    /// `T̄_t`, with `V T_t = T̄_t V`.
    pub fn transport(&self, phase: usize) -> Option<&ExactRatMatrix> {
        self.retention.navigator(phase)
    }

    /// `B̄_t = V B_t`.
    pub fn source(&self, phase: usize) -> Option<&ExactRatMatrix> {
        self.sources.get(phase)
    }

    /// `D_t`, unchanged by the descent.
    pub fn feedthrough(&self, phase: usize) -> Option<&ExactRatMatrix> {
        self.feedthroughs.get(phase)
    }

    /// `ρ̄_(r,t)`, with `ρ_(r,t) = ρ̄_(r,t) V`, where receiver `r` reads at phase `t`.
    pub fn reading(&self, receiver: usize, phase: usize) -> Option<&ExactRatMatrix> {
        let index = self
            .requests
            .iter()
            .position(|&request| request == (receiver, phase))?;
        self.retention.reading(index)
    }

    /// The account of every present-silent direction, in the adapted basis.
    pub fn silent(&self) -> &[SilentCoordinate] {
        &self.silent
    }

    /// `V x`.
    pub fn retained(&self, state: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        Ok(self.retention.retained(state)?)
    }

    /// **The descended ring's run** from a retained state `q` on the drives `e_t`, word tick `t` at
    /// phase `t mod P`: the returned waves `s′_t = ρ̄_(0,t) q_t + D_t e_t`, with
    /// `q_(t+1) = T̄_t q_t + B̄_t e_t` (Lean `descended_run_reads`).
    pub fn run(&self, retained: &[Rat], drives: &[Vec<Rat>]) -> Result<Vec<Vec<Rat>>, HnnError> {
        if retained.len() != self.retained_rank() {
            return Err(HnnError::Shape {
                what: "a retained state (the chart's rank)",
                expected: self.retained_rank(),
                found: retained.len(),
            });
        }
        let mut state = retained.to_vec();
        let mut waves = Vec::with_capacity(drives.len());
        for (tick, drive) in drives.iter().enumerate() {
            let phase = tick % self.phases;
            let feedthrough = &self.feedthroughs[phase];
            if drive.len() != feedthrough.columns() {
                return Err(HnnError::Shape {
                    what: "a drive (the ring's realified width)",
                    expected: feedthrough.columns(),
                    found: drive.len(),
                });
            }
            let port = self.reading(0, phase).ok_or(HnnError::ModeQuotient {
                ring: self.ring,
                what: "the port reads at every phase",
            })?;
            waves.push(add(&port.apply(&state)?, &feedthrough.apply(drive)?));
            let transport = self.transport(phase).ok_or(HnnError::ModeQuotient {
                ring: self.ring,
                what: "every phase descends",
            })?;
            state = add(
                &transport.apply(&state)?,
                &self.sources[phase].apply(drive)?,
            );
        }
        Ok(waves)
    }
}

impl SilentCoordinate {
    /// Whether this direction is released.
    pub fn released(&self) -> bool {
        matches!(self.silence, Silence::Released)
    }
}
