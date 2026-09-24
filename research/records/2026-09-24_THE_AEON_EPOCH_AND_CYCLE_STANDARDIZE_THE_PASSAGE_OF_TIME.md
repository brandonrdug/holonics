# The Aeon, the Epoch and the Cycle standardize the passage of time

[project-postulate] Brandon, September 24, 2026. **Aeon**, **Epoch** and **Cycle** are the
standard vocabulary for the passage of time. "Session", "episode", and counters named
`epoch`/`cycle`/`generations` that serve as one global clock are retired as terms for time.
The ruling came from auditing the code. "Session" appears about 1,120 times in Rust (66 files),
about 1,300 times in Markdown and 19 times in Lean. `epoch` (555 Rust uses), `cycle` (654) and
`generations` (331) served as separate privileged counters. Every one of them named a window
that the program chose, not a structure of the mathematics.

[definition] What we had made rigorous was spatial continuation: the tube, the tower, the
Holarchy and relative completeness. Coarse graining in time had no object of its own. It lived
implicitly in generator clocks and tubes, and explicitly only in process windows. This record
supplies the temporal object from the existing elementary objects.

## The three terms

[definition] **Aeon.** An arbitrary container of causality in time. It is part of a
Holarchy's parametric orientation: the stretch of the Holarchy's motion between two
occurrences.
- The Holarchy's generators carry clocks with phase lifts. Their joint phase lives on a torus
  `𝕋ᵏ`, and its lift to `ℝᵏ` retains winding (helix = circle + carry).
- An aeon `γ` is a 1-chain of the motion in that lift. It is not an interval of a privileged
  clock. Occurrences (the Lean foundation's events) bound it.
- An aeon is arbitrary: any causal span of the motion is one. Aeons compose by concatenation.

[definition] **Epoch.** A division of an aeon. A receiver's clock ticks when the motion crosses
the receiver's section `Σ_R`; parametron: "a section crossing is a clock tick". The ticks
partition an aeon into epochs at that receiver's grain.
- The partition belongs to the receiver and grain: another receiver or a coarser grain
  partitions the same aeon into different epochs.
- Coarsening merges epochs. Counting returns to a sub-section `Σ′ ⊂ Σ` is the first-return
  (induced) map, and the Odometer's carry is the same operation on a digit clock.

[definition] **Cycle.** A closed loop: completeness, not a measurement of duration. An aeon
that returns to its phase state is a cycle.
- Its readings are whole windings, the homology class paired with a clock class.
- Exact parts integrate to zero around it (Stokes), so its readings are gauge-free and
  invariant under deformation.
- A cycle conserves its frames in time: whatever a receiver reads over a cycle is a conserved
  count, not an elapsed quantity.

## How much time passed: a pairing, not a frame

[definition] A receiver's clock is a closed 1-form `ω_R`: `dθ_R` for a phase clock, or
`−U_μ dx^μ` for an observer with four-velocity `U` on a world tube. Elapsed time for `R` over
an aeon is the holon/coholon pairing:

```text
t_R(γ) = ⟨ω_R | γ⟩ = ∫_γ ω_R = n_R + r_R
n_R ∈ ℤ   whole windings: the quotient, the carry
r_R       open phase: the remainder
```

- **No frame is privileged.** Every receiver pairs the same aeon with its own form. The rate
  between two receivers is the typed ratio of their two readings, "one per two".
- **Composition.** Readings add under concatenation, with the carry cocycle:
  `winding(x+y) = winding x + winding y + carry`.
- **Cycles.** A cycle reads `r_R = 0` for every integral clock, and its `n_R` is topological.

## Coarse graining, flux and winding

[definition] **Flux.** Epoch ticks per unit parameter are the flux of the motion through the
receiver's section, `∫_{Σ_R} ρ v·n dS` for the flow's invariant density. The time a receiver
counts is the flux of the Holarchy's motion through its section. It does not matter whether the
motion is read as a push or a pull: the count is the flux.

[proved-standard; stated hypotheses] **Across grains.** For a measure-preserving return map
that is ergodic on the section, Kac's lemma gives a mean first-return time to `Σ′` of
`μ(Σ)/μ(Σ′)` fine epochs per coarse epoch. How much finer time passes per coarse epoch is
therefore a ratio of section measures, not a property of a privileged clock.

[proved-standard] **Two clocks and their crossing axes.** Take two clocks with frequency ratio `α`.
- If `α = p/q`, the pair locks, and every aeon of `q` ticks is a cycle. `p/q` is the pair's Farey
  lock address (`q·v_a = p·v_b`), where the two section axes on the torus intersect.
- If `α` is irrational, no aeon is a cycle. The natural epoch grains are then the
  continued-fraction convergents `p_n/q_n`, where `|q_n α − p_n| < 1/q_{n+1}`: near-returns at
  every grain, closure at none. The three-distance theorem bounds the gap structure at each
  grain.

The winding therefore decides where the Holarchy's own temporal boundaries fall.

## What it joins

- **Retention.** An aeon's boundary is where the future-sufficient quotient of the constitution
  is taken. What rests at a boundary is the retained constitution, not a record of the aeon's
  interior. A "session save" was a program-chosen proxy for this.
- **The Holarchy.** In space, the Holarchy decomposes the whole per receiver and grain
  (`view`, `count`). Its parametric orientation carries aeons, which decompose in time per
  receiver and grain (epochs). `count` exists only under a certified section, as in space.
  Together they decompose the world tube.
- **Open work this subsumes:**
  - the plan's clock-axis joining (§3.6, `join_axes`): two closed forms over one aeon, which
    commute or return their holonomy;
  - the time/entropy chain crossing (#5): the entropy-production clock as one more closed form;
  - Brandon's several axes of parametric time for cross-entropy: its rate along an aeon depends
    on which clock form parametrizes it.
- **Existing owners:**
  - Lean: `Geometry/PhaseCarry` (lift, carry), `Transport/CellHolonomy` (cycles and holonomy),
    `Objects/Pairing`, `Physics/ObserverBoundaryCurrent` (the observer covector),
    `Transport/ChangingReceiver`;
  - Rust: `holonics::geometry::winding` (`Odometer` as a tower of epochs, `LockAddress`).

## The general objects

These are stated in the elementary objects so that they can be derived further and implemented
as the framework's basis. The instances in the next section are graded applications, not the
objects' purpose.

### A1. The aeon groupoid and clock representations

[definition] Occurrences are the objects and aeons are the arrows. Composition is concatenation,
and orientation reversal `Rγ` gives the inverse. A **clock** is a representation of this groupoid
in `(ℝ,+)` that lifts a circle phase.
- A closed 1-form is a **flat** time connection. Its reading on an aeon is parallel transport,
  and on a cycle it is holonomy.
- Epoch crossings are the ℤ-valued cocycle.
- Carry is the 2-cocycle of reducing modulo the period.

[proved-standard] Readings are functorial (additive with carry). For closed clocks, cycle
readings factor through `H₁` and are homotopy-invariant.

### A2. Hodge-decomposed time

[proved-standard; agent-inferred reading] On the aeon's carrier (a compact Riemannian manifold,
or a finite cell complex with the discrete Hodge Laplacian), every clock 1-form splits as
`ω = dφ + δβ + h`. The three parts are three kinds of time:

| Part | Kind | Reading | Examples |
|---|---|---|---|
| exact `dφ` | **state** | fixed by the aeon's two boundary occurrences (Stokes) | entropy `S`, cross-entropy `C`, potentials |
| harmonic `h` | **winding** | topological and conserved on cycles | phase clocks, generator windings |
| coexact `δβ` | **production** | non-closed, nonzero on contractible cycles; the curvature of the time connection | irreversibility, circulation generation |

[agent-inferred] An aeon is relatively complete for a clock exactly when that clock reads exactly
on it. The persistent interior motion is the harmonic plus coexact remainder.

### A3. Asymptotic cycle

[proved-standard] For a flow-invariant probability measure μ, long aeons satisfy
`γ_T/T → A_μ ∈ H₁(M;ℝ)` (Schwartzman). Each receiver's long-run tick rate is
`⟨[ω_R], A_μ⟩`, and rate ratios are ratios of these pairings. On a torus, `A_μ` is the rotation
vector.

### A4. Entropy under a change of clock

[proved-standard] By Abramov's formula, entropy per epoch = entropy per unit time × mean epoch
length. By Kac's lemma, the mean first return to `Σ′` is `μ(Σ)/μ(Σ′)`. Entropy is a density along
aeons that transforms by the ratio of clock readings. The several axes of parametric time are
therefore well defined: each clock has its own entropy rate, and the rates are related by
pairings.

### A5. Production: the arrow as a positive, non-closed clock

[proved-standard] `dS = δQ/T + σ`, with `σ ≥ 0`. Over a cycle, `∮δQ/T = −∮σ ≤ 0` (Clausius).
- Phase clocks are closed and reversible. Production is positive and not closed; it is the arrow.
- The time/entropy crossing (#5) resolves here: the entropy axis is a positive curvature term,
  not a second phase clock.
- [agent-inferred] In the Holon, σ is the resistive `D ⪰ 0` term, `⟨Jv, D Jv⟩/T`. The
  power-neutral Dirac interconnection and the Cayley reaction contribute zero.

### A6. Irreversibility is a relative entropy

[proved-standard] `σ(γ) = D(P_γ ‖ P_{Rγ})` (Kawai–Parrondo–Van den Broeck; Gaspard; Maes). It is
additive over epochs for Markov dynamics, and zero exactly under detailed balance. This is
cross-entropy as a literal physical effect: the arrow of an aeon is the divergence between the
aeon and its reversal.

### A7. The first law of learning

[exact identity; agent-inferred reading] Along an aeon,

```text
ΔC = ∫ −Σ ṗ log q   (exchange)   +   ∫ −Σ p q̇/q   (deposition)
```

Each term depends on the path, and their sum depends only on the boundary. Over a cycle, exchange
equals minus deposition. This is the heat/work structure of learning.

### A8. The dynamical zeta of the epoch return map

[proved-standard] `ζ(T) = exp Σ_n N_n Tⁿ/n`, where `N_n` counts cycles of n epochs.
- For a linear or finite return map, `ζ = 1/det(I − T·M)`.
- The topological entropy is `log ρ(M)`, and the first pole sits at `T = e^{−h}`.
- The generator machine's conserved trace faces, `det(1−T·M)` and
  `∏(1−a_g T+q_g T²)`, **are** its dynamical zeta.

For a flow, the zeta is a product over primitive cycles weighted by their readings,
`∏_c (1 − e^{−s·t(c)})^{-1}`. The trace formula equates the resonances with a sum over cycles
weighted by `t(c)/|det(1−P_cᵏ)|^{1/2}`, where `P_c` is the cycle's transverse holonomy.

### A9. Placement and reversibility

[proved-standard, finite] Detailed balance makes the generator self-adjoint in `L²(π)`, so its
spectrum is real. Production is what permits complex spectrum. This is the finite form of #54:
`G ≻ 0, S = Sᵀ ⇒ σ(G⁻¹S) ⊂ ℝ`.

[agent-inferred model] Correlations decay at the transfer operator's spectral gap. The retained
quotient keeps the modes that survive the admitted future aeon: modes on the unit circle
(cycles) are conserved, and modes inside it decay.

### A10. The production functional

[agent-inferred synthesis over standard facts] A functional `P ≥ 0` on aeons and multi-aeons whose
**zero set is the distinguished class**:

| Subject | P | Zero set |
|---|---|---|
| Thermodynamics | σ | reversible cycles |
| Spectral | the generator's antisymmetric part | real spectrum |
| Kähler/Hodge | calibration defect `Vol(Z) − ⟨ω^p/p!, Z⟩` (Wirtinger) | complex (algebraic) cycles |
| Fluids | viscous dissipation `2ν|Def u|²/T` | Kelvin-conserved Euler cycles |

Complexification or indefiniteness removes the lower bound, and singular aeons appear there.

### A11. Singular aeon

[definition] An aeon in which one clock's reading is finite while another clock's epoch count
diverges: two clocks whose ratio blows up. The multi-parameter form is a k-chain swept by
commuting clocks, the crossing axes. Its closed orbits (subtori) are its cycles.

## Graded instances

- **Hodge.**
  - [reformulation, not progress] Algebraic cycles are the zero-defect multi-aeons (A10). The
    conjecture restates as: every rational `(p,p)` class is a ℚ-combination of zero-defect cycle
    classes.
  - [proved-standard] It holds where commuting clocks generate everything: toric varieties, and
    Białynicki-Birula decompositions, where orbit-closure cycles span the cohomology.
- **Spectral placement (RH).**
  - [standard] The trace formula is the pairing of spectrum with cycle readings (A8). Weil's
    explicit formula is its Lefschetz form, with primes as cycles of reading `log p`.
  - [conjectural] Deninger's flow.
  - [heuristic, open] In A9's terms, placement on the line is reversibility of that flow
    (Hilbert–Pólya), and Weil positivity is its positivity face. None of this proves RH.
- **Euler and Navier–Stokes.**
  - [proved-standard] Kelvin: Euler conserves the circulation reading of material cycles, and
    viscosity produces `σ ≥ 0`. Helicity is the linking reading of vortex cycles.
  - [proved-standard] Beale–Kato–Majda: a smooth solution continues past `T*` exactly when the
    vorticity clock reads finitely, `∫₀^{T*}‖ω‖_∞ dt < ∞`. This is A11.
  - [heuristic] With Littlewood–Paley shells as scale-clock sections, the energy flux `Π_j` is
    the tick rate across shell j. Under K41 the turnover times have a finite sum: infinitely many
    epochs in a finite aeon, the Onsager dissipation anomaly.
- **Complex fluids.** [proved-standard] Complexification makes the energy form indefinite,
  `B(a,a)−B(b,b)`, and Li–Sinai proved finite-time blow-up for complex 3D NS. Real NS keeps
  `σ ≥ 0`, but energy is supercritical relative to the vorticity clock's scaling. That is the
  exact shape of the open problem.

## Obligations, in construction order

**Lean** (`Holonics.Aeon`; items join #62 as they are owed):
1. The aeon groupoid and clocks: readings additive with carry. Cycle readings factor through
   homology and are homotopy-invariant.
2. Quotient and remainder: the split into windings and open phase agrees with the ratio's
   division with remainder.
3. Discrete Hodge-decomposed time on a finite cell complex, over the existing exact Hodge
   owners. State readings are boundary-determined, and harmonic readings are cycle invariants.
4. For finite Markov chains:
   - Kac's lemma and Abramov's formula;
   - `σ = D(P_γ‖P_{Rγ}) ≥ 0`, with equality ⇔ detailed balance;
   - detailed balance ⇒ real spectrum.
5. `ζ(T) = 1/det(I−TM)` and `h = log ρ(M)`, joined to the existing trace faces.
6. The first-law split of cross-entropy change (A7).
7. The convergent near-return bound for two clocks (continued fractions and Farey addresses).
8. Epoch refinement towers under a certified section.

**Rust** (`holonics::aeon`, or `geometry::clock`; K1 #72):
- `Aeon`, `Clock` (closed form with period and lift), `Epoch` partition, `Cycle`;
- `reading -> (windings, phase)`, `concat`, `reverse`, `epochs(receiver, grain)`, `coarsen`;
- `hodge_split(clock)` on cell complexes;
- `production(aeon)` for Markov and port-Hamiltonian instances;
- `zeta(return_map)`.

The HNN interface is then rebuilt over aeons (open from a retained quotient, advance, receive at
sections, close at a boundary), replacing the retired "session" types.
