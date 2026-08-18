# The Clifford lift, the phase wire, and the four untaken readings

**Date:** 2026-08-17
**Truth status:** `interpretation` for the ordering; every station's own return is graded where it
lands. Every citation below was verified at the line given on the day of writing.
**Evidence:** the findings this plan acts on are
[`research/records/2026-08-17_THREE_OWNERS_ONE_ABELIAN_DEFECT_AND_THE_JULY_CORPUS_ALREADY_HELD_THE_REPAIR.md`](../research/records/2026-08-17_THREE_OWNERS_ONE_ABELIAN_DEFECT_AND_THE_JULY_CORPUS_ALREADY_HELD_THE_REPAIR.md),
produced by one external adjudication run twice and two Opus sweeps, all read-only.
**Provenance:** Brandon, 2026-08-17: *"Deposit the sweep's findings independently, and then deposit
this as our active blueprint design plan, including everything you listed as 'owed'."*
**Plan:** sits under [`blueprint/THE_ROADMAP.md`](THE_ROADMAP.md). It **supersedes**
[`blueprint/THE_ARROW_IS_THE_DIVISION_AND_ATTENTION_KEEPS_ONLY_ITS_AIM.md`](THE_ARROW_IS_THE_DIVISION_AND_ATTENTION_KEEPS_ONLY_ITS_AIM.md),
whose stations one and two executed and whose stations three and four are carried here — station four
merged into station one by the correction below.

---

## 0. Why this plan is small

**One organ, two wires, four readings, one document repair.** The finger-trap rule was tested rather
than assumed and it held: almost everything this line needs already stands, and the single genuine
organ is a *lift* of `soma/body/src/arrow.rs` rather than a new semantic owner.

**The one sentence that orders the work:**

> Three owners — `multiquadratic`, soma's rotor face, and `traversible_chain` — carry one defect: the
> composition is **abelian**, so order is destroyed and holonomy is forced to the identity. Two say so
> in their own source. The remedy for the third exists in the same crate.

---

## 0a. WHAT RETURNED — all eight stations executed 2026-08-17

The record is
[`research/records/2026-08-17_THE_PHASE_IS_WIRED_THE_BAND_EDGE_IS_THE_REFLECTION_AND_THE_EXACT_CARRIER_HAS_A_COST_LAW.md`](../research/records/2026-08-17_THE_PHASE_IS_WIRED_THE_BAND_EDGE_IS_THE_REFLECTION_AND_THE_EXACT_CARRIER_HAS_A_COST_LAW.md).
`cargo test --workspace --lib` **2,380 passed, 0 failed, 19 ignored**.

| station | owner | what returned |
|---|---|---|
| one · the Clifford lift | `crates/holonic-engine/src/clifford.rs` | the algebra, with **24 of 64** basis-blade products differing from `multiquadratic` in sign alone and the magnitudes bit-identical; every prototype figure reproduced; the coboundary argument **run** rather than stated |
| two · the phase wire | `traversible_chain::PhasedTransfer` | a closed chain whose holonomy is **not** the identity while `det` still closes at one; non-commutation **iff** `sin φ ≠ 0` **and** `ρ ≠ 1`, both controls run; `P† J P = J`, so the conservation law survives the wire |
| three · the mouth | `soma/life/examples/the_deposit_conducts_and_the_later_current_rides_a_reflection.rs` | the arrival's own deposit distribution founds an admittance profile; the first grain was **blind** and the blindness is the return |
| four · the resonator | `traversible_chain::{StandingWaveReading, BlochReading, cavity}` | **`cos(α_edge) = |Γ|`** — the band edge is a rational rotation exactly when `ρ` is a rational square; `ρ = 3` lands on the order-six crystallographic rotation |
| five · the layered DAG | `crates/holonic-engine/examples/the_layered_lattice_is_compressed_by_its_own_receivers.rs` | material memory order **1**, not the declared depth; the **only irreducible collapse is at the terminal layer** — 151 sites in 39 blocks, all at `L−1`; both carriers agree, 104 device launches |
| six · the causal census | `crates/holonic-engine/examples/the_head_reads_the_aim_and_the_census_is_four_classes.rs` | **the falsifier fired** — the four-class census is a tautology at `d = 256`; what survives is the hand, split by a declared null into pairing (×2.9 on ANTI) and entry population (91% cohere after the shift) |
| seven · deposit then ride | same driver as three | **seven coordinates moved, six did not**, and the band class moved **PASS → STOP** |
| eight · the eight sites | `H.0266` and four more | all carry `G`; no registered claim changed truth value |

**And the run produced one correction to itself worth more than any station's green.** Handing
`pullback_inertia_bound` a `256 × 256` dense exact-rational form of 124-bit entries pinned one core
for nine minutes. The driver now fits its own cost law from its own sweep —
`t ~ 1.23e-6 · k^4.18`, projecting `k = 256` at **3.96 hours** — and **refuses the full extent by
projection rather than by a constant.** Nothing is wrong with `inertia.rs`; the caller owed it an
aperture and did not pay one. The general rule this earns: *before a deed on an exact carrier,
compute its cost from the measured entry width and the extent, and derive the aperture from that
number.*

---

## 0b. THE SURFACE CLAUSE — added 2026-08-17 at Brandon's direction, and it binds every station

**Brandon:** *"It is typically harder and more contaminating for us to retroactively ensure surface
utilization… as we approach complex problems that likely genuinely require GPU utilization for a
reasonable runtime the hardware surfaces become more relevant and important to secure; you can often
get away with neglecting the hardware surfaces for the experiments that don't require parallelized
compute for a lesser runtime."*

**Neither surface is a place and neither hosts the other** — `canon/THE_SURFACES_ARE_PATHS.md`, and
Brandon's 2026-08-13 ruling that the CPU is *"a bottleneck in a literal sense… a light-cone, a
pathway. Same for the GPU, they're just paths that work differently."* So the clause is not "put it
on the card"; it is **name the channel structure the deed's current actually needs, and say so in
the run.** The card's own doctrine is already ratified and is `GPU-first, not GPU-later`
(`cuda_refine.rs:3-6`, quoting him): *"every time we have to go from it not being integrated to
integrating it, you risk contamination."*

**And the diagnosis rule binds before the repair.** *"No GPU activity" is a symptom with at least
three distinct causes* — an aperture that cut real material to a toy, a bulk reduction left on the
wrong path, and a device call with no residency re-uploading an invariant operand. `CLAUDE.md`
requires measuring which one before repairing, and the third has a measured instance here: 4,096
questions of one 84 MB readout pushed roughly **343 GB** across the bus before `ResidentReadout::mount`
existed.

### Each station declares its channel, and three of the eight genuinely do not need the card

| station | material | channel, and why |
|---|---|---|
| one · the Clifford lift | four pairs at `d=3`, three keys at `d=4`, 64 blade products, one sparse pair at `d=512` | **serial path.** The deed is one product per pair over a single-digit population; measured **3 ms** wall. Parallelising it would be pure launch overhead. |
| two · the phase wire | ~40 exact-complex `2×2` products | **serial path**, same reason |
| three · the mouth | one deposit, one conduction | **measure before deciding.** `dimensional_wave` conducts a port ecology per tick; if the declared material is 8–13 items there is nothing for a card to carry, and that is the aperture defect rather than a surface defect |
| four · the resonator | a 5×10 band sweep, 8 cavity phases, 4 Sturm isolations | **serial path.** Measured **5 ms** wall. |
| five · the layered DAG | a transformer's own site lattice — sites × layers, with the product-order closure | **THE CARD, and it is already the law.** `receiver_exact_compression::compress_on_device` is the resident partition-refinement shell; `quotient_on_cpu` stands beside it as the exact reference, never as the implementation. A run of this station on the serial path has bypassed a standing card organ. |
| six · the causal census | a real head at `d ≥ 2048`, `N²` pairs | **THE CARD, and no new kernel.** See the aperture note below. |
| seven · deposit then ride | a conduction across a reflecting junction | **measure.** Same rule as three. |
| eight · the eight sites | documents | none |

### The aperture that makes station six a card deed rather than an impossible one

`d(d−1)/2` at `d = 2048` is 2,096,128 blade coordinates **per pair**, and `N²` pairs of those is not
a computation. But the four-class census **does not need the blade at all**:

```text
    aim     = ⟨q,k⟩                       one contraction
    area²   = ‖q‖²‖k‖² − ⟨q,k⟩²           Lagrange — the SAME products
    class   = sign(area² − aim²)          one exact comparison
```

So the whole census is **three dot products per pair**, `O(N²d)`, which is exactly `Q Kᵀ` plus two
diagonals — and `exact_readout_scores_batched` in `kernels/exact_embedding_fiber.cu` already computes
it in exact `__int128` with the readout resident and the queries crossing once.
**The blade is formed only to exhibit the plane for the largest population**, which is a bounded
exhibit the run declares. Nothing new is built; a fifth kernel here would be the explorative failure.

### What a station's return must carry about its surface

The device name, the resident octets, the launch geometry, and — where both paths ran — the **exact
work vector**, never elapsed time as the selector. `CLAUDE.md`: a cost is measured in work, a clock
may measure but may never select, and a nanosecond figure carries the frame it was taken in,
including whether the device had an active display.

**And the cost axis is Brandon's Landauer hypothesis, already folded into the roadmap.**
`Φ = P/(kT ln 2)` bounds **erasure and never transport**, so it prices the collapsing generators and
not the permuting ones — which puts it on station five and nowhere else in this plan, because station
five's collapsed population *is* the erasure, exhibited exactly with each pair's separating word. A
rebase with zero remainder costs nothing under this law, and stations one, two and four are rebases.

---

## STATION ONE — the Clifford lift (the organ)

**What.** A `d`-dimensional exact arrow in a library crate, over `Rat`: the scalar part, the 2-blade,
and the two spans, carried undivided.

```text
    aim     = Σᵢ aᵢbᵢ                          one rational
    cross   = (aᵢbⱼ − aⱼbᵢ)_{i<j}              d(d−1)/2 rationals — the 2-blade
    area²   = ‖a‖²‖b‖² − (a·b)²                Lagrange, cross-checked against the blade
    spans   = ‖a‖², ‖b‖²                       squared, so B⁻¹ = B/‖B‖² needs no root
```

with `divide(a,b) -> (quotient, remainder)`, the reconstruction law `a = q·b + rejection` asserted,
`Aim::{Cohere, Anti, Ortho}` lifted unchanged from `arrow.rs:36-39`, and the **exterior cocycle**
`σ(S,T) = (−1)^{#\{(i,j) : i∈S, j∈T, i>j\}}` as the multiplication's sign.

**Why this is one build and not two.** Station four of the superseded plan asserted `multiquadratic`
is the crossing-word algebra with the sign of the cross as the hand. **That algebra has no sign** —
its cocycle `∏_{i∈S∩T} kᵢ` is strictly positive and symmetric — and the obvious repair fails because
`μ(S) = (−1)^{|S|}` is a character, hence a coboundary, so twisting by it returns an isomorphic
algebra. The exterior sign is **not** a coboundary.

> **The crossing-word algebra that carries a hand is the even Clifford algebra, and
> `soul::FormedRotor { aim, cross }` is already its two-dimensional case.**

**Placement.** `crates/holonic-engine/src/` — it must not enter `soma/body`, which is `no_std` with
zero dependencies and typed at two dimensions by `Place`. The prototype to lift is
`crates/holonic-engine/examples/the_arrow_is_the_division_and_the_score_is_its_aim.rs:54-160`.

**Outcome.** A library carrier plus the driver rewritten against it, with the existing exact returns
reproduced: the aim-only reconstruction dropping `(0,1,−2)` on a generic pair and the *entire* vector
on an ortho pair; three keys at `d=4` with equal aim, equal area, and pairwise different blades.

**Expectation.** Bit-identical to the prototype's current output on the same material. If any figure
moves, the lift changed something and must say what.

**Falsifier.** The material must exhibit both collinear and non-collinear pairs, or the reading cannot
fail; the prototype already asserts this at `:268-271` and the lift must keep it. And the Clifford
product must be **non-commutative** on a witnessed pair — `e₁e₂ = −e₂e₁` exhibited — or the sign was
not installed and the whole station is decoration.

**Aperture.** `d(d−1)/2` blade coordinates. At `d = 2048` that is 2,096,128 rationals per pair, so the
census stations below must declare a subspace or a sampling and say which; a silent truncation would
read as coverage.

---

## STATION TWO — the phase wire (three defects, one edit)

**What.** Wire the exact propagation phase into `traversible_chain`, which states in its own source
(`:80-86`) that it owns none and that its holonomy is therefore *"the identity by construction… That
receipt could not have come out otherwise."*

**The parts, both standing.** `analytic_field.rs:1144-1156` — `ExactStratifiedLayer` carrying a
declared exact phase on the unit conic. `dimensional_wave.rs:1012-1015` — one applied per port, with
the reverse carrying its inverse.

**Why it works.** A rotation anticommutes with the interface matrix's off-diagonal part, which is
exactly the non-commuting link the module says it lacks.

**Outcome.** A closed chain whose holonomy is **not** the identity, with the phase declared.

**CITATION CORRECTED 2026-08-17.** This read *"the band structure read off `BandReading`
(the citation named a span of `dimensional_wave.rs`)"* and both halves were wrong: `BandReading` lives at
`crates/holonic-engine/src/traversible_chain.rs:713`, and it is a **twist census** — per-junction
inversion parity, the Möbius reading — not a band structure. There was no band structure anywhere to
read off. Building one is station four's content, and the two stations are one driver because they
are one carrier.

**Expectation.** Non-trivial holonomy on any chain whose phases do not sum to a whole turn.

**Falsifier, and it is the module's own.** `the_interface_family_is_abelian_which_is_why_its_holonomy_is_forced`
must **fail** after the wire on a phased chain and must still **pass** on an unphased one. If both
still pass, the phase is not in the loop.

**The exactness bound is a theorem, not a limit.** Rational rotations are the Niven angles, so exact
bands exist at the crystallographic orders — `winding_inertia::lattice_admits_order` owns exactly that
row — and past those the algebraic extension is required, for which `contact_gluing.rs:843-905`
already calls `multiquadratic::exact_sine` and carries `cos = 1/2 → sin = √3/2` with its generator
named. A chain whose phase leaves `ℚ` must return the extension, never an approximation.

---

## STATION THREE — the mouth onto the conducting carrier (the second wire)

**What.** Join the deposit to the conduction. `admit_later` (`incidence_production.rs:2113`) deposits
into an `IncidenceComplex`; `dimensional_wave` conducts on a port ecology; `diffusion.rs` is immutable
after `new` — constructor only, no `&mut self`. Three carriers, one law.

`soma/life` already depends on `holonic-engine`, so the dependency edge points the right way. This is
a carrier translation, not an organ.

**Outcome.** A prompt deposited at a site, conducted, reflected at junctions, and read at the
boundary — with `reached / reopened / saturated / untouched` returned from the mouth and a departure
receipt per port per tick from the conduction.

**Expectation.** The two ways to float are both reachable: material that arrives and causes nothing
(`saturated`) and material that reaches nothing (`untouched`).

**Falsifier.** The deposit-then-ride ablation of station seven. Without it this station has moved
bytes and proved nothing.

**Two standing bans this station must not break.** `2026-07-19_THE_STRESS…:308` bans a
*coarse-graining module* inside Soma — a receiver-**declared** collapse is lawful, an organ that
performs one is not. And `traversible_chain.rs:146` records that its `energy_residual` is
identically zero **algebraically** for its convention, so no receipt may quote it as evidence.

---

## STATION FOUR — ask the resonator what it resonates at (reading one)

**What.** `dimensional_wave` is a delay-line network with exact n-port scattering, per-port delay, and
exact phase, whose passive energy residual is forced identically zero or the event refused. **A
waveguide with a mismatched termination has standing waves, and nothing has ever asked.**

Measured 2026-08-17, with scope: `grep -rniE "standing[ _-]?wave" crates soma --include='*.rs'` → two
hits, both negations. `grep -rn "impedance" crates soma --include='*.rs' | grep -v examples` → **zero
in any library `src`**. The quantity owned is admittance — 76 in `analytic_field.rs`, 62 in
`traversible_chain.rs`, 35 in `dimensional_wave.rs`. Its one driver is about tapers.

**Outcome.** A standing-wave reading: the ratio, the resonant modes, the band edges, and the `Tr(M)`
pass/stop classification, all exact over `Rat` or returned in the declared extension.

**Expectation.** Non-trivial on a mismatched termination and **trivial on a matched one** — the second
half is the control, and a run without it has not measured resonance.

**Falsifier.** If a matched termination also returns standing waves, the reading is measuring the
instrument.

---

## STATION FIVE — the layered DAG through the compression organ (reading two)

**What.** Implement `ObservedSystem` (`receiver_exact_compression.rs:81-87`) over a transformer's own
site lattice: `items` = sites `(i, ℓ)`, `inputs` = the admitted transports, `receivers` = declared
output faces, `successor` = the product order `(j,ℓ) ⇝ (i,ℓ') ⟺ j ≤ i ∧ ℓ ≤ ℓ'`.

**Outcome.** The collapsed population **with the shortest word separating each pair**, and the memory
order — how far back the reading had to look. That is the exact object superposition is the lossy
analogue of, and the network never returns it.

**Expectation.** A non-empty collapsed population with a memory order greater than one; a memory order
of `None` would say the lattice is memoryless for the declared family, which would be a real return
and a surprising one.

**Falsifier, and it is the authored-partition test.** Which declared input, if varied across two
members of one returned block, would move them apart? If the answer is a field this driver wrote, the
partition is authored. The receivers must be declared **before** the run and exhibited in it.

---

## STATION SIX — the causal census on a real head (reading three)

**What.** Station three of the superseded plan, widened by a finding that supersedes its own framing.
Read a real model through the standing safetensors intake — `the_foreign_map_founds_its_axes.rs`,
`the_readout_founds_its_own_receivers.rs`, `the_readout_returns_a_fiber_not_a_winner.rs` — and take the
census per head.

**Widened, and this is the correction.** Report
`Causal::{TransportDominant, Balanced, StorageDominant, Unread}` rather than `Aim::Ortho` alone.
`arrow.rs:159-177` records that `founds()` cannot separate the non-point `[0:0]` from the honest point
`[0:1]`; **only `causal_class()`, which reads the pair, can.** A zero attention score therefore
conflates two utterly different causal facts — the pure orthogonal turn where the gyration is
*maximal*, and a relating behind that pole's own horizon with no causal character at all.

**And the form must not be a Gram matrix.** `inertia.rs:5-22` exists because that exact defect already
happened here: `MᵀM`'s positivity *"could not fail on any input whatsoever."* `In(K†K)` is
`(rank K, d_k − rank K, 0)` by construction, and `z ≥ N − d_k` whenever more keys than coordinates are
supplied, which would make "collapse" grow with sequence length. **The principled form is declared
first:** for a query family `{q_a}` with `A : k ↦ (q_a(k))_a` and a declared positive weighting `W`,

```text
    F_R = A†WA          and          ker F_R = ker A
```

— exactly the key directions invisible to every declared query.

**Outcome.** A per-head census of the four causal classes, with blades exhibited for the largest
population, and `ker F_R` reported against `d_k`.

**Expectation.** A non-trivial `Unread` population separate from the `Ortho` one. If they coincide the
widening bought nothing and the run says so.

**Falsifier.** If every head's census is empty or uniform, the blindness is real in principle and
absent in practice on this model, and this plan reports that rather than the principle.

**Aperture.** Exact rank over a rational lift of stored IEEE values is discontinuously sensitive and
will commonly be full; the run must declare its subspace or sampling and must not report a full-rank
result as a discovery.

---

## STATION SEVEN — deposit, then ride, across a reflecting junction (reading four)

**What.** The founding claim's real falsifier. Two drivers already have the shape —
`soma/life/examples/the_map_deposits_and_a_later_current_rides_it.rs` and
`the_later_current_rides_the_deposit.rs`, both driving `admit_later` twice — and **neither has been run
with a reflecting junction between the deposit and the later ride.**

**Outcome.** Deposit A, record the axes founded; deposit B; and measure whether B's conduct differs
according to whether A was deposited.

**Expectation.** It differs, and the difference is attributable to named foundings.

**Falsifier, and it is the whole station.** If B's conduct is bit-identical with and without A, the
foundings were decorative — *a contact that changes no pathway taught the body nothing.* And the
second arm: if the founded classes trace back to admittances this driver declared per junction, the
class is the preimage of an authored field however exact the arithmetic between them.
`traversible_chain.rs:88-99` already anticipates it — an admittance is *"how much of an arriving
current a site can take,"* derived from what the site shares with the current.

---

## STATION EIGHT — the eight sites (the document repair)

**What.** `Σᵢ|aᵢ⟩⟨aᵢ| = I` is load-bearing at eight places: `H.0266`'s registry owner
`papers/source/mathematics/definitions/bra-receiver-ket-construction.typ:43-53`; its restatement in
`topology-analysis-dynamics.typ:868`; a registered object depending on it in
`mathematical-physics.typ:610`; a paper importing it; the catalogue entry; the `ketbra` macro in
`lib/dirac.typ`; `canon/TABLET_THE_OPERATIONS.md:65`; and `CLAUDE.md:349`.

The line requires an orthonormal or Parseval family. For a generic family the sum is a **frame
operator**, not a projector, and reconstruction requires the dual frame. `H.0266` already handles the
sub-projection case; it does not handle the family being non-orthogonal at all.

**The repair language is deposited and ratified.**
`2026-07-20_THE_EULER_DIFFERENCE_REBASES_THE_METRIC…:236-258` (`FORMULA §CXXV`):

```text
    P G(x − P^[p]x) = 0     ⟹     P^[p] = [(PGP)|_range P]⁻¹ P G        (IV.5)
    with G = J*J                                                        (V.3)
    "The relation between those words, the available currents, and orthogonality
     is receiver-relative."
```

`[(PGP)|_range P]⁻¹ PG` **is** the dual-frame formula.

**Outcome.** Each of the eight carries its metric, with the frame-operator case named and the
non-orthogonal reconstruction pointed at the July deposit.

**Expectation.** No registered claim changes truth value; the change is that `G` is carried rather
than assumed.

**Falsifier.** `typst` and `claim-index` gates green, and any registered object whose `depends`
includes `H.0266` must still compile and still say what it said.

---

## What is refused throughout

- **No floats, and no square roots.** Lagrange supplies `‖a∧b‖²`; the polar form is never taken.
- **No Gram matrix as a discovery.** A form must be declared before it is measured, or it returns its
  own construction.
- **No coarse-graining organ inside Soma.** A receiver-declared collapse is lawful; a module that
  performs one is banned by a ratified July record.
- **No `winding_inertia` on non-circulant material** without its own refusal exhibited — its aperture
  is symmetric circulant and it refuses by name.
- **No receipt quoting `energy_residual`**, which is algebraically zero for its convention.
- **No count where a population is owed.** Every collapsed pair carries its separating word.

## What this plan does not claim

Superposition as a consequence of the rank budget is a **correspondence, not a derivation** — it needs
a rule for what happens when founding is demanded and the budget is exhausted, and nothing here
implements one. "A transformer cannot found an axis" is **withdrawn**: `V`, `W_O` and the MLP write
genuinely new directions, the budget is the context rather than `d_model`, and the honest residue is
that the founding channel has a one-symbol-per-step aperture with a collapse at it — *the deposit is
real; the blade does not survive the deposit.* And the Plinko identification with `multiquadratic` is
**false as stated**: Hamming weight is not a homomorphism from `(ℤ/2)ⁿ`, the path expansion is
multiplicative at the depth axis with `nᴸ` paths rather than `2ⁿ`, and the binomial is the degenerate
uniform case.
