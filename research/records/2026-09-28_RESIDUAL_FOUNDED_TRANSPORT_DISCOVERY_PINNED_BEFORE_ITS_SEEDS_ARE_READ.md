# Residual-founded transport discovery, pinned before its seeds were read

**Date:** 2026-09-28. Refs #63, #73. **Scope:** the first item of THE_REBUILD's ring-search row
("residual-founded transport discovery first",
[§4](../../docs/plans/THE_REBUILD.md#4-the-open-joins-and-the-learners-necessities-each-disposed)):
the founding law of the [learner record's §14.1](2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md#141-birth)
(atlas `birth.separator-transport-closure`) as one Rust owner with its Lean counterpart, and its
consumer on the moiré, a terrain with known truth. The pins below were committed before any pinned
seed was drawn or read. The receipt follows them.

The computational object is the helical pair interaction, read at a receiver's birth. Of the winding
guide's six objects the item touches the **helix** (the admitted transports: each grating's rotor,
circle plus carry), the **tube** (the passage's clocked span over which the residual is read at the
receiver's section, and the closure's rungs) and **faces and placement** (the founded faces `φ_i`,
the readout `D`, the founded family's face). The pair (the gratings' locks, which the joint torus
holds and no founded face reads), the cell holonomy (none is claimed) and the tower thread (no
restriction is founded) stay attached.

## 1. The law and its owners

[proved-derived; formal-checked] In a finite chart `X` over a field, with the admitted transports
`T_a` known and the receiving forms `V_old` held, a reached covector `λ_r ∉ V_old` founds

```text
V₀ = V_old + span{λ_r},   V_(n+1) = V_n + Σ_a T_a* V_n            (T_a* φ = φ ∘ T_a)
dim V₀ = dim V_old + 1                                             (opening_finrank)
strict steps ≤ dim X − dim V₀; once one step is still, all are    (strict_steps_le_chart, ladder_stable_forever)
the stable rung V is T_a*-invariant, the least such space ⊇ V₀    (founded_invariant, founded_le)
φ_i a basis of V, T_a* φ_i = Σ_j U_(a,ij) φ_j  ⇒  E T_a = U_a E    (exists_transport_matrices, founding_intertwines)
ρ = Σ_j D_j φ_j  ⇒  ρ = D E                                        (encode_reads)
```

Lean `Compression/Landmark/Context/Birth` (the ladder for any endomorphisms of a vector space, read
at `W = Dual K X`, `S_a = (T_a).dualMap`). It constructs an observable transport representation and
does not infer an unknown `T_a` ([counterexample] `Computation/NavigatorObservationScope`; learning
an unknown finite-state transport needs equivalence queries).

[definition; agent-inferred] **The Rust owner is `receiver::population::birth`**: a navigator founded
from a residual is a birth in the receiver's population, paid from its reserved mass
(`Population::found`) and identified across aeons by its declaration. It holds:
- `Closure::found`: independence decided in a prime chart (an image independent mod `p` is
  independent over ℚ), the dependents' coordinates read at once from the certified kernel of
  `[φ | dependents]` (`ratio::linear`), each dependent certified inside the rung the ladder puts it
  in, an unlucky chart retried in the next (at most four); `Closure::check` then verifies
  `E T_a = U_a E` row by row over ℚ, and `found` returns nothing that fails it. Typed refusals: a
  chart that is not finite, a transport not declared, a covector that separates nothing, a reading
  outside the founded forms, a founded reading that is not one class.
- `FoundedFamily`: survivor filtering over the chart's states `e_s`, each carried as `z_s = E e_s`,
  advanced by `U_a`, read by `D` (a class of states with one configuration is future-equivalent:
  the quotient by `ker E`). Its code is `log₂ d − log₂ #S`.
- `TransportBirth`: the declaration (chart, admitted transports, coupling `ρ`, held forms, tick,
  description `ℓ_g`); `reached(κ) = ρ*κ`; `found`; `moire(rates, class, ℓ_g)`, the gratings' joint
  port torus `d = Π q_i` read through the terrain's own `Grating::{port, sheet}` (rates only; the
  phases are the key).
- `SectionFounding`: the population's own trigger, at the section every `section_period` cells when
  the code since the previous section passes `ℓ_g`.

**Which covector reaches** [definition; agent-inferred]. The comparison at the arrival `y` is
`κ = e_y − q`; it reaches the chart through the coupling's adjoint, `λ_r = ρ*κ`. On a binary
alphabet `κ = q_(y′)(e_y − e_(y′))`, so `λ_r = q_(y′)(ρ_y − ρ_(y′))`: the polarized reading scaled
by the surprise mass. Its span is the polarized reading's whenever `q_(y′) > 0`, decided on the
population's enclosed face, and the founding reads only the span. `V_old = span{1}`, the mass form.

**The founded dimension against the truth's** [proved-derived]. For a permutation of a finite state
set, the emission from `x₀` is `y_t = ρ(T^t x₀)`, and the span of its shifts is the restriction of
`span{T*^t ρ}` to the orbit of `x₀`. So its Hankel rank is at most the founded dimension, with
equality when the torus is one orbit, and otherwise exactly when no nonzero founded form vanishes on
the visited orbit (and the mass form's restriction lies in the shifts' span, which holds whenever a
period carries a one).

## 2. The pins

1. **Terrain.** The moiré's parity color: `k = 3` gratings drawn from `MoireFamily { rings: 3,
   denominator: 8 }` by `Moire::draw`, on the eight fresh seeds `2026092881` to `2026092888`,
   `n = 2^14` cells.
2. **The control (without the birth).** The receiving tree at every depth of the ladder `1, 2, 4, 8,
   16, 32` and the parity gratings over `MoireFamily { rings: 2, denominator: 8 }` (the receiver
   expected two gratings), each named by `3` bits (seven families and the founding's slot):
   `M = 7/8`, the reserve `1/8`.
3. **The founding (with the birth).** The same population, through `SectionFounding` over
   `TransportBirth::moire` of the three drawn gratings' rates (the known `T_a`), the section every
   `2^8` cells. Its description, charged once in the prior, is `ℓ_g = 3 + ⌈log₂ R³⌉ = 17` bits: its
   slot, and the three rates named among the family's `R = Σ_(q=2)^8 φ(q) = 21` rates a ring
   (`21³ = 9261 = 3³·7³`). The phases are not declared.
4. **The truth.** The emission's observable dimension is the rank of its Hankel matrix over one least
   period `L`, `[y_((i+j) mod L)]_(i,j<L)`. Its code after the birth is `log₂ d − log₂ #S`, `S` the
   torus states at the birth cell whose emission, read through `Grating::sheet`, is the passage
   after it.
5. **The acceptance, on every seed.**
   1. `E T = U E` exactly (`Closure::found` returns nothing else) with at most `d − dim V₀ ≤ d`
      strict steps.
   2. The founded dimension equals the Hankel rank.
   3. The population's code after the birth, `code(n) − code(t_g)`, is at most the truth's code
      after the birth plus the declared margin `−log₂(m_g/M_n)` (the newborn's charge in the founded
      mass), decided on the enclosures.
   4. With the birth the population codes the whole passage strictly below the control, every
      charge in both codes, decided on the enclosures.

   A seed on which no section's residual passes `ℓ_g` founds nothing, and fails (3) and (4) with
   that named.
6. **The failure branch.** A failed item is named by its measurement. The law stays in Lean and the
   objects guide if no consumer earns it; unconsumed Rust is not kept.
7. **Budgets.** Projected before the run by `birth-probe` (below) against ten minutes and 20 GB.

The command: `cargo run --release -p holonics --example hnn_population -- birth` (the harness
`research/notebook/hnn_design/hnn_population_birth.rs`).

## 3. The projection

`birth-probe` reads no pinned seed. On the largest single orbit the family admits (rates `1/8`,
`1/7`, `1/5`, `d = 280`), the founding took 73 ms (dimension 141 after 139 strict steps, one prime
chart; `23430646` multiplications, peak width 2 bits), and both populations over `2^12` cells of a
hand moiré on that orbit took 122 ms and 451 ms, with a peak resident set of 42,900 KiB. Projected
for the run: at most `d = 512` states, eight seeds of two `2^14`-cell populations each, at most
five seconds a seed and under 200 MiB, far inside ten minutes and 20 GB.

## 4. The receipt

`[established-bounded; measured]` The pinned run, `hnn_population birth` in release after the pin
commit `4a452884`: 10,882 ms of exterior wall for the eight seeds and a peak resident set of
53,744 KiB, inside the projection. Codes are enclosures with exact endpoints, read at `L_R = 16`
as `n + k/16 + ε`, `0 ≤ ε < 1/16`.

| seed | rates | `d` | orbits `d/L` | least period | Hankel rank | the declared two-ring gratings | control's code | founded |
|---|---|---|---|---|---|---|---|---|
| 2026092881 | `3/8, 3/8, 4/7` | `448 = 2⁶·7` | 8 | 28 | 28 | died at cell 13 | `162 + 13/16 + ε` | no |
| 2026092882 | `4/5, 5/8, 1/5` | `200 = 2³·5²` | 5 | 40 | 21 | survived | `13 + 10/16 + ε` | no |
| 2026092883 | `4/5, 5/6, 6/7` | `210 = 2·3·5·7` | 1 | 210 | 106 | died at cell 11 | `943 + 4/16 + ε` | at cell 512 |
| 2026092884 | `2/7, 5/7, 5/7` | `343 = 7³` | 49 | 7 | 7 | died at cell 8 | `57 + 4/16 + ε` | no |
| 2026092885 | `3/4, 4/7, 7/8` | `224 = 2⁵·7` | 4 | 56 | 29 | survived | `13 + 10/16 + ε` | no |
| 2026092886 | `2/7, 5/8, 3/7` | `392 = 2³·7²` | 7 | 56 | 29 | survived | `13 + 10/16 + ε` | no |
| 2026092887 | `5/8, 3/5, 1/7` | `280 = 2³·5·7` | 1 | 280 | 141 | died at cell 9 | `1201 + 8/16 + ε` | at cell 512 |
| 2026092888 | `1/6, 4/7, 1/3` | `126 = 2·3²·7` | 3 | 42 | 22 | survived | `13 + 10/16 + ε` | no |

The two foundings, each at the second section (cell 512) from one prime chart, `V_old` the mass
form (`dim 1`):

| | 2026092883 | 2026092887 |
|---|---|---|
| arrival and residual since the previous section | class 1, `199 + 13/16 + ε` | class 0, `234 + 0/16 + ε` |
| rungs `dim V₀ … dim V` | `2, 3, …, 106` | `2, 3, …, 141` |
| (1) strict steps against `d − dim V₀` | 104 ≤ 208 | 139 ≤ 278 |
| `E T = U E`, `D E = ρ` | exact | exact |
| (2) founded dimension against the Hankel rank | 106 = 106 | 141 = 141 |
| founding work: additions, multiplications, divisions, peak width | 71868, 11741781, 212, 2 bits | 125208, 23361894, 282, 2 bits |
| founding wall time (the section's cell, exterior) | 38 ms | 66 ms |
| the truth after the birth: `#S` of `d`, code | 1 of 210, `7 + 11/16 + ε` | 1 of 280, `8 + 2/16 + ε` |
| the newborn's own code | equal to the truth's, exactly | equal to the truth's, exactly |
| the population after the birth | `24 + 8/16 + ε` | `24 + 14/16 + ε` |
| the margin `−log₂(m_g/M_n)`, `m_g = 2^(−17)`, `M_n = 7/8 + 2^(−17)` | `16 + 12/16 + ε` | `16 + 12/16 + ε` |
| (3) after the birth, less the truth, less the margin | inside `[−3/2^97, 3/2^97]`: undecided | inside `[−3/2^97, 3/2^97]`: undecided |
| (4) with the birth, against the control | `478 + 9/16 + ε` against `943 + 4/16 + ε`: `−465 + 4/16 + ε`, strictly below | `519 + 14/16 + ε` against `1201 + 8/16 + ε`: `−682 + 5/16 + ε`, strictly below |
| the newborn's acts | `Read` 16299, `Transport` 16090 | `Read` 16410, `Transport` 16131 |
| both populations' wall time | 1492 ms with, 506 ms without | 1904 ms with, 588 ms without |

**The verdict: the acceptance fails as pinned.** Six of the eight seeds founded nothing, so they
fail (3) and (4) as the pins state; on the two that founded, (1), (2) and (4) pass and (3) is
undecided. The separating terms, by their measurements:
- **The declared families did not fail on six seeds.** On four (2026092882, 885, 886 and 888) the
  declared two-ring parity gratings survived the whole passage and coded it at `13 + 10/16 + ε`
  bits: those three-ring parity words are two-ring parity words (the parity class locates a word,
  not its rings: `receiver::population::families`, "The parity class locates its word"). On two
  (2026092881 and 884) the two-ring gratings died by cell 13, but the trees read the short periods
  (28 and 7) within the opening section, and the whole passage cost `162 + 13/16 + ε` and
  `57 + 4/16 + ε` bits, so no later section's residual passed `ℓ_g = 17`. There was no residual to
  found from, and none was founded. The pin's premise (the declared families fail) held on the two
  seeds whose torus is one long orbit.
- **(3) is attained, not refuted.** After the birth the population's code is the truth's plus the
  margin to within `3/2^97` bits. The telescope's slack is `−log₂(1 + Σ_f m_f L_f / (m_g W_(t_g) L_g))`,
  the declared families' remaining mass after the birth, and it lies below the enclosure's grid,
  so "decided on the enclosures" cannot hold. The bound itself is the population's birth telescope,
  whose Lean statement is owed (#62).

**What the founding did where a residual existed.** On 2026092883 and 2026092887 the population met
a passage its declared families failed (the two-ring gratings died; the trees paid `199 + 13/16`
and `234` bits in the section before the founding). The reached covector, the polarized parity
reading, closed under the three rotors in one strict step a rung, to exactly the emission's Hankel
rank; the founded family located the phases to one state of the torus and coded the rest of the
passage at the truth exactly; with every charge included, the population with the birth less the
control read `−465 + 4/16 + ε` and `−682 + 5/16 + ε` bits. The measured work was 11,741,781 and 23,361,894 machine-word
and rational multiplications in 38 and 66 ms.

## 5. A diagnostic after the run

`[established-bounded; measured]` Not an acceptance: `hnn_population birth-dimensions`, added after
the pinned run, founds the closure on every pinned seed from the polarized reading, whether or not
a section would, and reads the founded forms restricted to the visited orbit.

| seed | orbits | founded dimension | restricted to the visited orbit | Hankel rank | the forms silent on the orbit |
|---|---|---|---|---|---|
| 2026092881 | 8 | 29 | 28 | 28 | one, `T*v = v`: a conserved charge, values `−6, −4, −2, 0, 2` |
| 2026092882 | 5 | 21 | 21 | 21 | none |
| 2026092883 | 1 | 106 | 106 | 106 | none |
| 2026092884 | 49 | 8 | 7 | 7 | one, `T*v = v`: a conserved charge, values `−4, 0` |
| 2026092885 | 4 | 29 | 29 | 29 | none |
| 2026092886 | 7 | 29 | 29 | 29 | none |
| 2026092887 | 1 | 141 | 141 | 141 | none |
| 2026092888 | 3 | 22 | 22 | 22 | none |

The restriction's rank equals the Hankel rank on all eight, as §1 derives. The founded dimension
equals it on six and exceeds it by one on two (`3/8, 3/8, 4/7` and `2/7, 5/7, 5/7`). On those two
the parity reading averages differently over different orbits: rings of one period keep their
relative phase along an orbit, and no balanced sheet of a coprime period (a `q = 8` ring beside the
others, as on 2026092882) evens the average out. So the founded forms carry the orbit's label, a
conserved charge constant along each orbit and zero on the visited one. So the founding law gives
the chart's observable representation, whose dimension exceeds the emission's minimal realization
by exactly the conserved charges the visited orbit does not vary (Lean
`Birth.{silent_invariant, eigenvalue_of_finite_order}`: the silent forms are invariant, their
rational eigenvalues `±1`). Had (2) been read on 2026092881 or 884, it would have failed by that
one charge.

## 6. Dispositions

- **The owner stays.** A consumer earned it where a residual existed: on both seeds that founded,
  the newborn coded at the truth exactly and the population coded hundreds of bits below the
  control, every charge included. The Rust owner, its tests and the Lean stay; the atlas rows
  `birth.*` name them.
- **The rotor crib** was not run: the loop's failed premise is its next subject, not a second
  terrain.
- **Owed to #62:** (a) the Hankel-rank identification: for a permutation `T` of a finite state set
  and a reading `ρ`, the rank of the emission's Hankel matrix from `x₀` equals the rank of
  `span{T*ᵗ ρ}` restricted to the orbit of `x₀` (Lean holds the invariance of the silent forms and
  their `±1` eigenvalues, not the rank equality); (b) the abstaining newborn's telescope, already
  owed, which bound (3) reads.
