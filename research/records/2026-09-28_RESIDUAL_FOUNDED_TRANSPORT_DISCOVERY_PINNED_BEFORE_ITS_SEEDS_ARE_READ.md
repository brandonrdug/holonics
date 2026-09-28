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

To be appended by the run.
