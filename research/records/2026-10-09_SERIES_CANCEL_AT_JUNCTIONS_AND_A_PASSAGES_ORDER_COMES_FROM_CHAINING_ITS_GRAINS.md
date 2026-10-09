# Series cancel at junctions, and a passage's order comes from chaining its grains

**Date.** October 9 (the lenses: October 1 and October 2). **Issues.** #73, #62, #63. **Grade.** Lens
record. Each section carries its own grade. The identities of §2.1 and §3.1 are checked here by
exact computation; the owners cited are formal-checked unless marked; the joins in §5 are owed.

**Why one record.** Both lenses ask what composition at a junction keeps, and the repository already
has one definition that holds both: causal time parity, under which adjacent grains share one time
face with opposed orientations, so interior faces cancel in the composed boundary (§2.2). Series
cancellation is what that composition does to the series that meet at a junction. Time parity is
what a single grain cannot supply by itself: the orientation, which the chain of grains or a wider
receiver supplies.

## 1. The lenses

Brandon, October 1: read the computation as a graph of intersecting equations whose series
expansions meet. Ideally the exact series ratios cancel along the intersections, at the junctions
and pivots, and that simplifies the computation of the whole graph. This is the calculus side of
what the agents had been doing with "damping" and physics, and they keep splitting the subjects
because they do not see the connection between the calculus and the physical motion. The modulo is
for flux, for complex Euler and Navier–Stokes. Outward flux can stabilize inner flux: it is one more
interior ↔ exterior relation, as in vortices.

Brandon, October 2, on the release locking together stations whose order its readings cannot
certify:
- Time parity: order comes from chaining grains. If the algorithm cannot see the orientation of a
  flux from where it stands, the flux is probably non-orientable at that grain.
- A cross-section of a channel's water cannot tell where the potential driving the whole channel
  comes from. An observer of the whole body of water moving relative to land can orient the flux.
- Time parity is non-orientable whenever events are not clearly reversible from the grain's
  perspective. A reversible action is part of a wider lens, and the flux of the higher grain
  reveals the constraint.
- Words in a sentence whose order can be reversed without changing the meaning are the same case:
  without a relevant context the meanings of the parts are reversible and depend on one another.

## 2. Series cancel at junctions

### 2.1 Elimination at a pivot

[proved-standard; checked by exact computation; owner] Partition a linear constitution into
boundary and interior, `K = [[A, B], [C, D]]`. Eliminating the interior at its pivot `D` leaves the
boundary operator `S = A − B D⁻¹ C` (Schur complement; Kron reduction on a network). Where the
interior's pivot is `D = I − N`, with `N` its returns of spectral radius below one,
`D⁻¹ = Σ_(k≥0) Nᵏ` sums every excursion through the interior, and the finite form is the geometric
remainder `(Σ_(k<n) Nᵏ)(I − N) = I − Nⁿ`. The pivot replaces the interior's series of returns by one
ratio. This is the cancellation Brandon names.
- *Example.* Two conductances `g₁ = 2`, `g₂ = 3` in series through one interior junction. Eliminating
  the junction gives `S = g·[[1, −1], [−1, 1]]` with `g = g₁g₂/(g₁ + g₂) = 6/5`: the junction's
  potential cancels and the series rule appears.
- *Owner.* HNN_FORMULA already states this reduction for the diffusion step `M = C + τ dᵀW d`, with
  the source and the retained interior surviving in the boundary operator. It names the Schur
  transfer integration by reflection, the discrete `Λ_DN`
  ([reflection, leaders and recursive packing](../../docs/HNN_FORMULA.md#reflection-leaders-and-recursive-packing)).
  The lens's new content is that the cancellation is the calculus of the physical damping, not a
  separate subject.

[proved-derived; formal-checked owners] **The lawful form keeps the interior's memory.** Eliminating
the interior of a dynamic Holon gives one boundary operator, `(sI − A − B(sI − D)⁻¹C) x̂ = x(0) + f̂ +
B(sI − D)⁻¹(z(0) + ĝ)`. The dynamic Schur response, the interior memory and the state-space resolvent
are one coupled equation, and the initial interior survives each (atlas `resolvent.dynamic-schur`,
[HNN_FORMULA](../../docs/HNN_FORMULA.md#state-space-convolution-and-diffusion-are-one-realization)).
Eliminating an interior keeps a dynamical boundary memory with kernel `B e^((t−s)D) C`, and a static
Schur elimination can fail even for a passive oscillator (atlas `fluid.boundary-memory`; Lean
`Physics/ReflectedBoundaryMemory.reflectedResidual_rate`). This is Brandon's outward flux that
stabilizes inner flux: the exterior's return is the memory term, and an elimination that drops it is
not lawful.

### 2.2 Interior faces cancel at every join

[definition; formal-checked owners] The repository already states and proves the cancellation at
each kind of join.
- **Causal time parity** (project definition `definition:causal-time-parity`, the paper
  `mathematics/definitions/causal-time-parity.typ`, cited by the
  [HNN/Athena foundation plan](../../docs/plans/HNN_ATHENA_FOUNDATION.md#4-the-receiver-kernel-natural-grain-and-retained-continuation)).
  A causal grain from a receiving cut `Σ_k` to a later cut `Σ_(k+1)` has boundary
  `∂E_k = Σ_(k+1) − Σ_k + Γ_k`, with `Γ_k` its lateral world boundary. When the output cut of each
  grain is the input cut of the next with opposed induced orientation,
  `∂(Σ_(k=m)^(n−1) E_k) = Σ_n − Σ_m + Σ_k Γ_k`. Every interior time face cancels from the composed
  boundary and stays in the causal interior. Between adjacent chain degrees the same law is the
  incidence content of `∂∂ = 0` and the discrete face of telescoping. The definition says what it
  is not: not an inverse event, not reversibility.
- A serial join of addressed passages returns incoming, middle and outgoing, and the middle face
  cancels through the pullback equality (atlas `holon.addressed-boundary-join`; Lean
  `Foundation/AddressedBoundary.boundary_join`).
- Joined control volumes: any return placed on the shared face cancels exactly (atlas
  `fluid.balance-join`; `Physics/Fluid/ControlVolume.outflow_join_ignores_sharedFace`).
- A route's adjoint return telescopes to its ends: the interior cancels, the origin gives and the
  terminus receives (atlas `learn.route-deposit`;
  `Computation/HolonicWorldReturnDeposit.twoStep_interior_cancels`).
- Finite telescoping and the geometric remainder (atlas `jet.telescoping`;
  `Geometry/Telescoping.finite_telescoping`, `finite_geometric_remainder`).
- The junction's energy ledger is Tellegen's (atlas `tube.junction-gauss-tellegen`;
  `Transport/JunctionLaw.tellegen`; `Holon/Dirac.tellegen`, `kirchhoff_isDirac`), and composition
  preserves the Dirac property (`Holon/Dirac.compose_isDirac`).
- The HNN's junction scattering is an involutive isometry of the admittance-weighted energy, so the
  junction contributes zero power (atlas `hnn.junction-scattering`;
  `HNN/Propagation.junctionScattering_involutive`, `junctionScattering_isometry`).

[proved-standard; formal-checked owner] **The series cancel only if the ratio is carried as its
pair.** A receiving junction that merges a contribution of mass `a` and value `v` into a held mean
`y` of mass `M` moves it by `y′ − y = a(v − y)/(M + a)`, since `y′ = (My + av)/(M + a)`. The update
composes exactly when the pair `(M, J = My)` is carried, `(M, J) ⊕ (a, av) = (M + a, J + av)`: the
pair composes associatively, and an unweighted running mean does not, `((0 + 0)/2 + 4)/2 ≠
(0 + (0 + 4)/2)/2` (atlas `norm.mass-current-associative`;
`Computation/AttentionModeCompression.weighted_summary_associative`, `unweighted_mean_not_associative`).
This is the ratio law, "one per two" before it is a number, applied at a junction. Dividing early is
what stops the series from cancelling.

[agent-inferred] **Cancellation is not damping.** A junction contributes zero power, so cancellation
there redistributes or conserves. Damping needs an energy decrease inside a dissipative element or
a flux that leaves through a port. The interior's balance and the exterior's carry that flux with
opposite signs, and the boundary memory keeps it. "Damping" read at a junction is therefore always
the exterior's return, never the junction's own loss.

## 3. A passage's order comes from chaining its grains

[definition; agent-inferred reading] Brandon's reading that order comes from chaining grains is
causal time parity read for orientation. The composed boundary `Σ_n − Σ_m + Σ_k Γ_k` carries the
order of the whole chain. A single grain contributes its orientation only when its shared faces are
matched, with occurrence, frame and clock data at the selected grain, as the foundation plan
requires. The
notation guide already separates three states: unoriented, oriented relative to a frame, and
non-orientable, a nontrivial holonomy of the hand. Orientability is a reading of the continuing
object at a station, not a fixed attribute
([notation](../../docs/HOLONIC_NOTATION.md#orientation-an-expression-is-unoriented-until-it-is-causally-framed);
Brandon, September 19). The subsections below give each part its exact form.

### 3.1 One involution has no direction; two in a chain have one

[proved-standard; checked by exact computation; formal-checked owners] The half-turn
`S_a x = 2a − x` is an involution (`Geometry/AffineSwing.theSwingIsAnInvolution`), and so is the
HNN's junction scattering (`junctionScattering_involutive`: `junction ∘ junction = id`). An
involution is its own reverse: read at its own grain, the act and its reversal are one act. Chaining
two orients them. `S_a S_b x = x + 2(a − b)`, and the reversed order is its inverse: for `a = 1/3`,
`b = 1/2` the two orders translate by `−1/3` and `+1/3`. For any word of involutions, reversal is
inversion, `(J₁ ⋯ J_n)⁻¹ = J_n ⋯ J₁`. So a receiver orients a chain exactly when it separates the
composite from its inverse. Two pumped reflections composing into a turn by their relative phase
(the parametron's row in CLAUDE.md) is the same fact.

[formal-checked owners] On a closed chain, orientability is a `ℤ/2` holonomy. A circuit of `k`
reflections has determinant `(−1)ᵏ` and reverses orientation exactly when `k` is odd (atlas
`tube.orientation-bit`; `Transport/JunctionLaw.reflection_circuit_determinant`,
`orientation_reversing_iff_odd`, `walkHolonomy_telescopes`; `Objects/Pairing.no_orientation_of_reversing_cycle`).
Non-orientable means a nontrivial holonomy of the hand in `H¹(·; ℤ/2)` (atlas
`holon.unoriented-junction`). Brandon's "non-orientable at that grain" has this exact form.

### 3.2 The arrow lives on cycles and on the chain's mean

[formal-checked owners] Entropy production along a passage is `σ(γ) = D(P_γ ‖ P_(Rγ)) ≥ 0`: the
distinguishability of the passage from its reversal. It adds over epochs for Markov dynamics and is
zero exactly at detailed balance (atlas `aeon.a6-irreversibility-kl`, `xent.passage-production`).
- A stationary nearest-neighbour chain is in detailed balance and has no arrow
  (`Physics/Thermal/ChainAxes.path_no_arrow`; atlas `heat.chain-no-arrow`).
- A stationary ring carries one current `J`, with production `J·A`, where `A` is the cycle's
  affinity. Reversing the orientation flips `J` and `A`, not the production (atlas
  `heat.ring-current-affinity`). The arrow lives on cycles.
- One step back across a junction can read negative. The arrow belongs to the path law's mean, not
  to a micro-step (`ChainAxes.backward_step_reads_negative`; atlas `heat.aeon-entropy-not-monotone`).
- Detailed balance is a self-adjoint navigator in `L²(π)`, with real spectrum. Production permits a
  complex spectrum (atlas `aeon.a9-placement-reversibility`).

### 3.3 The cross-section reads less of the arrow than the whole

[formal-checked owner] At any cut `A`, a chain's epoch production splits into the production across
the neck plus half the production inside each side, so `σ_cut(A) ≤ σ_epoch`, with equality exactly
when every junction inside either side is balanced (atlas `heat.cut-production`;
`Physics/Thermal/Schnakenberg.cutProduction_le_epochProduction`, `cutProduction_eq_epochProduction_iff`).
Brandon's cross-section of the channel is the cut. The whole body of water is the epoch.

[proved-standard; agent-inferred reading] **Which higher grain orients.** Relative entropy does not
increase when one map is applied to both path laws (data processing). A receiver whose readings are
a function of the cut's readings, a coarser partition of the same section, never orients what the
cut cannot. The grain that orients is a wider receiver: one joined to more of the passage, such as
both ends of the channel with its driving potential, or the closed cycle. In the objects that is the
tube's longitudinal span, not a coarser partition of one section.

### 3.4 The duplex is read the same from both ends

[definition; formal-checked owner] The helical code's pairing `σ̄(w) = σ(w)ᴿ` is an involutive
anti-automorphism, and each strand is the other's key. A single-strand defect's repair has two
members, since either strand may be the damaged one. Only a frame that marks the template strand
resolves them. Without one, the decoder returns a class only when every member decodes alike and
otherwise refuses (the guide's [helical code](../../docs/ELEMENTARY_OBJECTS.md#the-helical-code-how-holons-encode),
item 4; `Transport/HelicalCode`). The duplex is non-orientable at its own grain, a wider frame
orients it, and the decoder holds the two members instead of choosing one.

### 3.5 Simultaneity is a commutation claim

[agent-inferred; the lens's occasion] The release locks together the stations whose gap enclosures
its readings cannot order (Rust `hnn::prediction::bank_release` under `LockOrder::Gap`; Lean
`HNN/ExecutedComparison.certifiedLock`, `leader_locks`, `lone_lock_is_largest`,
`certified_order_needs_crossing`; the [lock rule's record](2026-10-02_A_FLIP_IS_SET_BY_THE_LOCK_RULES_MARGIN_AND_NO_LAW_IN_THE_CHAIN_CERTIFIES_IT_BEFORE_THE_SUCCESSOR_IS_READ.md),
§5). The lens says when that is lawful. Locking `j` and `k` together is one class with both orders
exactly when every admitted future face agrees on them:

```text
F_fut(T_j T_k x) = F_fut(T_k T_j x)   for every admitted x;   linear chart: F_fut [T_j, T_k] = 0
```

Otherwise the order is a two-member fibre, to be carried until the chain's continuation or a wider
receiver separates it, never collapsed into "simultaneous". This is the hardware law read in time:
co-present regions execute together when their effects commute (CLAUDE.md, hardware law). The lock
record's own observation that a pair locked together can split once a move certifies one above the
other is this fibre reopening.

### 3.6 Reciprocity is what an elimination leaves unoriented

[proved-standard; checked by exact computation] The Schur complement of a symmetric constitution is
symmetric, since `(B D⁻¹ Bᵀ)ᵀ = B D⁻¹ Bᵀ` when `D = Dᵀ`. After its interior is eliminated, a
reciprocal medium transfers alike between two ports in both directions, so its boundary cannot
orient a passage between them. In §2.1's example the reduced map is
`[[6/5, −6/5], [−6/5, 6/5]]`. Adding a unit antisymmetric coupling between port `0` and the junction
gives `[[7/5, −3/5], [−9/5, 6/5]]`, whose two transfers differ.

[agent-inferred; owner named] Orientation therefore enters only through nonreciprocal relations,
with their power terms: pumps, active relations and directed forces. The guide states the
condition: an asymmetric scalar potential can have a symmetric Hessian, and directed active forces
need their own relations and power terms ([the morphodynamic circuit](../../docs/ELEMENTARY_OBJECTS.md#the-morphodynamic-circuit)).

## 4. What the repository already owns

Every owner named in §§2–3 was opened for this record. The ones the joins consume:
- causal time parity (`definition:causal-time-parity`, a project definition without a Lean proof);
- elimination with memory (`resolvent.dynamic-schur`, `fluid.boundary-memory`);
- the pair composition (`norm.mass-current-associative`);
- junction scattering (`HNN/Propagation`);
- the orientation holonomy (`Transport/JunctionLaw`, `Objects/Pairing`);
- the production of chains, rings and cuts (`Physics/Thermal/ChainAxes`, `Physics/Thermal/Schnakenberg`);
- the duplex decoder (`Transport/HelicalCode`);
- the lock rule (`HNN/ExecutedComparison`, `hnn::prediction`).

Its diagnostic orders `LockOrder::Ascending` and `LockOrder::Descending` already execute the two
single-station orders that §3.5's certificate compares.

## 5. The joins owed

1. **The commutation certificate at the lock** (Lean and Rust; #62, #73). Its consumer is
   `bank_release`. A joint lock of `j` and `k` is admitted only when the two orders give equal
   admitted faces, `F_adm(T_j T_k x) = F_adm(T_k T_j x)`. Otherwise the release returns the
   two-member order fibre with its witnesses, as the decoder does with an unmarked duplex. The two
   orders are read with the existing diagnostic orders; no new routine is written. Lean:
   `certifiedLock` with this premise, and the statement that a commuting pair's joint lock is one
   retention class with both orders.
2. **The pair through every receiving junction** (#73). The receiving junction carries `(M, J)` and
   reads `y = J/M` only at its face; the consumer equation is `(M, J) ⊕ (a, av) = (M + a, J + av)`
   with `y′ − y = a(v − y)/(M + a)`. Where an executed path divides or rounds each weight before
   the merge, it is to be named and repaired at its owner.
3. **Elimination keeps its memory** (#62). Any reduction of field loci by their pivots states the
   dynamic Schur form with the interior's initial state and the exterior's return. A static
   reduction is admitted only where its memory term is proved zero.
4. **Lean statements owed** (#62):
   - the causal sweep `∂(Σ_k E_k) = Σ_n − Σ_m + Σ_k Γ_k` on an oriented occurrence complex, beside
     `Geometry/Telescoping`;
   - reversal of a word of involutions is its inverse;
   - orientation as a receiver reading, which separates the composite from its inverse;
   - the data-processing bound for `σ` under a map applied to both path laws;
   - the Schur complement of a symmetric constitution is symmetric, so a reciprocal interior leaves
     its boundary unoriented.

**Acceptance for the first loop** (fixed before any build). On the lock rule's existing known-truth
fixtures, for every joint lock the release takes, read the two single-station orders' successor
faces exactly. Report:
- how many joint locks commute on the admitted faces;
- for each that does not, its order fibre and the first admitted reading that separates the two
  orders.

No lock rule changes until this count is read.

**Recorded failures checked.**
- A located cause carried unrepaired into a new consumer: the lock rule's flip is a located cause
  (October 2), and join 1 repairs it at its owner instead of building beside it.
- A design thought in the programming language: the junction is stated as a pivot, a pair and a
  holonomy, not as arrays, offsets or windows.
- An authored routine standing in for learning: the certificate reads the release's own orders.
- Text run as the exception: junctions, chains and cuts are modality-free.
