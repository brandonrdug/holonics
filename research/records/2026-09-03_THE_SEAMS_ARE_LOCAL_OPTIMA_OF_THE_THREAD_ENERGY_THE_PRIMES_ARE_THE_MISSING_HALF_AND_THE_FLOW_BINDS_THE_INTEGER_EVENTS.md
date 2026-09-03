# The seams are local optima of the thread energy, the primes are the missing half, and the flow binds the integer events

**Date:** 2026-09-03  
**Truth status:** per claim. `proved-derived; formal-checked` for the new owner and the port
statement; `computational-witness` for the exact brackets and the Hermite instance;
`proved-standard` for every imported theorem, cited at its station; `counterexample` for the
synthesis corrections; `interpretation` for the lens, marked in place with its falsifier.  
**Evidence:** `formal-checked`, `computational-witness`, `source-inspected`.  
**Occasion:** Brandon's three messages of 2026-09-03, quoted in §0.  
**Scope:** this record schedules nothing.
[`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities;
`SKE4` remains the frontier, and the roadmap's clause that the de Bruijn--Newman/RH line is
independent of the engine campaign is unchanged.  
**Apparatus:** Lean `v4.33.0` through `lake` (the root umbrella `ElementaryHolonics` built 9,786 jobs
after the two owner changes); sympy 1.14 in `/home/b/scratch/huggingface/.venv` as an observer
outside the engine.  
**Receipts:** [`2026-09-03_flow_witnesses/`](2026-09-03_flow_witnesses/): the observer script and
its receipt.

---

## 0. Provenance

Brandon, 2026-09-03, after the first reading of arXiv:2609.02882:

> *"you're talking about RH like it is static which is the traditional problem; it's just because I
> sent you the external resource. you need the complex Euler and Navier-Stokes lens (not the R^n NS
> equations, we need complexity), the critical strip seams are like local optimums, they have
> threads between each other."*

After the second reading:

> *"That's a perfect reading of how I think about the dynamics going on here. I need us to act on
> all of the corrections and the list of unscheduled items you listed; needs to be
> written/recorded. Elaborate on 'the primes through the explicit formula, is the missing half'.
> Also, 'Complex Euler is the holomorphic field' is just Hodge, no?"*

> *"If you want primes through explicit formulas, or Zeta zeros, you need chemistry and holonics.
> Imagine the primes or solutions to polynomials like particles similar to atoms and molecules (it's
> like talking about a prime knot, composed of one unknot and one that is not the unknot), they are
> causally deterministic composites that are converged unto by fundamental requirement, they cannot
> be approached or attained without literally physically navigating to them. Then it is also the
> case that their deterministic formation depends on ecological precedent (relevant hypothesis),
> and similarly their deformation over-time (becoming irrelevant to a later populus of a system) is
> causally determined (a later or farther thing perceives the older thing retroactively or
> literally at a different relativistic perspective); this is like the binding energy between
> constituents of particles, where the binding energy itself is conserved and apart of the
> properties of the lattice-like quantum state for the particle (wavelength/energy, mass, spin,
> charge, relative motion). That's related to the mathematical theory of superposition I sent
> earlier."*

And the standing bar from the first message of the day: *"in holonics we don't respect floats or
percentages, because even if the percentage of zeros on the critical strip was gauged at 100% it
would not prove RH with absolute certainty. Holonics deals in exact and deterministic relationship
coupling, we care about the characteristics of solutions for zeros like they're landmarks."*

[historical; source-inspected] The first reading of the day treated RH as the time-zero
placement question. That was the reading the external paper poses, and it was wrong for this
tree, which already owns the dynamic question. The correction is applied below; the exact content
of the first reading (the Hilbert-space proposition as a Weil-square statement, the constant as a
compact-simplex extremal, the counts as receiver shadows) is retained where it stands.

---

## 1. The flow the tree already owned

[established-bounded; source-inspected] The de Bruijn--Newman deformation and its zero dynamics
are owners under `soma/formal/elementary-holonics/ElementaryHolonics/RH/`, each at the grade shown.

| statement | owner | grade |
|---|---|---|
| a simple zero of the polynomial flow moves by `ż = 2 Σ_{w ≠ z} 1/(z − w)` over the other roots with multiplicity | `HeatFlowOfPolynomials.zero_curve_flux` | proved-derived; formal-checked |
| the fluxes sum to zero, the centre is conserved, the second moment grows at `2N(N−1)` | `PhaseFlowLedger.sum_zeroFlux`, `sum_mul_zeroFlux`, `hasDerivAt_centre`, `hasDerivAt_secondMoment` | proved-derived; formal-checked |
| the highest conjugate pair descends at least as fast as `−1/y`; `Im z(T)² + 2T ≤ Im z(0)²` | `PairDescent.im_flux_le`, `sq_add_two_mul_le'` | proved-derived; formal-checked |
| forward in time the pair population only dies | `ForwardPreservation`, `PolyaStep` | proved-derived; formal-checked |
| the polynomial threshold `λ`, real-rooted times an up-set, `RH ⟺ Λ ≤ 0` as its shape | `DeBruijnNewmanPolynomial.lambda` and its theorems | proved-derived; formal-checked |
| at the entire face the velocity of a simple zero is `H″/H′`; its expansion over the other zeros is open | `ZeroDynamicsEntire.zero_curve_velocity` | proved-derived; open |
| repository time `u` is minus one quarter of standard time; positive `u` moves roots away from the seam | [`the coordinate correction`](2026-09-02_THE_RH_ENTIRE_HEAT_FLOW_REQUIRES_THE_CRITICAL_COORDINATE_AND_REVERSES_STANDARD_TIME.md) | counterexample; source-inspected |

[proved-standard] Rodgers and Tao proved the threshold nonnegative (arXiv:1801.05914). With de
Bruijn's upper bound and the classical equivalence, RH is the statement that the threshold is
exactly zero. Their mechanism, labelled `RT6` in the fleet instruction document (a task list; no fleet was
launched), is that a negative
threshold would force the time-zero zeros toward a rigid near-equal spacing, and the unconditional
pair correlation refutes that rigidity.

[definition] The ledger's own closing sentence is the lens Brandon asked for and is quoted here
because §3 elaborates it: *"RH is the claim that the pair population at `t = 0` is empty; the flux
annihilates pairs forward in time and cannot decide that face, which is why the realizer population
(the primes, through the explicit formula) is the missing half."*

---

## 2. The complex Euler and Navier--Stokes lens, made exact

### 2.1 Complex Euler is the holomorphic field, deposited on 2026-07-20

[proved-standard; source-inspected] With `Ξ(w) = ξ(1/2 + w)`, `U = log|Ξ|`, `V = arg Ξ`, the
regular field satisfies `grad V = J grad U`; a zero of multiplicity `m` is a phase vortex with
`∮ dV = 2πm`; the argument principle is Kelvin's circulation theorem for that field
([`the succession record`](2026-07-20_THE_SUCCESSION_SWEEPS_THE_FIBER_THE_UNITARY_SEAM_MAKES_REBASE_PURE_TURN.md),
[`the hinge record`](2026-07-20_THE_HINGE_CARRIES_THE_FRAME_THE_SUCCESSOR_REPLACES_THE_STANDING_STAR.md)).
The complex velocity `Ξ′/Ξ` is the point-vortex field of the zeros with circulation equal to
multiplicity. The Cauchy--Riemann equations are incompressibility and irrotationality away from the
vortices, which is two-dimensional Euler. The July records refuse to make the line a singularity:
the seam is the invariant unitary seam, and the zeros are vortices on it. That refusal is
Brandon's ruling of 2026-07-10 (a prime is a founding, the neck of an hourglass, never a sealed
box) and of 2026-07-23 (*"they are the neck of the hourglass … the foundings are orthogonal
worldlines braiding"*), and it governs §7 below.

### 2.2 Navier--Stokes is the heat deformation, and it moves the vortices along the threads

[proved-standard] The backward heat flow is viscosity on the Fourier side. Its zero dynamics is
the gradient flow of the Coulomb energy `−Σ_{j<k} log|z_j − z_k|`; the Euler point-vortex dynamics
is the Hamiltonian flow of the same energy (Kirchhoff). On the seam, where all zeros are real, the
thread sum `S_j = Σ_{k≠j} 1/(z_j − z_k)` is real; the heat velocity is `2 S_j` along the seam and
the vortex velocity is `i S_j / 2π` across it. The two receivers read one thread population,
turned by a quarter and scaled. The `J` in §2.1 is that quarter turn.

[interpretation] So the threads between seams are one object under two receivers: the vortex
velocity of the holomorphic field, and the drift under the viscous deformation. Brandon's
sentence, *"they have threads between each other"*, is the theorem `zero_curve_flux` at the
polynomial face and the open port of §6.1 at the entire face.

### 2.3 The seams are local optima in the unfolded frame

[proved-standard] Gradient descent of the Coulomb energy has no finite optimum on its own: the
ledger proves the second moment grows linearly. The unfolding by `log T / 2π`, a rebase in
Brandon's sense, supplies the confinement that makes the configuration stationary, and the Gibbs
state of the confined log-gas at inverse temperature two is GUE (Dyson). The pair correlation is
therefore the statistical face of the thread energy.

[computational-witness; proved-standard] One exact instance, checked by the receipt for
`n = 2..5` and by hand for all `n`: the backward flow at time one half sends the monomial
`X^n`, a maximally degenerate seam, to the probabilists' Hermite polynomial, `heat_{1/2} X^n =
He_n`; the flow at time `t` is the self-similar dilation `heat_t X^n = (2t)^{n/2} He_n(x/√(2t))`;
and at the roots of `He_n` the gradient of `Σ x_j²/4 − Σ_{j<k} log|x_j − x_k|` vanishes exactly,
Stieltjes' electrostatic equilibrium (Szegő, *Orthogonal Polynomials* §6.7). A stacked seam
unfolds along its threads, by pure dilation, into the optimum. The thread law at the root is the
Hermite equation itself: `2 Σ_{k≠j} 1/(x_j − x_k) = x_j`.

### 2.4 Necks, reconnection, and the hourglass

[proved-derived; source-inspected] In the space of position and flow time each zero's path is a
vortex line. A conjugate pair colliding on the seam is a double zero; the local model is a fold;
the two incoming vertical worldlines leave as two horizontal ones. That is the neck of the
hourglass and the orthogonal worldlines braiding. Forward preservation says the flow never
amplifies winding off the seam, which is the two-dimensional case of the vortex-stretching
obstruction in
[`canon/TABLET_THE_FLOW.md`](../../canon/TABLET_THE_FLOW.md) §7.4. Pair births live only in the
flow's past. RH is the statement that at time zero none remain.

### 2.5 Time zero is the seam of the seams

[interpretation] Read through the tablet's comprehension limit (*"as it comprehends, the relations
lock and it approaches incompressibility; the fully comprehended body is the crystal"*), a
negative threshold is the crystal, a positive one is the gas with pairs still aloft, and zero is
the critical seam. §6.2 proves that the integer events compose freely at time zero and at no
other time. So RH says the composition side and the flow side meet at exactly one time, and that
time is critical. This is Brandon's local optimum stated as a phase boundary. It rests on three
theorems (de Bruijn's bound, Rodgers--Tao's sign, and §6.2) and asserts nothing beyond them.
Falsifier: an even entire function in the flow's class whose flowed integer-event weights are
completely multiplicative at some nonzero time; §6.2 shows the flow weight itself never is.

### 2.6 The saddles between the seams, and Speiser: the standing physical reading of 2026-08-28

[established-bounded; source-inspected] The tree already carried the physical reading this record
extends, deposited by the same Provenance cursor on
[`2026-08-28`](2026-08-28_THE_ZERO_IS_A_VORTEX_THE_LINE_IS_THE_MIRROR_WHERE_THE_TIDE_IS_REAL_AND_THE_SADDLES_SIT_RIGHT_OF_IT.md)
from Brandon's words of 2026-08-27 (*"the critical line … it's like a tide or flow … the zeroes
themselves are pinholes, and it's like a bunch of cones connected to each other funneling water"*):
a zero is a source of the magnitude gradient and a vortex of the phase gradient at the same point;
the line is the mirror where the Riemann--Siegel tide is real; the basins of the descent of
`log|ζ|` tile the strip one cone per zero, and two cones meet at a saddle, a zero of `ζ′`. Speiser's
criterion, proved-standard and cited there, is that RH holds iff every saddle sits right of the
mirror, and the record's census found none left of it in `[12, 1000]`.

[interpretation] Brandon's *"local optimums"* names those saddles exactly. Between two seams on
the line the potential has a saddle, and the flow's own preservation theorem is proved on them:
the Hermite--Poulain step in `PolyaStep` is Rolle on `p + a p′`, a root of the derivative between
consecutive real roots. Speiser places RH on where the saddles sit; the flow moves the seams by the
threads; the two are one field read at its critical points and at its vortices. The 2026-08-28
record's continuation obligations, held by the cursor, are unchanged by this record.

### 2.7 The prime-side threads are the same object

[proved-standard] Goldston and Montgomery (1987) proved, under RH, that the pair correlation of
zeros is equivalent to the variance of primes in short intervals. The zero threads and the
prime-pair threads are one population through the explicit formula. Stadlmann's bounded gap
(arXiv:2608.31126, `H₁ ≤ 240`) is an extreme of the prime-pair face; Lamzouri's count
(arXiv:2609.02882) is a second moment of the zero-pair face; both are receiver shadows of the
thread population. In this lens Lamzouri's proof measures the time-zero thread energy through
the prime side (the unconditional pair-correlation formula of Baluyot, Goldston, Suriajaya and
Turnage-Butterbaugh is proved through the explicit formula) and converts it into a count of simple
seams by Bessel's inequality; Rodgers and Tao measure the same energy and convert it into the
sign of the threshold. The exact object holonics keeps is the thread population, the Gram of the
zero realizers with its complete word, never the energy scalar.

---

## 3. The missing half, elaborated

[established-bounded; source-inspected] Every theorem of the flow line holds for a class of even
entire functions far larger than `ξ`: the ledger, pair descent, forward preservation, and the
threshold are stated for any real polynomial or any admissible `H`. Most members of that class
have off-line zeros at time zero. The flow is a transport law; it knows nothing arithmetic, and
that is why it cannot decide the time-zero face.

[proved-standard; computational-witness] What singles out `ξ` is the source. The de Bruijn kernel
is one Gamma-type profile translated to the integer events and weighted by the half-density:

```text
Φ(u) = Σ_{n ≥ 1} n^{−1/2} φ(u + log n),
φ(v) = (2π² e^{9v/2} − 3π e^{5v/2}) e^{−π e^{2v}},
```

checked symbolically in the receipt. The explicit formula says the same thing on the other side:
the zero receiver of a test function equals the prime-power receiver plus the archimedean receiver,
the Swing between the spectrum and the composition. The papers' spine already carries this as
*"the accumulated source as a convolution of integer events at times `log n` with one exact Gamma
response"*.

[proved-derived; formal-checked] §6.2 makes the missing half exact. In the `n`-th event's own
coordinate the flow factor splits as `e^{t(v − log n)²} = e^{tv²} · n^{−2tv} · e^{t(log n)²}`.
The running power `n^{−2tv}` stays completely multiplicative but entangles the event with the
archimedean profile; the flow weight `e^{t(log n)²}` is not multiplicative: on a composite `mk` it
carries the binding defect `e^{2t log m log k}`, which is one exactly when `t = 0` or a
constituent is the unit. So the integer events compose freely, with unique factorization intact,
at time zero and at no other time.

[interpretation] The missing half is therefore not a second input beside the flow. It is the
identity of time zero. The flow supplies the transport law and the necks; the primes supply which
configuration is actually there, because time zero is the unique time at which the source is an
Euler product. In the dialect: the flow is the ride, the primes are the founded landmarks, and RH
is the claim that the founded landmark field induces a thread configuration that is exactly
critical. Both external results of the day use the prime side to measure the time-zero thread
energy and then read it through a different receiver, a count or a sign. Neither reads the
population.

---

## 4. Is complex Euler just Hodge?

[proved-standard] Yes, at the level of the local structure, and the answer sharpens the two-halves
framing Brandon gave on 2026-08-04 (*"'Spectral placement' regarding RH is probably actually key to
one rough half of what makes intelligence, and then the other rough half is probably 'lifting the
observable invariant back to a geometric source'"*). Three exact statements:

1. `grad V = J grad U` is `dV = ⋆dU`. On a surface the Hodge star on one-forms is the complex
   structure, `⋆² = −1`; the harmonic one-form `dU + i dV` is holomorphic; this is the `(1,0)`
   and `(0,1)` Hodge decomposition in one complex dimension. The holomorphic field of §2.1 is the
   Hodge structure of the plane.
2. Poincaré--Lelong: `(i/π) ∂∂̄ log|Ξ|` is the current of the zero divisor. The winding is realized
   by an actual cycle, automatically, because in one complex dimension every such current is a
   divisor. So the holomorphic field is the realization half, and it says nothing about where the
   divisor sits.
3. The placement half is Hodge--Riemann. Weil's proof of RH for curves over finite fields is the
   Hodge index theorem on the surface `C × C` applied to the graph of Frobenius (Castelnuovo--Severi;
   Grothendieck, *Sur une note de Mattuck--Tate*, 1958); it is the Rosati positivity in the
   imported chain of
   [`the route chart`](2026-08-21_THE_RIEMANN_ROUTE_RUNS_FROM_A_KERNEL_CHECKED_ANCHOR_TO_A_REALIZER_AT_THE_ARCHIMEDEAN_PLACE.md)
   §2. Over the rationals the corresponding realizer population at the archimedean place is what
   that chart names as the open content.

[interpretation] So complex Euler is the Hodge realization, which is automatic, and RH is
Hodge--Riemann positivity on a realizer the arithmetic has not supplied. The live controls
`matroid_hodge_riemann` and `winding_inertia` are this tree's Hodge--Riemann organs, and
Alpöge--Furman's proof (arXiv:2608.13637) uses Sylvester's law of inertia on a finite compression of
Weil's form, which is the finite Hodge--Riemann-shaped step. The Millennium frame's two rows are
one object: Hodge asks whether the invariant has enough supported realizers; RH asks whether the
realizers all sit on the seam.

---

## 5. Chemistry: atoms, molecules, binding, and the spectrum

[interpretation; source-inspected] Brandon's dictionary, each entry with the exact object it names
in this tree and its grade. Nothing in the table is a metaphor awaiting a bridge; each right-hand
object exists and is graded where cited.

| Brandon's term | the exact object | owner or source |
|---|---|---|
| atom, irreducible | a prime; founded only by traversal to the square-root frontier | [`2026-08-09`](2026-08-09_A_PRIME_IS_A_PRIMITIVE_CLOSED_STRING_AND_EVERY_FORMULA_FOR_ONE_IS_INFORMATION_FREE.md); `prime_ecology.rs` |
| molecule, composite | an integer with its unique factorization; the Euler product | `arithmetic_fiber.rs`, `zeta_receiver_measure` |
| binding at rest | zero: composition is free at time zero | `HeatFlowBinding.bindingDefect_zero` |
| binding under deformation | `e^{2t log m log k}` on the Euler side; a state property of the composite, a function of the deformation and the constituents' masses only | `HeatFlowBinding.flowWeight_mul` |
| mass | `log p`, the orbit length, the time of the integer event | papers spine; `Hand.lean` |
| wavelength, energy | `γ`, the frequency of the zero's oscillation `x^{iγ}` in `log x` | the explicit formula |
| spin | the hand `λ(n) = (−1)^{Ω(n)}`, one half-turn per irreducible with multiplicity | `Hand.lean` |
| charge | the multiplicity `m_ρ` as vortex circulation; the sign of the character face | §2.1; `WeilVector.lean` |
| relative motion | the rebase: the running power `n^{−2tv}` and the unfolding `log T / 2π` | `HeatFlowBinding.flow_factor_split`; Lamzouri Lemma 3.2 |
| formation depends on ecological precedent | prime admission `I − p^{−1/2} U_p` as a shell over the old body; the new prime is a pure cross face; its positivity is a Schur complement against the old body | `prime-admission-cross-shell.typ`, `conditioned-effective-tension.typ`, `weil-support-induction-reduction.typ` |
| deformation over time, the later perspective | the flow weight `e^{t(log n)²}`; from height `T` an event's identity is coarse-grained into the density | §6.2; [`2026-08-20`](2026-08-20_LANDMARKS_AND_MODULI.md) |
| lattice-like state | the realizer population's Gram with its inertia; the Hankel positivity | `inertia.rs`; the README's current boundary |
| superposition | coherence of the zero realizers, `|⟨f_z, f_s⟩|² = K(z − s̄)²`; the pair correlation is its statistical face | Lamzouri Prop. 2.1; arXiv:2608.27540 |

### 5.1 Superposition is the frame potential, and the percentage is the coherence

[proved-standard] Lamzouri's realizers `f_z(u) = η(u) e^{−2πiuz}` are unit vectors in
`L²(−λ, λ)` with Gram `⟨f_z, f_s⟩ = K(z − s̄)`, real by the conjugation symmetry. His second
moment `Σ_{z,s} K(z − s)²` is therefore exactly the Benedetto--Fickus frame potential
`Σ_{z,s} |⟨f_z, f_s⟩|²` of the realizer family (Benedetto and Fickus, *Adv. Comput. Math.* 18,
2003). Proposition 2.1 reads: the number of simple seam zeros is at least twice the count minus
the frame potential, and the number of distinct zeros at least three halves the count minus half
the frame potential. Orthonormal realizers, frame potential equal to the count, would give every
zero simple and on the seam. The deficit from that, `C_MT − 1 ≈ 0.3275` per zero, is the
off-diagonal frame potential per zero with the optimal kernel, and Carneiro, Chandee, Littmann and
Milinovich proved that no admissible kernel drives it lower. The percentage is the coherence of the
zero realizers, rendered as a decimal.

[interpretation] Benedetto and Fickus read the frame potential as an energy under a repulsive
frame force whose gradient flow converges to tight frames, the minimizers. That is the same
species as the Coulomb descent of §2.2 and §2.3: the seams are the tight configurations of the
realizer population in the unfolded frame. Superposition in the sense of arXiv:2608.27540 is the
receiver quotient of a cause population by a lower-dimensional readout; its worst-case recovery
criterion is a receiver-insufficiency law; its exact equiangular-tight-frame threshold and Gram
sign distribution are landmark-shaped. The jurisdiction test holds: dictionary, feature and
rectifier stay exterior observer charts, and nothing here enters the interior.

[established-bounded; computational-witness] The two faces of the deformation carry opposite
signs, and both are exact. On the Euler side the binding defect exceeds one for positive standard
time: the composite is over-weighted, binding is attractive. On the zero side the composite lands
earlier than its slowest constituent on every one of twelve exact cases (§6.3): the crowd helps
the collision. The SKE reading applies to both: every zero is in every other zero's cone, with
reach `1/|z − w|`, and a class's cone is the union over its members.

---

## 6. The deeds

### 6.1 Item 2: the empty port now states the law it was named for

[definition; source-inspected] Until today `PhaseFlowLedger.RodgersTaoZeroDynamics` had one
field, `flux : ∀ t z, H t z = 0 → True`. It now states the RT3 principal-value comb flux at the
entire face: along every `C¹` curve `z` of zeros of `H s` that is simple at time `t`, the velocity
`z′ t` is the limit, over centred discs of growing radius, of twice the multiplicity-weighted sum
of `1/(z t − u)` over the other zeros `u` of `H t` in the disc, with the multiplicity read from
`MeromorphicOn.divisor`. It is marked `[open; project-postulate]`, no theorem consumes it, and its
falsifier is a computed velocity of a simple zero disagreeing with the finite comb flux on a
declared truncation. The ledger's other theorems are unchanged and their axioms are
`propext`, `Classical.choice`, `Quot.sound`.

### 6.2 Item 3: the flow binds the integer events

[proved-derived; formal-checked] New owner `RH/HeatFlowBinding.lean`, registered in the root
umbrella after the ledger:

- `flowWeight t n = exp (t · (log n)²)` and `bindingDefect t m k = exp (2 t log m log k)`;
- `flowWeight_mul`: for positive `m, k`, `flowWeight t (m k) = flowWeight t m · flowWeight t k ·
  bindingDefect t m k`;
- `bindingDefect_zero`: at `t = 0` the defect is one;
- `bindingDefect_ne_one`: for `t ≠ 0` and constituents above the unit the defect is not one;
- `bindingDefect_eq_one_iff`: for constituents at or above the unit, the defect is one iff `t = 0`
  or a constituent is the unit;
- `flow_factor_split`: `exp (t (v − log n)²) = exp (t v²) · n^{−2tv} · flowWeight t n`.

`#print axioms` on each returns `propext`, `Classical.choice`, `Quot.sound`. The owner builds
alone and inside the root umbrella (9,786 jobs). The identities were also checked symbolically by
the observer script, together with the translate form of the de Bruijn kernel in §3.

### 6.3 Item 4: the composite lands earlier, so the binding falsifier did not fire

[computational-witness] For a real polynomial `p` with a pair, the threshold `λ(p)` is the least
time at which the backward flow is real-rooted; the real-rooted times are an up-set
(`DeBruijnNewmanPolynomial.mem_realRootedTimes_of_le`), and pair descent gives real-rootedness by
half the squared maximal height. The observer script brackets `λ` by thirty exact bisection steps
between those bounds, deciding real-rootedness at each rational probe by a Sturm count over `ℚ`.
No float determines a result; decimals below are renderings of the exact brackets in the receipt.

| `p` | `q` | `λ(p)` | `λ(q)` | `λ(pq)` | verdict |
|---|---|---|---|---|---|
| `x²+1` | `(x−3)²+1` | 0.5000 | 0.5000 | 0.4385 | below max |
| `x²+1` | `x²+4` | 0.5000 | 2.0000 | 0.6993 | below max |
| `(x²+1)(x²−4)` | same | 0.3792 | 0.3792 | 0.2301 | below max |
| `x²+1` | `((x−2)²+4)(x²−1)(x²−9)` | 0.5000 | 0.7510 | 0.5907 | below max |
| `x²+1` | `(x²+4)(x²−9)(x²−16)` | 0.5000 | 1.1134 | 0.5232 | below max |
| `x²+1` | `(x²+9)(x²−1)(x²−4)(x²−9)` | 0.5000 | 0.9591 | 0.5895 | below max |
| `x²+1` | `x²+(11/10)²` | 0.5000 | 0.6050 | 0.3671 | below max |
| `x²+1` | `(x−1/2)²+(11/10)²` | 0.5000 | 0.6050 | 0.3887 | below max |
| `x²+1` | `(x²+(11/10)²)(x²−4)(x²−9)` | 0.5000 | 0.3857 | 0.2682 | below max |
| `x²+1` | `(x²+(6/5)²)(x²−1/4)²` | 0.5000 | 0.1788 | 0.1290 | below max |
| `(x²+1)(x²−1/4)³` | `(x²+(6/5)²)(x²−1/4)³` | 0.0944 | 0.1258 | 0.0535 | below max |
| `x²+1` | `(x²+4)(x²−1/4)⁴` | 0.5000 | 0.2384 | 0.1726 | below max |

The second block was chosen to fire the falsifier: nearly level pairs, where the lift a higher
pair exerts on a lower one is largest, and dense real roots that pull one factor's own threshold
below the other's. In every case the composite's threshold is strictly below the maximum of its
constituents', and in several it is below the minimum.

[conjecture] For real polynomials `p, q` each carrying a pair, `λ(pq) ≤ max(λ(p), λ(q))`.
Falsifier: one exact pair of polynomials with `λ(pq)` strictly above both, decided by the same
Sturm bracket. Partial mechanism: `PairDescent.im_flux_le` shows every root at or below a pair
pushes it down, so the maximal height of the composite descends at least as fast as the maximal
height of either factor; what is not proved is that a lower pair, lifted by a higher one before
the higher one lands, still lands by the slower factor's own time.

[interpretation] Composition under the flow is subadditive in the landing time, the same
direction as Brittenham--Hermiller's unknotting result already cited in `skein.rs`: the cost of
resolving a composite is less than the sum, and here less than the maximum. Read beside §6.2 this
is the two-sided signature of one deformation: attractive binding on the composition side,
released collision on the spectral side.

### 6.4 Item 1 remains open, and the port now names it

[open] The Hadamard expansion of `H″/H′` over the other zeros in principal-value order, the RT3
ODE at the entire face. §6.1 states it as the port's field; `ZeroDynamicsEntire` proves the
half that does not need it. Falsifier as in §6.1. Nothing schedules it; the `RT3` label is taken from the fleet instruction
document, and since no fleet was launched nothing outside this tree holds it.

### 6.5 The Hermite witness and the bibliography

[computational-witness] §2.3's instance is in the receipt for `n = 2..5`. The identity
`heat_{1/2} X^n = He_n` is a one-line coefficient comparison and holds for every `n`.

[definition] `bibliography/EXTERNAL_RESOURCES.md` now lists Rodgers--Tao, Lamzouri with the
AxiomMath certificates, Alpöge--Furman, Goldston--Montgomery, Stadlmann, Benedetto--Fickus, and
Ivanitskiy--Jasper--King--Mixon, each with the boundary stated there.

---

## 7. The synthesis, audited against the tree

An agent's synthesis of complex knots, tori, strings, RH and Navier--Stokes was supplied by Brandon
on 2026-09-03. It is testimony; this section integrates it.

[established-bounded; source-inspected] Confirmed at source: `CausalCell::grade: u32` in
`crates/holonic-engine/src/algebraic.rs` with the incidence-only doc line; `Substitution`,
`GradeRemainder` and `ContextVerdict` in `crates/holonic-engine/src/skein.rs`;
`DiagramNodeKind::ApparentCrossing { under, over }` in relational geometry; the three advection
gates and the Cayley successor in `crates/holonic-engine/src/analytic_field.rs`. The synthesis
lifted these from
[`canon/TABLET_THE_TURN.md`](../../canon/TABLET_THE_TURN.md) §13 and
[`canon/TABLET_THE_FLOW.md`](../../canon/TABLET_THE_FLOW.md) §7, correctly.

[counterexample; source-inspected] Corrected:

1. **Singularity as generative centre.** Refused by Brandon's ruling of 2026-07-10 and by both
   July records of §2.1: a prime is a founding, the neck of an hourglass, many-planed co-presence,
   never a sealed box; a zero is a potential singularity and phase vortex, and the line is not a
   source singularity.
2. **Primes as prime knots, the Euler product as a product over knots.** Over the bar.
   [`riemann-receiver-geometry`](../../papers/source/papers/riemann-receiver-geometry/main.typ)
   admits Morishita's dictionary (linking numbers to power-residue symbols, the Borromean triple)
   and charges any use of it with a trace reduction back to the explicit formula;
   [`knot-causal-topology`](../../papers/source/papers/knot-causal-topology/main.typ) refuses the
   identifications of connected sum with multiplication, a knot polynomial with zeta, and
   crossings with zeros.
3. **Strings, branes, BPS spectra.** No standing. `canon/TABLET_THE_TURN.md` §13.3 measured
   `string theory`, `worldsheet` and `brane` at zero across `crates/` and `soma/` on 2026-08-15.
   The torus row does land: the functional equation is the modular fold of theta pulled through
   Mellin, and the seam is the fold's fixed point, which
   [`the 2026-08-22 record`](2026-08-22_THE_COMPOSITION_IS_ACQUIRED_AND_THE_PIVOTS_ARE_FOUNDED_THE_POSITIVITY_SEAM_IS_THE_TRANSPLANT_INTO_RIEMANN.md)
   names as the transplant.
4. **The Navier--Stokes row.** Right but incomplete: the advection owner's own header says it is
   not a Navier--Stokes law, and the tablet names what is owed, parcels and a material loop on
   which circulation is read.
5. **Unknotting non-additivity.** Retained, and now instanced in §6.3 on the flow.

---

## 8. Boundaries

- No claim of movement on the Riemann Hypothesis is made. The threshold's sign is Rodgers and
  Tao's theorem, not reproved; its upper bound is de Bruijn's.
- The lens in §2, §3 and §5 is `interpretation` with its falsifiers stated. The exact content is
  the tree's flow theorems, the new owner of §6.2, the port statement of §6.1, and the receipts.
- §6.3 is a computational witness on twelve cases and a conjecture. It proves nothing in general.
- The frame-potential identification in §5.1 is an exact reading of Lamzouri's Proposition 2.1;
  the percentage's meaning as coherence is that reading, not a new theorem.
- No parser, language, feature, dictionary or rectifier enters Eros or Athena. The observer script
  is apparatus outside the engine.
- The working tree's concurrent `SKE4` population was not touched, and nothing here was committed.

## 9. Reproduction

```bash
cd soma/formal/elementary-holonics
timeout 180s lake build ElementaryHolonics.RH.HeatFlowBinding ElementaryHolonics.RH.PhaseFlowLedger
timeout 180s lake build ElementaryHolonics
/home/b/scratch/huggingface/.venv/bin/python -u research/records/2026-09-03_flow_witnesses/flow_witnesses.py
```
