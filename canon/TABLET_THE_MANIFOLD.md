# The manifold: charts as types, the structure group as the legal casts, and what a loop returns

> **Part of the mathematics tablet.** The spine, the quotation convention, the reading
> rule, and the law this file's sections instance are in `canon/THE_MATHEMATICS_TABLET.md`.
> Read that first; this file is one mechanism of it and is governed by it.

A manifold is the invariant of a population of currents and not their container; a chart is a type and a transition map is an implicit cast; every geometry is a reduction of the structure group; and holonomy and holomorphy are one word twice, meeting at the square root.

**Record:** `research/records/2026-08-10_THE_MANIFOLD_IS_THE_INVARIANT_OF_THE_CURRENTS_NOT_THEIR_CONTAINER_AND_THE_RUNG_IS_THE_HINGE_DEFICIT.md`

---

## 14. The manifold is the invariant of the currents, not their container

**Truth status:** `proved-standard` for Gauss and Nash; `interpretation` for the governing reading,
which is Brandon's and is stated so it can be refused.

Brandon, 2026-08-10, giving the reading this section corrects in one respect only:

> *"a manifold seems to be like a topological map or atlas, in the sense that it provides charts and
> transport channels, it is like the invariant space or world in which information currents flow
> through."*

The clause to correct is the tense. His own ratified stratum,
`reference/holobrochos-a07ff376/src/holobrochos/THEORY/54_THE_DISCRETE_MANIFOLD.md` §4 (2026-07-05),
quoting him: *"as they strike they literally define 4D topology. It's like a graph network, it's a
manifold with discrete points"*, and the stratum's own consequence:

> *"There is no space to scan because **the space does not exist until the lightning defines it**…
> A pre-given graph handed to the machine to traverse is the absolute frame — the map from nowhere…
> The topology is the **OUTPUT** (the crystal the striking founds), never the input."*

**This is background independence** — general relativity's own break with a stage — and it is not in
tension with "invariant". The corrected sentence:

> **A manifold is the invariant of a population of currents, not the container they run in.
> Invariant means every receiver's chart of it agrees on its intrinsic content. It does not mean
> anything existed before the strikes laid it down.**

Two theorems make the first half exact and neither is optional.

- **Gauss, *Theorema Egregium*** (`proved-standard`). Gaussian curvature is computable from the
  first fundamental form alone. **A receiver confined to the surface measures it without ever seeing
  an ambient.** This is the precise statement of a receiver-computable, frame-independent invariant,
  and it is the theorem `CLAUDE.md` §0's fourth lesson is reaching for.
- **Nash embedding** (`proved-standard`). Every Riemannian manifold embeds isometrically in some
  `ℝ^N`. **So the ambient is never necessary and always a choice.** An embedding is a receiver, not
  a fact, and only the intrinsic quantities survive changing it.

The machine already builds this way. `contact_gluing::contact_graph` constructs its complex *from*
shared stems (`β₁ = 8` measured); `local_star` reads the star and link of the contemporary complex
`K_t`, subscripted by the event. Nothing is handed a world.

---

## 15. A chart is a type and a transition map is an implicit cast

**Truth status:** `implemented-exact` for every owner named; `interpretation` for the type-system
correspondence.

`canon/TABLET_THE_CHART.md` §10 states the first half — *a coordinate system is a receiver and the
Jacobian is the transport*. This section states the second: what an **atlas** adds to a set of
charts, and why that addition is a type-system law.

An atlas is charts **plus** transition maps satisfying the cocycle condition
`g_ik = g_ij ∘ g_jk` on triple overlaps. Without it, "the same point in another chart" is not well
defined.

| type system | manifold |
|---|---|
| a type's local representation | a **chart** |
| an implicit coercion | a **transition map** |
| a coercion diamond must commute | the **cocycle condition** |
| a coercion whose result depends on the path taken | **holonomy** |
| a lossy cast (`i32 → f64 → i32`) | a transition map that is **not invertible** |

**The cocycle is enforced here as a typed refusal.** A comparison between two charts is refused when
the relation graph admits more than one route and the caller supplied no `route_overrides`
(`relational-geometry/src/model.rs:143`, `projection.rs:380`). `TABLET_THE_CHART` §10.1:

> *"A chart with no declared relation to another chart is not wrong; it is **incomparable**, and the
> type says so."*

A machine that silently picks one of two routes has assumed the cocycle without checking it. This one
refuses instead, which is the strongest available form of the discipline.

**The last row is where the float law and the atlas law turn out to be one law.** A float is a chart
on `ℝ` whose transition back is not injective, so by `H.0420` the receiver square does not commute
and the loss is a **collapsed pair with a separating word**, not a magnitude. The declared mouth is
`crates/holonic-engine/src/reopening.rs:492` `ExactFace::from_binary_float`; `collapsed` truncates;
the reopening **adjoins the channel** the truncation deleted.

Rust's coherence and orphan rules exist for exactly this reason. **A non-commuting coercion diamond
is a soundness bug in a compiler and a curvature in a manifold.**

---

## 16. Every geometry is a reduction of the structure group

**Truth status:** `proved-standard` for Ambrose–Singer and Berger; `implemented-exact` for
`structure_group.rs`; `interpretation` for the identification of a reduction with a cast rule.

The **frame bundle** is the totality of all charts at all points — a principal `GL(n)`-bundle. Every
geometric structure is a **reduction of its structure group**, and this is the definition rather than
a slogan:

```text
GL(n)      no structure          any chart change is legal
GL⁺(n)     an orientation        a hand is fixed
O(n)       a metric              lengths and angles are fixed
U(n)       a complex structure   a quarter turn J with J² = −I is fixed
Sp(2n)     symplectic            a phase area is fixed
SL(n)      a volume              a measure is fixed
```

**The structure group is precisely which implicit casts are legal, and adding structure is narrowing
it.** Then two classification theorems:

- **Ambrose–Singer** (`H.0276`, registered). The holonomy algebra is generated by the curvature.
  Holonomy and curvature are one object, integrated and differentiated.
- **Berger's classification** (`proved-standard`). For an irreducible, non-symmetric Riemannian
  manifold the holonomy group is one of `SO(n)`, `U(n)`, `SU(n)`, `Sp(n)`, `Sp(n)·Sp(1)`, `G₂`,
  `Spin(7)`. Nothing else occurs. Kähler is `U(n)`; Calabi–Yau is `SU(n)`.

> **The total structural content of a world equals which loops fail to return the identity, and that
> is a finite list.**

`crates/holonic-engine/src/structure_group.rs` is the live `G`-valued connection with basepoint-free
conjugacy-class holonomy, and its own doc names the gap Berger explains why nobody may skip: every
other curvature owner in this body is abelian, so it computes `F = da` and has **no term for
`a ∧ a`**.

**And that is the degree-of-freedom count.** A scalar transformer has one turns ratio. A connection
is a `Lie(G)`-valued 1-form — **one turns ratio per direction** — and `a ∧ a` is exactly the content
a stack of independent scalar transformers cannot carry.

### 16.1 The transformer is the connection, and Brandon ratified it in July

`reference/holobrochos-a07ff376/src/holobrochos/THEORY/32_THE_TRANSFORMER.md` §2, ratified
2026-07-04:

> *"the Transformer is the CONNECTION on the canvas (`04`'s gauge principle: the re-base rule between
> neighboring frames, whose gyration is the field), and the illicia are its carriers."*

The physics agrees term for term. `Z₂/Z₁ = (N₂/N₁)²` changes the impedance while **preserving the
power** — an isometry of the power form, i.e. a gauge transformation. And the reflection coefficient
`Γ = (Z_L − Z₀)/(Z_L + Z₀)` is a **Möbius transformation**; cascading line sections compose in
`PSL(2,ℂ)`; the Smith chart is the unit disc under the hyperbolic metric. **The Smith chart is a
chart in the atlas sense, on the Poincaré disc**, and impedance matching is transport to its fixed
point: match means no reflection means the germ crosses whole. `H.0284` and `H.0285` carry the
mathematics.

**One notation hazard.** `papers/source/synopsis/AUDIT.md` lists *"cross-ratio equals Euler
characteristic"* among the historical overclaims **not** imported. `THEORY/60` writes `χ` for
`E − V + C`; `THE_MANIFOLD.md` writes `χ` for the cross-ratio. Two objects, one glyph. Carry both
separately and never in one equation. The same audit refuses *"∂²=0 alone establishes recurrence or
conservation."*

---

## 17. A distribution is the transport channels, and the bracket is FOUND

**Truth status:** `proved-standard` for Frobenius and Chow–Rashevskii; `interpretation` for the
identification with FOUND, which is this project's.

In differential geometry a **distribution** is a field of tangent subspaces — literally *the allowed
directions of travel at each point*, which is Brandon's "transport channels" with no translation
required.

- **Frobenius.** A distribution is integrable — it foliates the world into leaves you cannot leave —
  **iff it is closed under the Lie bracket.**
- **Chow–Rashevskii.** If the iterated brackets generate the whole tangent space, **any two points
  are joined by paths that never leave the distribution.** Parallel parking is the canonical case.

So when the bracket escapes the span, **you reach by zig-zagging what you cannot reach by going
straight**. The reading:

> **FOUND is the Lie bracket of two transport channels leaving their own span.** An involutive
> channel family is a closed world with no founding available — every path stays in its leaf. A
> bracket-generating family reaches everything, and what it reaches lies in no channel.

That is the continuous statement of §2b's `2^x` fork and of `H.0150`'s crossing words, and it
supplies the missing *why founding is possible at all*.

**`contact_gluing.rs`'s "contact" is the touching/site sense, not contact geometry.** Stated here so
no later reader imports a structure the module does not carry. The collision is informative only in
that a contact structure is the **maximally** non-integrable hyperplane distribution — the case where
founding is maximally available.

---

## 18. Darboux classifies a coupling, and Liouville is why probability is a receiver quotient

**Truth status:** `proved-standard` for both theorems; `interpretation` for the two applications.

### 18.1 Darboux answers `H.0219`'s question structurally

> **Darboux.** All symplectic manifolds of a given dimension are **locally identical**. A symplectic
> structure has **no local invariants whatsoever.** The same holds for contact structures.
> (`H.0281`, registered.)

Set that against Riemannian geometry, which *has* a local invariant — curvature. `H.0219` asks of
every organ whether its coupling is a boundary flux or a global constraint. This is a structural
criterion for that question:

| structure | local invariants | `H.0219` verdict |
|---|---|---|
| Riemannian | curvature — **yes** | boundary flux; decomposes over a partition |
| symplectic / contact | **none, by Darboux** | **pure global constraint** — there is nothing local to read |

**That is why incompressibility forces a nonlocal solve.** `∇·u = 0` is exactly the kind of
constraint with no local content, which is `CLAUDE.md` §0b's *"a system admitting no local quotient
must couple globally"* arriving as a theorem rather than as a design note.

### 18.2 Liouville

> **Liouville.** A Hamiltonian flow preserves phase-space volume. (`H.0282`, registered.)

**A deterministic flow cannot compress phase space.** So a distribution never narrows by dynamics; it
narrows only by an observer's coarse-graining. That is `CLAUDE.md` §13 rule 2's `Π` (the lived
construction) against `Q` (the receiver's declared quotient), as a theorem of classical mechanics —
the flow conserves the volume, and the apparent spreading is a finite grain failing to track the
filaments.

Brandon's 2026-08-10 ruling — *"probability and statistics come from not being able to certainly
reconstruct any external holon's interior"* — is Liouville plus a finite grain, and requires nothing
further.

### 18.3 Arnold, and the theorem under "determinism is not predictability"

> **Arnold (1966).** The Euler equations of an ideal incompressible fluid are **geodesics** on
> `SDiff(M)`, the infinite-dimensional Lie group of volume-preserving diffeomorphisms, under the
> right-invariant `L²` metric.

A fluid state is a **point** on a manifold, the flow is **free motion**, and every apparent force is
**curvature of the group**. This is the literal form of Brandon's *"fluid dynamics genuinely take
place about the distributions of structured groups of information"* — `SDiff` the structured group,
the `L²` metric the distribution.

Arnold evaluated the sectional curvature of `SDiff(T²)`, found it **negative in most sections**, and
derived exponential divergence of neighbouring flows with a predictability horizon of roughly two
weeks for the atmosphere. **`CLAUDE.md` §0b's bound — determinism is not predictability — is a
curvature sign, computed, in the domain Brandon named it in.**

**It also names what `kelvin.rs` was missing.** In this picture circulation is the momentum map of
the relabelling symmetry, so **circulation is a pairing against a class in `H₁`, not against a
covector.** Total-sum preservation is a statement about a covector; closure is a statement about a
cycle. They coincide only when `|V| = 2`, which is why the theta graph never exposed it —
`CLAUDE.md` §0c's measured finding, with its hypothesis named.

`canon/TABLET_THE_FLOW.md` §7 holds the built gates: `analytic_field.rs` refuses construction unless
`AᵀΩ + ΩA = 0` and `A·1 = 0`, with circulation covectors required closed **and** left-fixed by the
successor.

---

## 19. Holonomy and holomorphy are one word twice, and they meet at the square root

**Truth status:** `proved-standard` for the analysis; `interpretation` for the identification of
analytic continuation with the holon.

`ὅλος` = whole. **Holonomy** = whole + `νόμος`, the law the whole imposes on a loop. **Holomorphy** =
whole + `μορφή`. **Monodromy** = `μόνος` + `δρόμος`, "running around once".

**Holomorphy is the maximal-structure case.** Complex differentiability forces conformality where
`f' ≠ 0` (`H.0284`), makes the real and imaginary parts harmonic conjugates, and gives **analytic
continuation: the germ determines the whole.** That is the strict definition of a holon, as a theorem
about a specific structure group rather than as a metaphor. The obstruction to single-valued
continuation is **monodromy**, which is the holonomy of the flat connection on the sheaf of germs.

They meet at one example the canon already depends on:

```text
√z     monodromy −1    around 0     run around once, come back negated
log z  monodromy 2πi   around 0     additive, unbounded — the winding number
```

`√z`'s monodromy **is** §2b's half turn, **is** §0b's `1/2`, **is** `structure_group.rs`'s
`CentralDoubleCover`, **is** the `±` of the root. The branch point is precisely where the whole
cannot be reconstructed from a germ, so **the sign ambiguity is the residue of holomorphy failing,
not a defect of the root.** `TABLET_THE_CHART` §10.4 lands the same fact from the chart side: the one
point the affine half-angle chart cannot see is `t = ∞`, which is `−1 = e^{iπ}`.

**And the residue theorem is the transformer.** `∮ f'/f = 2πi(Z − P)` (`H.0283`) — an oriented loop
enclosing a pole returns a winding, enclosing nothing returns zero, and the count is an **integer
because the holonomy is quantized.** That is `THEORY/60_THE_TRANSFORMER_CIRCUIT.md` §2's oriented and
symmetric readings, in complex analysis, with the quantization derived rather than asserted.

---

## 20. The intake manifold is the junction law, and it is this body's front

**Truth status:** `proved-standard` for the acoustics; `established-bounded` for the front
measurements, which are `research/records/2026-08-10_THE_SPINE_ASSESSED_BY_ITS_OWN_LAW…` §3.3–§3.4;
`interpretation` for the identification.

Brandon, 2026-08-10, noting the engine part is apt: an intake manifold is a plenum feeding `N`
runners — **one → N**, a fan-out; an exhaust manifold is `N` runners into a collector — **N → one**,
a fan-in. What sets its performance is entirely **phase**:

- a pressure wave travels a runner at `c` and **reflects at the impedance discontinuity** —
  rarefaction at the open plenum end, compression at the closed valve — and ram-charges if it returns
  inside the valve window. Helmholtz: `f = (c/2π)·√(A/(V·L))`. Long runners tune low, short tune high.
  This is a transmission line with reflection at a discontinuity, tuned by phase; §16.1's Smith chart
  is its impedance picture, and `causal_reflection.rs` is the same operation at its own altitude.
- **equal-length headers** exist so pulses arrive **in phase**; unequal lengths give the
  characteristic burble, which is a beat between mismatched channels.
- **scavenging**: one cylinder's exhaust pulse lowers the pressure that helps pull the next one's
  out. The runners do not couple to each other. **They couple only through the collector.**

Measured against this body's front: `generate_currents`'s map has **no coupling at all** — each state
reads immutable suffix ecologies and writes only its own fork — and **the entire cost of parallelizing
lives in the join**, whose `merge_witnesses` is `Vec::append` into a `BTreeMap`, associative and
therefore a monoid.

> **Runners free, collector priced.** Same sentence.

And the car states one design rule this repository had not:

> **Equal path length.** A fan-out whose branches have unequal depth pays at the collector no matter
> how decoupled the map is. In the front's terms that is **load balance**, and it is a property of
> the material rather than of the schedule — which is `H.0219`'s own bar: flux locality licenses a
> decomposition and never a schedule.

The four slots `CLAUDE.md` §4 requires:

```text
source geometry   N cylinder ports on one shared plenum
receiver map      the valve, open for a window
transport         pressure waves at c along runners of declared length
returned residual volumetric efficiency ≠ 1 — the phase mismatch, exhibited as a beat
```

---

## 21. Reflection is the mechanism, and the crossing bears the load

**Truth status:** `proved-standard` for the classical results; `implemented-exact` for the owners;
`interpretation` for the identification, which is Brandon's and predates this file.

Brandon, 2026-08-10, naming the mechanism this section exists to state:
*"pay attention to how phase distributions and emergent hypergeometry about manifolds mechanically
enable integration and differentiation by reflection (reflecting, diffracting, refracting, crossings,
intersections, section modulus, quantum mechanics)."*

### 21.1 Why reflection is a mechanism and not an image

**The interior is an integral over its boundary, and the kernel is built by reflection.** That is not
a metaphor for diffusion; it is how the kernel is constructed. The method of images solves a boundary
value problem by placing a *reflected* source across the boundary so the two cancel on it — so the
boundary condition is satisfied **by construction** rather than imposed, and the resulting Green's
function is literally a sum over reflections. `crates/holonic-engine/src/diffusion.rs` carries the
exact form: the Schur complement `S = M_∂∂ − M_∂I M_II⁻¹ M_I∂` over `Rat`, with a certificate, and the
interior recoverable as `u_I = −M_II⁻¹ M_I∂ f`.
[The record](../research/records/2026-08-09_THE_INTERIOR_IS_AN_INTEGRAL_OVER_ITS_BOUNDARY_AND_THE_KERNEL_IS_BUILT_BY_REFLECTION.md).

**And differentiation is the same operation with the sign flipped.** `causal_reflection.rs` states it
at its own altitude — *"the relation that costs an improper integral on one side costs a negation on
the other"* — which is why a return stroke riding back against its orientation negates the increment,
and why `running_integral::holonomy` refuses a walk that does not close.

So: **integration by reflection is a boundary construction, and the half-turn is what the reflection
costs.** §19's `√z` monodromy is the same `−1`.

### 21.2 The four optical words are four apertures, and each is a declared receiver

| word | what selects | the aperture |
|---|---|---|
| **reflection** | the boundary sends the current back | the image source; the residual is what does not cancel |
| **refraction** | the medium changes the phase velocity | the impedance ratio — §16.1's Möbius `Γ`, the Smith chart |
| **diffraction** | the *lattice* selects by phase coherence | Bragg: `2d sin θ = nλ`; the reciprocal lattice returns discrete directions |
| **interference** | two paths meet and their **cross term** decides | `H.0216`'s tower identity: the cosine cross term **is** the interference cross term **is** the Feynman vertex |

**The lattice row is the one that connects to §18's Darboux argument.** A crystal is not a container
light passes through; it is *a receiver that selects by phase*, and its **band gap is the set of
passages that return nothing** — the forbidden interval being an aperture of the lattice and not a
property of the light. §1.3's crystallographic restriction is the same statement about which
rotations that lattice admits at all.

### 21.3 The crossings bear the load, and that is what section modulus measures

Brandon's own reading: *"In knots it is the crossings that bear the load, this is fundamentally how
energy distributes in any system."*

**Section modulus** `Z = I/c` is the engineer's statement of exactly that: the bending stress a
section carries is `σ = M/Z`, so **the geometry of the section — not its mass — decides what load it
bears.** Two beams of equal area carry wildly different loads depending on where the area sits
relative to the neutral axis. `H.0219`'s divergence-locality classification is the same distinction
one altitude up: what a decomposition costs depends on where the coupling sits, not on how much there
is of it.

In this body the crossing that bears the load is the **hinge**: `TABLET_THE_TURN` §11.5 puts the
curvature on the codimension-two hinge between cells and never on a cell's own corners, and
`contact_gluing`'s `HingeGluing` classifies what happens where two sides meet. **A cell carries no
curvature; the crossing does.**

### 21.4 What quantum mechanics contributes, in this frame

Not a source of randomness. **The observer effect is the receiver declaration**, and the squared
modulus is the quotient by the phase circle (`H.0217`) — so a probability is what remains after the
phase is deleted, which is `CLAUDE.md` §0b's fourth carrier of the one deletion.

`2026-08-10_THE_OBJECT_IS_THE_UNRECONSTRUCTABLE_INTERIOR…` makes that measurable: **probability is
the shadow of an unexhausted candidate set.** Where the machine exhausts — `147456 → 1` candidates
over 87,380 vertices — the shadow goes and there was never a distribution. Where it cannot, the
shadow is the honest return.

**Which is why the four optical words matter mechanically rather than decoratively:** each is a way a
receiver's aperture selects, and every one of them leaves a residual that is *addressable* — a phase,
an angle, a forbidden band, a cross term. An addressable residual is one the loop can return.

---

## 22. The receiver's reach is a causal cone, and the horizon is its radius

**Truth status:** `interpretation` for the reading, which is Brandon's; `implemented-exact` for the
derivation, which is `token_invariance::saturation_horizon`; `measured` for every figure.
**Occasion.** Brandon, 2026-08-10, correcting the framing this section replaces: *"not really a
'window' I don't really like that phrase, it's a light-cone, this is relativistic physics"*, and
then on the level: *"'horizon' shouldn't be a constant either if it is."*

### What was wrong, and it was an ontology error rather than a word

The assistant described a receiver's reach as an **aperture** and then as a **window** — a hole in a
plate. Both are wrong, and the second is worse, because a window is a property a receiver *has*, and
that re-things the receiver. The unit is always a relation.

Measured the same day, and the corpus had the right object all along:

```
horizon           docs 129   code 79      ← saturated
null cone         docs   6   code  3
light cone        docs   6   code  0
causal cone       docs   5   code  0
causal past       docs   1   code  0
causal diamond    docs   0   code  0
```

**Every part was present; the object joining them had never been named once.**

### The cone, stated

A receiver sits at an **event**, not on a surface. Its reach is the causal cone at that event:

- **an apex, not a plane.** Every receiver has its own cone and none is privileged. That is what
  makes it relativistic, and it is why a declared capacity is doubly wrong — a number in *no frame
  at all*.
- **two sheets, asymmetric.** The past cone is what can have conditioned me; the future cone is what
  I can condition. The machine already declares both and says so:
  `the_axis_reads_what_the_neighbour_does.rs:78` — *"the founding horizon is deliberately not the
  reading horizon — they are two declarations."* This is causal parity: `∂∂ = 0` makes no temporal
  inverse, and a return stroke is a **chord**. It is the periplus, asymmetric under time parity.
- **three regions, not two.** Inside: causally connected. **On the null boundary: traversal returns
  nothing** — `Q(v) = 0`, §2b's vacuous difference, which in Minkowski *is* the light cone. Outside:
  not attenuated but **unable to have contributed**. A window has in and out; a cone has a boundary
  where the returned difference is exactly zero, and that boundary is a surface in the material.
- **the metric sets the cone, and the metric is already a receiver face of standing.** `CLAUDE.md`
  §13 rule 2: `grad_G L = G⁻¹ dL`, and *"the metric is a receiver face of standing"*. So the reach
  is not installed by anyone — **it is what standing looks like from an event.**
- **lensing is the metric bending the cone**, not a diaphragm. The body already has this and it was
  dismissed once as a proper name: `soma/body/src/manifold.rs:158`, *"the deposited circulation DRAGS
  the passing frame WITH it (**Lense–Thirring as the general law**)"*.

### The machine was already computing causal diamonds and calling them windows

`token_invariance::step_at` writes index `2(k−1)` as `L^k` and `2(k−1)+1` as `R^k`, so a window
enumerates an occurrence's neighbourhood **shell by shell** — `−1, +1, −2, +2, …` — in order of
`|offset|`. That is a discrete causal diamond: two sides are two sheets, the shell index is proper
distance along the stream, and `None` is where the whole ends, which is the material's own boundary
rather than padding. **The horizon is that diamond's radius**, and it was a literal `1` in every
driver.

Two consequences follow and both are load-bearing: the window at `h` is a **prefix** of the window
at `h+1`, so refinement is monotone; and the first differing index is **the shell at which two
occurrences separate**, which the shared-prefix array already reports.

### The horizon is read off the material — and a cone propagates, it is not searched

`saturation_horizon` (`crates/holonic-engine/src/token_invariance.rs:2276`) holds the partition and
refines it one shell at a time, touching only occurrences whose class is **not yet a singleton**
(`:2154`, `classes.iter().filter(|c| c.len() > 1)`). A singleton can never split again, so that
population shrinks monotonically and the accumulated work (`:2161`) is

```text
   Σ_k  (occurrences NOT YET SEPARATED at shell k),   k = 1 ..= bound
```

**Corrected 2026-08-10 by reading the owner. This paragraph said the work was "the volume of the cone
that is still live, not the volume of the cone", and that is not what the code sums.** Two things
separate the two readings, and both are in the source:

- **`bound` is census-wide, not surface-local.** `:2140` takes
  `material_horizon_bound(census).max(1)`, and `material_horizon_bound` (`:2017-2024`) is the length
  of the **longest whole in the entire census**. A surface's shell loop therefore runs against a
  ceiling set by material it never touches — a coordinate of the corpus promoted into the cost of
  reading one surface, which is the absolute-frame defect §0's second lesson names.
- **Not-yet-separated is not still-carrying-difference.** `shell` (`:2084-2101`) returns `None` on a
  side once the site leaves its own whole's stream, so past the ends of its material an occurrence
  reads `(None, None)`. A plural class whose members have all run out of material compares
  `(None, None)` against `(None, None)` at every remaining shell, cannot split at any depth, and is
  still counted in `active` at each one — carrying no difference while being summed as though it
  did. The loop exits early only when `active == 0` (`:2155-2158`), which such a class prevents.

So the honest statement of what `active_total` is today: **the number of occurrence-shells the
refinement visited, summed over occurrences still sharing a class, out to the whole census's longest
whole.** It is an **upper bound** on the live cone's volume and is never equal to it — a class that
is plural at shell `k` and does not split there carried no difference at `k` and was still counted.
The gap is bounded when every class eventually reaches a singleton, which is what `exhausted`
reports and what the declared corpus below satisfies at 29,533 of 29,533; it is unbounded when one
does not, because the shells then run to the census ceiling regardless of the surface.

**The repair is owed in the code, not here.** `token_invariance.rs:2051` carries the same sentence
as a doc comment on the field (*"The cost, exactly: occurrences still carrying difference"*), so the
document and the owner are wrong together; the field's name is honest and its description is not.
What the loop needs is a ceiling read off the **surface's own** reach rather than the census's, and
a plural class all of whose members are past their material must be recognised as terminal.

**The first implementation binary-searched inside the material's ceiling, and that was the error the
ontology predicts.** Probing at the ceiling materializes `2 · bound` readings per occurrence; on
this repository's own corpus it reached **19.6 GB resident on one core in 6m39s with no output** and
was halted. The propagating form runs in **0.22 s**. *Light does not sample its way to a horizon; it
advances one shell at a time and stops where the difference dies.*

Stopping is a theorem, not a heuristic: a quiet shell does **not** prove saturation, because
refinement can stall one shell and resume — `Z A B C D E` against `W A B C D E`, read at `C`, agree
at shells 1 and 2 and differ at 3. The loop stops when every class is a **singleton**, which no
deeper shell can split, or at **that surface's own** ceiling.

**The ceiling is the surface's, not the corpus's — corrected 2026-08-11.** An occurrence at position
`p` of a whole of length `L` reads `max(p, L−1−p)` shells and `(None, None)` forever after, so a
surface's ceiling is the maximum of that over its **own** sites. Running every surface against the
longest whole *in the census* let one unrelated long document lengthen an unrelated surface's loop
for material that had not changed — a corpus-global coordinate deciding a surface-local cost, which
is §0's second lesson. Measured: summed surface-local ceiling **204,777,453** shells against
**854,324,625** the corpus ceiling imposed, a 4.17× worst-case bound. It costs nothing where every
surface exhausts, which this corpus does, and it is the whole cost where one does not — so a declared
control supplies the material the corpus cannot: two byte-identical wholes, read once beside a short
filler file and once beside a long one, where the corpus ceiling moves and `bound`, `shells`,
`active_total` and `classes` do not.

### Measured on the declared corpus

The corpus grows, so every row carries its clock.

| | 2026-08-10 | 2026-08-11 |
|---|---|---|
| corpus ceiling, read off the census | 28,875 shells — the longest whole | 28,875 |
| word surfaces / occurrences | 29,533 / 1,187,776 | 29,587 / 1,193,603 |
| `active_total` — occurrence-shells visited, summed over occurrences not yet separated | **1,710,423** | **1,730,964** |
| surfaces the authored `1` could not see whole | **10,230 of 29,533 — 35%** | **10,265 of 29,587** |
| distinctions it missed | **423,250** | **426,036** |
| `"the"` | horizon **49**, 37,530 classes against **3,990** at `h = 1` | horizon **85**, 37,797 against **4,002** |
| corpus horizon | **51**, forced by exactly one surface: `"that"` | **88**, forced by exactly one: `"a"` |
| termination | **29,533 of 29,533** exhausted to singletons — final by theorem | **29,587 of 29,587** |
| surfaces whose least final radius is **0** | not reported — an authored `.max(1)` returned them as `1` | **10,676 of 29,587** |

**The last row is a repair, not corpus growth.** `saturation_horizon` returned `last_split.max(1)`,
so a surface no shell ever split — each of the 10,676 occurs exactly once, and has nothing to
separate — reported a least final radius of `1`. The floor was invisible to
`tools/authored_levels.py` because it is not a `const`, and its unit test was guarded
`if horizon > 1`, excluding exactly the case the floor decided. The card carried the identical floor
in `cuda_refine.rs`; both now return `0`, and `the_card_refines_the_front` re-run on an RTX 4080
SUPER agrees with the CPU on every surface it reads — **18,911 of 18,911** at the first re-run and
**18,917 of 18,917** at a later one the same day, with **68,734 crossings on the card against 68,734
shells on the CPU: one law, one cost.** The two figures differ because *the corpus grew under the
measurement* — another session is writing files into it — which is the reason every row above carries
its clock rather than a bare number.

**And the two carriers are now handed the same ceiling.** 163,023,246 shells surface-local against
546,228,375 the corpus ceiling imposed, with a declared control that neither carrier is handed a
foreign one. A cost law that held on the CPU and not on the card would have been a second frame
smuggled in as an optimisation.

**WITHDRAWN 2026-08-11: the sentence that stood here was produced by a broken gauge.** It read
*"The corpus cannot grade the loop's soundness — zero of 29,533 ever stall."* That zero came from
`SaturationHorizon::walked_past()`, which returned `shells > horizon` — **false on every propagation
that exhausts to singletons**, because the last shell walked is the last shell that split. It
measured no quiet shell at all, returned `false` even on the fixture built expressly to exhibit one,
and its unit test passed only through an `|| exhausted` disjunct, which is `¬e ∨ e`.

Re-measured 2026-08-11 with `interior_quiet_shells` — shells that split nothing **and** were followed
by one that did:

| | |
|---|---|
| surfaces that stall and resume | **5,008 of 29,587** |
| interior quiet shells, total | **27,668** |
| deepest resumption | `"first_depth"`: quiet at shell **1**, resumed at shell **73** |

**So the corpus grades the loop's soundness emphatically.** A loop halting at the first quiet shell
returns the wrong horizon on 5,008 real surfaces, and on `"first_depth"` it returns 1 where the truth
is 73. The declared fixture is kept and is now the *stronger* half rather than the only one: it
exhibits the **witness** — the quiet shell, the resuming shell, and the two occurrences that
resumption pulled apart, each checked to agree at the quiet shell and differ at the resumption —
against a second, independently written unsound loop. `CLAUDE.md` §8's rule stands; what failed was
the measurement that invoked it.

### The two costs are different objects, and conflating them is what "aperture law" did

```text
   reading      O(d · h)    the volume of the causal diamond the window enumerates
   exhibition   C(d, 2)     the pair product — a PRESENTATION, not a transport
```

On `"the"`: **1,838,970 to read against 704,231,685 to exhibit — 383×.** A caller's declared
capacity guards only the second. Calling it *"the aperture law"* promoted an output-buffer guard to
a law and then reasoned from the promotion.

### The charts, built — and what the constant was standing in for

`SeparationChart::{Orbit, Star(i), Pair}` with `demand(chart)` computing extent and the exact
transition degree from `d`, and `pair_atlas()` returning the `d` star charts. Proved: the atlas
covers the pair chart as a **multiset**, each separation reached from both endpoints, `2·C(d,2)`
against `C(d,2)` doubled — a rebase with no remainder. And the demand is required to **vary over the
base**, because a quantity that did not vary is one a constant could have served.

Measured on the declared corpus, at the surface the constant used to refuse:

```text
  "the"     pair chart   571,608,766 points   over 33,812 orbits   degree 33811/2
            star chart        33,811 points                        degree 1     ← returned WHOLE
```

**Both drivers now carry no capacity at all.** The cross-check compares in the degree-one chart:
31,933 readings, 0 disagreements; 27,171 surfaces whose pair chart is wider are named with the width
their own material required rather than skipped by a number.

### The same law one altitude up: the sweep is a front

29,533 surfaces, each reading independent of every other — shared immutable census and atlas,
disjoint occurrences. That is a front, and `sweep_over` covers it across the charts a caller
declares, by **extent** rather than by count. Driving it serially pinned one CPU core while
twenty-three stood idle, which `CLAUDE.md` §9 names a defect to diagnose rather than narrate.
`the_covered_sweep_equals_the_serial_sweep` requires the readings to be identical: a lane is a
realization coordinate and may not move a reading.

**Two defects were introduced and removed while building this, and both are one shape:**
*materializing a population to learn a number the material already carried.* Folding the whole star
atlas costs `2·C(d,2)` — twice the pair chart it replaces, so reading the atlas means one chart at a
time. And computing each surface's demand by rebuilding its complex re-ran the most expensive
operation in the organ for a number the sweep was already holding. Each pinned a core for minutes.

### The card refines the front — GPU-first, on the whole corpus

**Deposited 2026-08-10.** Brandon: *"the card's integration is so fucking important and you can't
just keep punting it… every time we have to go from it not being integrated to integrating it, you
risk contamination. It's GPU first."* And on the demonstration: *"I don't know why you only show me
`"the"`… you are still treating the machine like a toy without a purpose."*

`kernels/refine_shell.cu` + `crates/holonic-engine/src/cuda_refine.rs`. One lane per occurrence, one
crossing per shell. Equality of readings is made equality of **dense identities** once over the whole
corpus — 550 distinct readings — with identity zero reserved for a terminus *before* any reading is
assigned one, because a terminus is family-invariant and must be a value no reading can take. A shell
key is then one `u64`, and the new class is the identity of `(current class, key)`, claimed by
`atomicCAS`. The atomic is on the **claim**, never on the reading. The table cannot fill: distinct
pairs are at most occupied occurrences, so a capacity above that always leaves an empty slot —
derived, no load factor, no number chosen.

Measured on the declared corpus, RTX 4080 SUPER, 1024 threads per block and warp 32 both read off the
device and the kernel:

| | |
|---|---|
| surfaces refined on the card | **18,889** |
| crossings | **68,647** |
| partitions agreeing with the CPU | **18,889 of 18,889** |
| derived horizons agreeing | **18,889 of 18,889** |
| idle lanes, named rather than hidden | 18,760,509 |
| deepest cone | `"a"` at horizon **88** over 19,072 orbits |

**A partition is not a numbering.** The card claims identities in probe order and the CPU in
lexicographic window order, so the comparison is of the induced **equivalence** — requiring the
numbering to match would be requiring a realization coordinate to be causal.

**And the first run disagreed, which is why it was run.** The card returned 1,794 classes for `"of"`
at shell one against the CPU's 1,787 — finer, never coarser. The cause was a race of my own making:
the claim and the key are two stores, and a lane that found its own class in a slot whose key had not
yet landed walked on and claimed a **second** slot for the same pair. It splits a class in two and
looks like nothing. The trace shell by shell is what found it; the aggregate said only *"116 horizons
disagree."*

### One law, many materials — the factoring, which is the theorem and not a refactor

**Brandon, 2026-08-10, and this is the correction the section above did not yet carry:** *"why the
fuck do you think you have a choice about 'paths'… why is this not ontologically integrated →
encapsulation and factored in the codebase for streamline networking and interconnections based in
how we expect the machine to work according to the theorem."*

A device path per organ is the **cabinet-of-organs failure one level down**. `canon/THE_HOLOBROCHOS_SPINE.md`
convicts it for organs; it is no better for carriers. And the governing record already fixes the
ontology — *"CPU/RAM and GPU/VRAM are local charts of the same caused body"* — while `CLAUDE.md` §4
fixes the method: **one operation carries many materials.**

So the refinement is split at the joint the theory names:

```text
   MATERIAL   the key an occurrence carries at causal shell k        token_invariance::shell_key
   LAW        the identity of (class, key)                           cuda_refine::quotient_on_*
```

The law is **material-free by construction** — its only inputs are a class and a key per cell — so it
knows nothing of streams, occurrences, windows, states or language. `kernels/refine_shell.cu` carries
the same split: `shell_keys` is the material, `claim_identities` is the law.

**Who conducts through it, stated as reach rather than as intent — measured 2026-08-10.** The
sentence that stood here, *"every organ with a front supplies a key law and shares everything else"*,
is the design and not the position.

**RE-MEASURED 2026-08-15, and the 2026-08-10 census had decayed in both directions.** It read
*"`cuda_refine` has three consumers"* and named one that no longer exists: `current.rs:921`
`quotient_generation_states` occurs nowhere in the tree — `grep -rn "quotient_generation_states"
--include='*.rs' soma crates` returns zero. The module meanwhile gained library consumers the census
could not have seen. Command:
`grep -rn "cuda_refine\|CudaRefineExecutor" --include='*.rs' soma crates`.

```text
   LIBRARY   holonic-engine: embedding_fiber, receiver_exact_compression, token_invariance
             life: causal_section
   DRIVERS   the_card_refines_the_front:40 (the separation front's card path),
             the_foreign_map_founds_its_axes, the_code_material_returns_its_world_line,
             the_conditioned_section_returns_after_detachment, the_operation_survives_the_codec
```

So the factoring carries more materials than the census recorded, and the reading it supported —
*"the CPU-side migration of the organ that motivated the factoring is owed"* — is stated against a
population that has moved and must be re-taken before it is cited again.

**Proved on both charts and against the organ:**

| | |
|---|---|
| CPU and card return the same partition | 1 · 2 · 31 · 32 · 33 · 1,024 · 40,000 cells, on the real card |
| the organ's key through the shared law = the organ's own refinement | every separable surface of the declared fixture |
| the separation front on the card, unchanged by the factoring | 18,891 surfaces · 68,653 crossings · partitions and horizons 18,891 / 18,891 |

**Equality is of the induced equivalence, never of the numbering.** A carrier claims identities in
whatever order its lanes reach them, and requiring two carriers to agree on numbering would be
requiring a realization coordinate to be causal — the record's own words: a lane, a warp, a block and
a CPU thread are realization coordinates and none is a holon.

### Chronology is not seriality — arcs, junctions, and why the card's model is the same law

**Brandon, 2026-08-10, correcting a flattening this section had built on:** *"one receiver's returned
chronology is not necessarily serial, it's a distribution of arcs, like the lightning leaders… I do
not know why you don't ontologically understand why events are ever serial in arcs and
electromagnetic events as opposed to parallel and branching in junctions."*

The distinction, stated so it can be used:

- an **arc** is one conducting channel, so what travels it is ordered;
- a **junction** is where current distributes, so what leaves it is co-present;
- **irreversibility and total order are different properties.** Time parity — the arc's asymmetry —
  is not seriality. *"Do not remove chronology"* forbids deleting the causal order; it does not
  license asserting a line where the material has a **tree**. Conflating the two is what produced a
  serial walk over a population that branches.

**And the device's execution model is that law in silicon rather than an analogy for it.** Lanes of
a warp are co-present exactly while they share a path and the hardware **serializes them when they
diverge** — arcs serial, junctions branching, enforced by the physics. The many channels exist to
carry combinatorial binary path distributions, which are `H.0150`'s membership words: the Boolean
lattice, crossing depth, inclusion–exclusion as its Möbius function. A monitor is a receiver and a
distribution is a receiver, and the pipeline carrying a triangle through model → world → view → clip
→ screen is transport of a relation across charts with an interpolation law. The triangle is the
primitive because it is the smallest carrier of a relation with a hand — the tower, the law of
cosines, the hinge deficit, and Brandon's own *"in friction triangles are the quantum."*

### One expansion law — built, proved, and conducting for ONE of the three organs

```text
   token_invariance::sweep_covered      surfaces     -> readings
   morphological_language generation    states       -> successors
   causal_language leader               branch tips  -> continuations
```

A covering per organ is the cabinet failure one level down, exactly as a device path per organ is.
`hardware_cover::expand_front` (`crates/holonic-engine/src/hardware_cover.rs:1019`) is the law: the
material supplies `cell -> successors`, the law covers it by **extent**, and successors are
reassembled in the **front's own order** so a lane's completion order never becomes chronology.
Proved identical at 1, 2, 3, 8 and 64 lanes over a branching front (`:778-803`), with a failing cell
surfacing from any lane (`:807`).

**Corrected 2026-08-10: the migration is one organ of three, and this subsection claimed all three.**
`expand_front` has **six** occurrences in the tree — the definition, three of its own tests
(`:785`, `:790`, `:809`), and exactly **one external caller**:

| organ | what it covers with, today |
|---|---|
| `causal_language` leader | **`expand_front`** — `soma/life/src/causal_language.rs:482`, with the tip's extent supplied as `emitted.len() + 1`. Migrated. |
| `token_invariance::sweep_covered` | its **own** by-extent placement, `token_invariance.rs:1776-1811` — the same law, written twice. Not shared. |
| `morphological_language::generate_currents` | `std::thread::available_parallelism()` directly (`soma/life/src/morphological_language/ecology.rs:1453`) and sections the front `sections[at % lanes]` (`:798`) — **by count**, which is the law `sweep_covered`'s own comment names as wrong at `token_invariance.rs:1776`: *"Cover the surfaces by EXTENT, not by count: a surface with a million occurrences and one with two are not one unit each."* Not shared, and covering by a different law. |

So what is established is that the law exists, is proved lane-invariant on a branching front, and
carries one organ. Two migrations are **owed**, and the second is not a rename: it changes
`generate_currents` from a by-count cover to a by-extent one, which is a change of law and not of
plumbing. `hardware_cover.rs:866-875` and `causal_language.rs:480-481` both already describe the
three-organ sharing as accomplished, so the same overstatement sits in two code comments and is owed
there too.

### What mounting a carrier used to cost, measured

`condition_route_receivers_with_executor` walked receivers in a plain `for`, threading one carrier
through all of them, while its CPU twin `condition_route_partition` says outright: *"Parallelism
lives across independent receiver ecologies; one receiver's returned chronology remains serial."*
**So mounting a card cost the parallelism** — the device sat resident holding 2 GB at 0% while one
CPU core walked the population, which is precisely what was observed.

Repaired: each lane of the receiver cover mounts its own carrier, and the caller's carrier keeps a
section so a mounted card is never idled. Measured on the bounded corpus:

| | before | after |
|---|---|---|
| device utilisation during conditioning | 0 % at 2,066 MiB | **34 % at 6,191 MiB** |
| conditioning | did not complete under observation | **103.5 s, completed** |

**And the wall that remains is named rather than dressed:** generation does not return on this
corpus, which is the condition `canon/THE_MEASURED_CAPABILITIES.md` already records — `4 → 55,098 ms`,
`8 → no return`. Conditioning crossing the card does not move it, and this section does not claim
otherwise.

### What this section forbids

1. **No receiver reach described as a window, an aperture, or a capacity.** Name the cone, its apex,
   its two horizons, and its null boundary.
2. **No horizon authored.** It is read off the material or declared by a caller **with the reason
   stated**; `token_invariance`'s *founding* horizon is still a caller declaration and deriving it is
   owed.
3. **No cost claim borrowed from an organ that refuses a presentation.** The reading and the
   exhibition are different objects; say which one a figure measures.
