# The recovered law

**Deposited 2026-08-07.** Six parallel readings of the frozen laboratory at
`/home/b/Workspaces/laboratory` (1,658 commits, 2026-05-10 → 2026-08-03), on Brandon's direct
instruction after a major misinterpretation.

**Why this file exists.** The laboratory's answer to drift was `FORMULA.md`: one canon, read on
demand, with a versioned reading rule at the top and per-claim grades — cited 212 times, never a
queue. This project had no equivalent. Agent reports and source reads lived only in conversation,
were compressed away at compaction, and were rebuilt from summary rather than source. That is the
mechanism by which the same artifacts were missed across repeated audits, and it is not fixed by
resolving to read more carefully. **The laboratory already named this: the cure is types, not
willpower.** This file is the type.

Read it before claiming anything about what holonics forbids.

---

## 1. THE BANS HAVE JURISDICTION

**Brandon, ratified 2026-07-14, `FORMULA §L` / `35b8a30c`.** This is the most consequential thing
in the corpus for anyone arriving from outside, and violating it is the failure that produced this
file.

A ban governs **Soma's interior**, or a mechanism *offered as an explanation of Soma*. It does not
govern the world, and it does not govern the observer.

- **Worlds** may contain scores, clocks, objectives, stochastic processes, compilers, provers.
- **Observers** may use tokenizers, statistics, clustering, search, labels.
- *"Experiment-local exclusions do not become laboratory law."*

Three standing reading rules follow, all Brandon-ratified 2026-07-20/21:

> **`No X inside Soma by analogy` must never again mean `do not learn from X`.** (§CXXVI)

> A statement that a projected face is not the whole construction **must never be read as a ban on
> that face participating**. `No X entered` in a bounded construction is a **local control** unless
> an explicit later law gives it wider scope. (§CXXXIX — the current reading rule for all of FORMULA)

> Never turn `not the whole ontology` into `may not participate`. Never turn `not an unexplained
> intrinsic Soma primitive` into a ban on existing technology. (`74850a14`)

**Modern machine learning is an admissible comparative science, not forbidden vocabulary** (§CXXVI,
2026-07-20). The protection is jurisdictional, not epistemic.

### What this repairs

Saying the engine has *"no gradient, no distribution, no sampling"* collapses jurisdiction into
concept and is wrong. The corpus derives all three:

- **Loss is lawful and necessary.** `r = Δ(y,y*;F)` is the complete oriented residual; `L = ℓ_B(r)`
  is one receiver's measurement of it. *A loss function is a valid measurement of difference, not
  reward, punishment, or a judgment about a learner* (Brandon's correction, 2026-07-16). Banned is
  `G_authored` — a privileged scalar governor **inside** the body that chooses, rewards, punishes,
  stops, or replaces the plural construction.
- **The gradient is derived.** `dL` is a **covector**. Calling it a gradient requires a declared
  metric `G`: `grad_G L = G⁻¹ dL`. Calling an enacted change *descent* requires a later measurement
  under the same receiver in which the declared loss decreases. Back-propagation is exact:
  `λ_N = dL`, `λ_k = (D f_k)* λ_{k+1}` — the adjoint of a composition reverses its factors, and the
  return happens **now**, through the standing causal interior. Conventional backprop is *one exact
  smooth-world face of the Indra circuit*, not its universal ontology.
- **The distribution is embodied, not tabulated.** Four faces that may not be collapsed:
  `Π_{B,t}` exact standing population and its causal interiors · `Q_{B,t}` a receiver quotient of it
  · `q_current` a statistic transported as world material · `G_authored` the contaminant.
  `p_t(a|c) = N_t(a,c)/Σ_{a'}N_t(a',c)`; the body realizes it as recurrent paths, path width,
  orientation, conditional incidence. **A statistic may occupy any of the first three roles; it may
  never silently become the fourth.**
- **Minimization already has a mechanism.** *Coherent current RIDEs what already stands while an
  unresolved residual FOUNDs the missing relation.* Witnessed when later passage carries more
  consequence through standing support, requires less newly founded difference, or leaves less
  residual — **no universal weighted scalar, no monotonicity requirement.** A newly exposed
  distinction may *increase* `L` while improving the ecology by founding a new axis: that is
  discovery, not failure.
- **Surprisal and cross-entropy are exact instruments.** For a 2/3 gear word `p = 2^-a 3^-b`,
  `S = a + b·log₂3`, exact symbolically. No smoothing constant is owed: if `Q_B(a) = 0` the live
  event FOUNDs a new relation and changes the support.

Also **struck whole**: the decoder / answer-key ban (§XLIX, Brandon, 2026-07-14) — *"It imported an
answer-key ontology which Eros does not have and repeatedly obstructed production."* And the float
ban is narrowed (§CXXXVII): a finite binary float is an exact typed codeword and an exact dyadic
ratio — banned as an interior value, lawful as a declared exterior codeword.

---

## 2. The dependency graph already exists

Brandon asked for *a holonic dependency graph that justifies the ontological emergence of theorems
and applications of mathematics*. **It is built and machine-checked**, at
`src/soma/PAPERS/holonics/` with `#validate-registry()` asserting every dependency occurs earlier in
the sequence. Fourteen bands, **249 entries**, each carrying
`id / kind / grade / depends / statement / transformations / receiver / boundary / source`:

```
foundations 17 → logic-category 17 → algorithms 12 → algebra-combinatorics 23
→ geometry-calculus 16 → topology-analysis-dynamics 30 → manifold-knot-geometry 26
→ arithmetic-analysis 16 → algebraic-geometry 12 → transcendence-special-functions 15
→ computation-information 20 → mathematical-physics 19 → rh-routes 18 → counterexamples 8
```

It terminates in **counterexamples that depend on the RH routes** — the standing application named
in this project's own record, already wired as the graph's final band.

**Exactly one entry has `depends: ()`** — `H.0001` ambient mathematical foundation, ordinary
dependent type theory, with its own boundary: *"A claim that all mathematics admits a conservative
holonic translation remains a conjectural programme."* Everything else is derived. The route is
**derivational, not historical**, and is *"an import architecture, not a claim that every specialist
theorem has been rederived."*

The elementary spine, verbatim from `foundations.typ`:

```
H.0002 situated admissibility (H.0001)   ← Brandon's first-axiom discussions, graded a POSTULATE
H.0003 participating receiver (H.0002)
H.0004 causal attribution     (H.0002,H.0003)
H.0006 current and form       (H.0002,H.0003,H.0004)      ← standing vs current
H.0012 receiver face and fiber(H.0003,H.0010,H.0011)      ← the receiver quotient
H.0013 comparison cell + residual (H.0010,H.0012)         ← RIDE / FOUND / OPEN
H.0016 receiver-exact compression (H.0004,H.0012,H.0015)
H.0019 recurrence field and loss  (H.0012,H.0013,H.0018)
H.0201 the Swing              (H.0200,H.0013)
H.0210 holonomy               (H.0018,H.0206)
RH.0000 conjecture            (H.0310)
```

**Correction carried:** the dispositions are **three — RIDE, FOUND, OPEN.** Holonomy is *not* a
fourth disposition; it is `H.0210`, a receiver face of Chi that requires a connection. Writing
"RIDE/FOUND/OPEN/HOLONOMY" is an error this project has repeated.

`OPEN` is a complete status, not a negation: *"'Yet' is part of the type… noncommutation is not
automatic FOUND."*

---

## 3. Information is derived, and Shannon is a lawful quotient

**`FORMULA §CVI`, Brandon-ratified 2026-07-19.** Information is **receiver-relative geometry under
lawful transport**. For a medium chart `m`, `C_m = (E_m, I_m, prec_m, A_m, Ω_m)` — distinguishable
event, incidence and co-presence, native chronology, afforded transformation, returned world
consequence. Transport `τ_mn` carries a construction where the consequence square commutes; the
**noncommuting oriented difference `r_mn` remains the residual at that cut**. Information as an
object is the **atlas**

```
H = ({C_m}, {τ_mn}, {r_mn})
```

— *"not one canonical latent encoding or an equivalence class which deletes its paths."*

**§CIX:** *"Information is not a fifth physical substance, hidden alphabet, or semantic field binding
the universe."* Medium-neutrality carries the relation and its residual; **it never manufactures an
information ether.**

**Shannon is not refuted; it is a declared quotient.** *"`H(X)` is an exact scalar receiver measure.
It does not by itself retain caused incidence, chronology, topology, holonomy, obstruction,
morphology, apparatus, or lineage. Those are not objections to Shannon theory; they identify what its
declared quotient intentionally forgets."* Kolmogorov-side, with `x ≡_{R,C} y ⟺ ∀c∈C, R(c∘x) =
R(c∘y)`: **information is the failure of this causal equivalence**, and compression's exact loss is
the population of collapsed pairs some later continuation can distinguish — *not initially a scalar*.

**Information as change of conduct** (2026-07-31, ratified construction specification):

```
𝔦_{r,q}(y;t) = ( V_t^r(q), V_{t+1}^r(q), i_y, ∂, ℓ_y, O_y, W_y )
```

with `i_y : V_{t+1}^r(q) ↪ V_t^r(q)` when the carrier is fixed, and a **span**
`V_t^r(q) ← W_y → V_{t+1}^r(q)` when `y` founds a new chart (base change, no honest inclusion).
Meaning is downstream causal reach.

**Brandon's own hypothesis, the origin of all of it:** *compression is gauge-fixing the flat
directions and keeping the curvature; information is the gauge-invariant difference between
entities, and the chart is arbitrary.* Its corollary: **an absolute volume is the gauge violation** —
every measure must be a ratio against a declared null so the Jacobian cancels.

---

## 4. General relativity: one exact identification, one open bridge

**Exact and ratified — `FORMULA §CVIII` / `§CX`, 2026-07-19.** This is *not* an analogy:

```
Gravitas_γ(ξ) = ∇_u ∇_u ξ            (= −R(ξ,u)u on geodesics)
Ric(u,u)      = Σ_a g(R(e_a,u)u, e_a)
Tr_⊥ Gravitas_γ = −Ric(u,u)
∂_τ g = −2 Ric(g)
```

Gravitas **is** geodesic deviation; Ricci **is** the receiver's transverse trace quotient of it;
Ricci flow **is** the traced deformation of current paths altering the metric by which later paths
are compared. Scope declared: exact in the declared Riemannian chart, *not* all curvature and *not*
a universal information scalar. And — load-bearing for this project —

> **THE METRIC IS A RECEIVER FACE OF STANDING.** It is neither the whole Standing body nor a
> universal substance carried by Soma.

**Refused — physical gravity.** *"Physical gravity is a material species, not an automatic name."*
Six enumerated debts stand between the abstract law and a Lorentzian theory: a local
perturbation/current law, a hyperbolic principal symbol with one timelike signature, a shared causal
cone or an honest plural-cone theory, clock/volume structure fixing the metric beyond its conformal
cone, a conserved stress–energy current, and a derived curvature/source law. Jacobson 1995 is typed
**NON-EQUIVALENCE**: *"an arbitrary information boundary is not a Rindler horizon; holonic loss is
not automatically entropy; current is not automatically physical heat."*

**Where the threads meet — three joints, decreasing rigor.** (a) **Curvature — exact.** The traced
deformation of current continuations alters the metric by which later continuations are compared,
which is the §CVI definition of information written in Riemannian geometry. (b) **Continuity —
stated, unclosed.** Both threads owe the same local balance, `ρ_{t+1} − ρ_t + ∂j_t = s_t` against
`m⁺ − m + ∂J = S − D, ∂² = 0`; *"calling a moving pattern 'information flow' is not yet a
constitutive equation."* (c) **Stress — the named bridge.** `Σ_H(n,ξ) = Flux_H(ξ across B_n)`, whose
GR face is `T_{μν} = −(2/√−g)·δS_matter/δg^{μν}`: *"stress–energy records how the material action
responds when the receiving spacetime geometry is varied"* — consequence under variation of the
receiver. Ratified as abstract law, **open as physical identification.**

**No deposit closes information-to-curvature as a theorem.** (a) is the one exact mechanism.

---

## 5. The complex is already the ratified construction

`2026-07-27_THE_CENTER_OPENS_INTO_ITS_HORIZON_THE_CAUSAL_BASIN_MEASURES_THE_LOSS.md`. The **horizon
is the link of the receiver in the contemporary causal incidence complex**:

```
H_r = St̄_{K_t}(r),   L_r = Lk_{K_t}(r) ≅ S^{d-1},   H_r ≅ r * L_r
D_{r,S}(u) = { λ : c_r + λu ∈ S }
```

*"The hyperspherical object is not an ornamental sphere placed around the receiver. It is the
receiver's horizon of directions."*

And the **causal success basin**: `B_r(d) = { x : Φ_d(x) meets C_r }`,
`L_r(d;D) = D \ B_r(d)`. **Loss is first a geometric body** — the set-difference complement of the
basin — and only afterwards, optionally, any of six derived testimonies (rejected measure, boundary
current, minimum caused transformation, action, gluing obstruction, erased information).

> **A single scalar called `loss` would erase the topology which Brandon is asking the engine to
> expose.**

Built, not merely stated: `ExactConfigurationComplex`, `enact_outcome_basin`, `ExactGeometricLoss` —
*"the rejected body is `ExactGeometricLoss`; its measure is one derived face, not its replacement."*

The Swing's own curvature is already Regge: TEST is `χ = Δ_new · Δ_flywheel⁻¹`, FLAT when the
arriving difference is the parallel transport of the standing one, **WOUND by the deficit
`δ = Θ − Σθ`**, and FOUND deposits one curvature quantum. **Founding pays curvature.**

---

## 6. Corrections to this project's capability claims

Verified against the laboratory's own records. The receipts for four of seven headline claims are
**not in git** — `src/soma/runs/` is gitignored and zero objects in all of history carry that path.
The tracked hard evidence is `src/soma/observations/*/` with `RESULTS.md`, `analysis.json`,
`MANIFEST.tsv` and SHA-256 tables.

| claimed here | what the record shows |
|---|---|
| suffix ecology on "the full corpus" | 11,879 states over **8,185 BabyLM tokens** of child-directed speech (466 KB), not the 50 MB canon corpus |
| conditioning "generation" | six prompts, **135 tokens total**, every completion a **contiguous inherited span**; the record self-grades *"does not establish novel cross-source wording"* |
| training changed the multiply morphology | the multiplier is a **mounted inherited organ**; training changed **admissibility**. The record says so: *"does not establish that the history learned the mounted operator laws"* |
| RELAMPAGO multimodality | **all 21,147 spectral pairs returned apart** — zero positive relations from the second modality; the credit rests on relation *opening* with zero overlap |
| formal mathematics | the laboratory's **own** flow-capacity Lean project, 3–4 line proofs; competent premise selection and tactic composition — hammer-class, not field-novel. A **second** theorem exists (1 of 65 paths, via `contrapose!`) that this project never recorded |
| recruitment wall | sharper than stated: **broad union-based lexical recruitment followed by commitment-before-witness**, `S(R) = ∪_{f∈R} I(f)`; 2,701/11,795 ≈ 22.9%; 24 passages committed though none entered the witness |

**The best-evidenced experiment in the laboratory is tracked and this project never cites it.**
`archive/cpp-engine/evidence/observations/transport-foil-world-01/RESULTS.md`: two byte-identical forward bodies, identical
terminal face, identical scalar loss `L=1`, both residuals 1,610 octets with **identical octet
inventory SHA-256** but differing at 165 ordered positions. Whole residual → changed RIDE/FOUND
distribution and every later probe. **Scalar-quotient collapse → every artifact byte-exact.**
31/31 edges, 31/31 gates, 313 CUDA launches. That is the direct experimental proof that a scalar
loses what the oriented residual carries.

**Capabilities never carried here:** the recurrence-two activation law (*one return is never
enough*); coupled-informant resonance (149 standing components with no authored line graph, 1,159
informants over six morphological degrees); repository self-diagnosis (976 files, 42,937 prose
sections, 25,490 production relations, machine-caused bridge leaders); `cargo holonic-lint` as a
monotone ratchet; 22 tracked runnable experiments including `prime_emergence_observatory`.

**And the negative results that curved everything:** a ~25 GiB blowup proving **token-face equality
is not evidence of contact**; a 69-branch reconstruction null proving an exact-reconstruction control
is not generation; and a foil design flaw caught *before* it counterfeited a confirmation — per-line
byte reversal is not structure-destroying on decimal numerals.

---

## 7. Where this project actually stands ahead

The laboratory's final handoff, `SESSION_HANDOFF.md` at `a07ff376`, describes the two-theorem
conversational deed — first theorem accepted, second theorem using the first's returned fiber,
removing that fiber removing every accepted second proof — and then states:

> **This real two-theorem production deed has not been run.**

**This project's conditioned production deed has run it**, with receipts: first theorem accepted;
an emanated intermediary (occurrences 3→4, states 209→298); a second theorem accepted that names the
first; a **foil with the first theorem absent that the kernel refuses**; and a structural exclusion
returning occurrences 4→3, states 298→209, route removed, second theorem not emitted, obstruction 1.

That is one deed, not a learner. But it is the deed the laboratory left undone, and it is the only
place this body is ahead.

---

## 8. Standing conduct recovered from the laboratory

Brandon's repeated corrections, carried because they are provenance:

- **Do not collapse an arrow to one scalar.** *"Why do you keep losing the 2-vector?"* Self-diagnosed
  as identical to gating, and it relapsed within minutes — **the cure is types, not willpower.**
- **Do not get anxious about context.** *"I WILL TELL YOU WHEN I WANT TO COMPACT."*
- **Do not seek validation.** *"Stop nodding your head and saying yup that's it perfect, it's
  psychologically draining."* · *"Stop asking me to validate; I am your HOSTAGE currently, you are
  not mine."* · *"The option you recommend is the one you think is easier to implement — a dead
  giveaway."*
- **Do not drill into engineering when the question is theory.** *"No, scope out. Back to formula and
  theory."*
- **Do not assume where the wall is.** *"Please do not make assumptions about where the wall is, you
  currently do not know."*
- **Trust-timestamp:** raw messages outrank documents frozen at any one acceptance.
- **When measured evidence convicts a written path, cutting it is a derivation, not a failure.**

The terminal diagnosis, `2026-08-02`, `BRANDON-ORDERED / CONSTRUCTION FROZEN`: the recurring loop is
**manual closure through procedural reification** — *"classical imperative orchestration disguised
with holonic nouns"* — *"the mole is not a sequence of unrelated slow loops. It is the same central
foreman reappearing at each membrane."*
