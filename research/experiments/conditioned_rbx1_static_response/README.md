# The conditioned RBX1 static response returns its null fibre, its refusals and its sign

[historical] Further runs of this application are deferred by the latest post-Wave-10 request.
The [library audit](../../records/2026-09-20_WAVE_TEN_IS_REPAIRED_AND_THE_LIBRARY_RETURNS_TO_HELICAL_GENERATORS_AND_HNN.md)
retains these measurements and repairs the generic response owner. In particular, the old
response-family reading considered individually compatible input columns; the complete admissible
family is `ker(Z*B)` and can include their combinations. Old family-rank fields below remain
measurements of the earlier implementation, not evidence that the repaired full family was run.

[measured] Dated 2026-09-19, on tree `27c72825`. Issue advanced: **#55**. Contract:
[the conditioned structural response consumer](../../../docs/plans/THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md#the-conditioned-structural-response-consumer).
Counterexample that shaped it: the
[plan audit](../../records/2026-09-19_THE_PLAN_AUDIT_RECONNECTS_SHARED_LAWS_CONSUMERS_AND_HARDWARE.md#verification).

**What this is.** This experiment extends the preceding structural readings with a
**source-conditioned static response**, scored against
measurement already on disk. It is a bounded elastic experiment. It is **not** general structure
prediction, and it is not an admission test for whether a generated response counts as prediction.

**What it returned.** On the N-terminal arm the declared
uniform-compression response is **oriented opposite** to the measured free→bound change against
both bound partners, and its *largest* unoriented overlap with a sibling model of the source NMR
ensemble (`cos² = 0.821`, and the same sign in 19 of 19 models) exceeds its unoriented overlap with
either bound structure (`0.222` against 3DPL, `0.453` against 7Z8R). The declared local elastic
model does not beat the source's own spread on that window. A squared cosine alone would have
scored the compression and its opposite identically, which is the contract's point.

---

## 0. Notation

`|q₀⟩` is the source configuration — one mounted alpha-carbon window of free RBX1. `K` is the
declared stiffness, `Z` a basis of its **full** kernel, `B` the forcing map, `|u⟩` the force family
and `|f⟩ = B|u⟩`. `⟨quadrance|` is the receiver. The general object is the **tube**: the RBX1 chain
carried along its residue index. A **tower** is one instantaneous frame of it — the window's
Jacobian at `q₀`. The passage `free_↗ bound` carries the declared forcing downstream to the bound
environment; its residual is the environment the claim was read at.

---

## 1. What was declared, and it was declared before the comparison structure was opened

The example's source order **is** this order. Sections 1–4 below are fixed and printed before §5
reads a single held-out coordinate.

### 1.1 The source `|q₀⟩`, its correspondence and its environment

| slot | declaration |
|---|---|
| entry | **2LGV**, solution NMR, 20 deposited models, chain `A` |
| why | the only measured RBX1 in the M5 sequence search with **no cullin partner**: a free-state source |
| representative | one **alpha carbon** per residue, exact decimal decoding through `physical_intake::mmcif` |
| correspondence | `label_seq_id + 8 = ` M5 residue index, taken from the M5 experiment's `measured_staging.json` and not re-derived |
| environment | RBX1 alone; 3 `ZN` in the deposition; pH undeclared by the depositor |
| known divergence | 2LGV is the solubilised construct **`W27S, V30S, L32Q, W33S`**. All four sit **inside** the arm window. |

The four substitutions are carried, not smoothed. The receiver reports a scope that includes their
pairs and a scope that excludes them, and both are below.

### 1.2 The elastic energy, its stiffness and its units

```text
E(q) = ½ Σ_c γ_c ( ℓ_c(q) − ℓ_c(q₀) )²,          γ_c = γ₀ > 0,  [γ] = energy / length²
K    = Hess E(q₀) = J* W J,   W = diag( γ_c / (4 ℓ_c²) ),        [W] = energy / length⁴
```

`J` is `rigidity_receiver::RigidityJacobian`, which differentiates the **squared** length
`F_c = |q_i − q_j|² − ℓ_c²`, so `∇F_c = 2 ℓ_c ∇ℓ_c` and the factor `4 ℓ_c²` is exactly what turns
the rigidity differential into the energy Hessian. `ℓ_c²` is the exact rational
`DistanceConstraint::squared_length`, so `W` is exact and `W = W* ⪰ 0`. `K = K*` is **checked entry
by entry** at construction; the returned `self_adjoint_defect` is `0/1` on every window below.

**The reading is declared, never inherited.** `holonic_chain::elastic_chain` builds the same matrix
expression `A = −J*J` as a **dissipation** form with `Ω = 0, G = I`. Reading that expression as a
physical stiffness is a change of physical content. `ElasticDeclaration` carries the energy, the
units and the pairing as data so the change cannot happen silently.

Units: one declared stiffness unit `γ₀` per admitted contact. Every displacement below is
`angstrom · γ₀⁻¹` and every quadrance change is `angstrom² · γ₀⁻¹`. **The overall scale of the
response is the free ratio `|u|/γ₀`, and it is never fitted to the held-out displacement.** The
oriented score below is scale-free by construction; the scale the response *would* need is
reported as `scale_diagnostic_enters_no_score` and enters nothing.

### 1.3 The metric and the gauge

`G = I` on the declared Cartesian coordinate basis — a **declaration**, not an absence of one, and
the pairing in which `K = K*` above holds. The gauge is `Z* G δq = 0`: the representative of the
affine fibre `δq₀ + span Z` that is `G`-orthogonal to the **whole** kernel. It is well posed
exactly when `Z* G Z` is invertible, which is checked, and the returned `gauge_residual` is exactly
zero everywhere below.

### 1.4 The forcing map `B` and the force family `|u⟩`

A contact site is a **support**. It fixes neither a direction nor a magnitude, and the three
provenances are declared separately.

* **Support** — CONDITIONED. Read from the deposited bound frames by
  `stage_partner_contacts.py`: the M5 residues of the window whose alpha carbon lies within a
  declared **10 Å** alpha-carbon aperture of a partner chain. 3DPL gives 39 contact residues
  against cullin-5; 7Z8R gives 45 against CUL1/CAND1. *This is conditioning on the held-out
  entries' contact topology and it is reported as such.* No held-out **displacement** is used.
* **Direction** — from `|q₀⟩` alone. Each generator is a **pinch**: `+(q_j − q_i)` at block `i`
  and its negative at block `j`.
* **Magnitude** — four declared laws per support: `u = +1` uniform compression, `u = −1` uniform
  expansion, alternating by generator index, and a single generator with the rest zero.

[proved-derived] **The pinch is self-equilibrated.** Its net force is `f_i + f_j = 0` and its net
moment about any origin is `(q_i − q_j) × f_i = 0`, so every column is exactly orthogonal to every
translation *and* every rotation generator linearized at `q₀`. This is **checked**, not asserted,
against `TrivialMotionReading::generators`, and it holds on every support below. Compatibility can
therefore fail only against an **internal floppy mode**.

[proved-derived] **A pinch along an existing bar is compatible by theorem, not by measurement.**
When the loaded pair is itself constraint `c`, the column is exactly `−½ J* e_c`, so it lies in
`image J* = (ker J)^⊥ = image K`. A reading that only ever pinches along its own bars has not
tested compatibility at all. Three supports are therefore declared:

| support | what it is |
|---|---|
| `interface_<entry>` | the window's elastic contacts with **both** endpoints at the `<entry>` interface |
| `interior_control_<entry>` | the window's elastic contacts with **neither** endpoint at the interface — same operator, same magnitude law, different support |
| `long_range_interface_<entry>` | pinches between interface residues that are **not** elastic contacts — deliberately off the bars, bounded to four, widest separation first |

---

## 2. The operation

Let the columns of `Z` span the **full** `ker K`, including internal floppy modes. Static
equilibrium requires `Z* f = 0`, and that is tested exactly before anything is solved.

* **compatible** — `K δq = f` is solved through `exact_linear::preimage_fibre`, which returns the
  complete affine fibre and selects nothing. The declared gauge then picks one representative.
  `K δq − f` and `Z* G δq` are both returned and both are exactly zero.
* **incompatible** — the response is **refused**. `(I − P) f`, the part of the forcing no static
  equilibrium answers, is retained, and `preimage_obstruction` returns the covector witnessing it.
  A least-squares projection is a **different receiver**; it exists as
  `StaticResponse::least_squares_projection`, it is labelled on every return, and it is not what
  this experiment reports.

---

## 3. The receiver

Oriented pairwise-**quadrance** changes. `Q_ij = |q_i − q_j|²` is invariant under every rigid
motion of space, so the comparison needs no superposition and inherits none — checked by a test
that translates and rotates a configuration and gets exactly zero change.

| reading | expression |
|---|---|
| predicted, linearized | `2⟨q_i − q_j, δq_i − δq_j⟩` |
| dropped quadratic term | `\|δq_i − δq_j\|²` |
| predicted, finite | the sum of the two |
| measured | `Q_ij(held-out) − Q_ij(q₀)`, exact |

**Signed agreement is reported, and `cos²` is reported beside it.** `cos² = ⟨p,m⟩²/(‖p‖²‖m‖²)` is
an exact rational; it scores `−p` identically to `p`, so on its own it cannot tell a response from
its opposite. The sign is the exact sign of `⟨p,m⟩`.

Three declared scopes: `all_pairs`; `separation_at_least_3` (the M5 receiver's own minimum — `i,i+1`
and `i,i+2` are inside any protein aperture whatever the fold does); and
`identically_typed_and_separated`, which further drops every pair touching 2LGV's four
substitutions. The tables below quote the **identically typed** scope unless stated.

---

## 4. The windows, and what each one costs

Both established windows were run. A window residue is kept only if it is resolved in **all 20**
2LGV models **and** in 3DPL **and** in 7Z8R.

| window | declared | resolved everywhere | coordinates | contacts at 8 Å | `rank J` | `dim ker K` | trivial | **internal floppy** | status |
|---|---|---|---|---|---|---|---|---|---|
| `n_terminal_arm` | M5 21–38 | **18** | 54 | 36 | 36 | 18 | 6 | **12** | **returned**, 73 s |
| `ring_core` | M5 41–80 | **37** (64–66 excised) | 111 | 156 | 104 | 7 | 6 | **1** | extent only, §6 |

`ker K = ker J` is **verified** by applying `J` to every kernel vector, not argued from `γ_c > 0`.
`dim ker Jᵀ` — the self-stress — is 0 on the arm and 52 on the core, by rank–nullity on the
constraint space.

**Residues 64, 65, 66 are excised and named**: 3DPL does not resolve them. That is the receiver
retaining an unresolved coordinate rather than interpolating one.

**The internal floppy modes are the reason the contract demands the full kernel.** On the arm a
reading that took `Z` to be the six rigid motions of space would be wrong by **12 dimensions** and
would have called every long-range forcing below compatible. On the core it would be wrong by one.

The bounded-window caveat is declared: each window is cut out of the chain, so its boundary
residues lose the contacts their neighbours outside the window would supply. That is a property of
the bounded experiment, not of RBX1.

---

## 5. The N-terminal arm, M5 21–38

Both bound partners contact **every** residue of this window, so `interface_3DPL` and
`interface_7Z8R` are the *same* 36 generators and return identical readings. There is no
`interior_control` here: every arm contact is an interface contact. That is itself the finding that
this window is entirely interface.

### 5.1 The compatible forcings, and their orientation

Identically-typed-and-separated scope, 72 pairs.

| magnitude law | vs **3DPL** sign | `cos²` | vs **7Z8R** sign | `cos²` |
|---|---|---|---|---|
| `u = +1` uniform compression | **−1** | 0.222469 | **−1** | 0.452600 |
| `u = −1` uniform expansion | **+1** | 0.222469 | **+1** | 0.452600 |
| alternating by generator index | −1 | 0.076712 | −1 | 0.193496 |
| single generator, rest zero | −1 | 0.001812 | −1 | 0.011001 |

**Read the two top rows together.** `cos²` is *identical* down the pair, and the sign is the only
thing that separates a compression from an expansion. The measured free→bound change in this window
is oriented with the **expansion** member of the declared family and against the compression
member. A squared cosine would have reported one number for both and called it agreement.

One bit of orientation, selected after the fact from a family that contains both signs, is **not**
a validated prediction, and it is not reported as one here. What the declared family predicted
in advance was a pair `±u`; the measurement chose a member.

### 5.2 The control the response does not beat

| control | reading |
|---|---|
| source NMR ensemble, 19 models against model 1, vs the `u = +1` response | sign **+1 in 19 of 19**; largest `cos²` = **0.821098** |
| the same response vs 3DPL | sign −1, `cos²` = 0.222469 |
| the same response vs 7Z8R | sign −1, `cos²` = 0.452600 |

[measured] **The declared response resembles the source ensemble's own spread more than it
resembles either bound structure, and with the opposite orientation to both.** The ensemble's own
quadrance-change norms (‖ΔQ‖², all pairs, exterior decimals) run from `1.12 × 10⁶` to
`1.83 × 10⁷` against a measured 3DPL change of `7.05 × 10⁶` and a 7Z8R change of `9.22 × 10⁶` — the
free→bound signal on this window is *inside* the ensemble's own range. **This is a negative result
for the declared local elastic model on this window, and it is the result.**

### 5.3 The forcings that are refused, and why that is the honest branch

All four `long_range_interface` forcings — pinches between interface residues that are **not**
elastic contacts — are **incompatible** on both bound supports. `Z* f ≠ 0`, no static equilibrium
of the free window answers them, the retained `(I − P) f` is returned, and
`preimage_obstruction` returns a covector witnessing each refusal. `admissible_generators = 0` of
4 in the bounded family reading.

This is exactly what the arm's **12 internal floppy modes** predict: pulling two unbraced parts of
an open window apart is answered by a mechanism, not by a stress. The projection receiver would
have returned a displacement here. It is a different receiver and it was not used.

### 5.4 The family reading, and the rank that is *not* claimed

| support | generators read | admissible | `force_rank` | `response_rank` | `rank K` |
|---|---|---|---|---|---|
| `interface_3DPL` | 8 (declared bound) | 8 | 8 | **8** | 36 |
| `interface_7Z8R` | 8 | 8 | 8 | **8** | 36 |
| `long_range_interface_*` | 4 | **0** | 0 | 0 | 36 |

The certified statement is about the **operator**: restricted to `{f : Z* f = 0}` the gauge-fixed
response `f ↦ δq` is a linear bijection onto `{δq : Z* G δq = 0}`, so `response_rank = force_rank`
on every admissible family. That is read by solving a whole basis and taking an exact rank. **One
observed displacement cannot produce this number**; it tests membership and residual against the
image and nothing more.

---

## 6. The RING core, M5 41–80 less 64–66 — the extent reached, and its cost

[measured] **The arm window is the certified return. The RING-core window did not return within
1 h 45 m of exact rational elimination on this machine and is reported as an extent, not as a
result.** Its declarations, its network and its null fibre are exactly the ones §4 tabulates —
37 residues, 111 coordinates, 156 contacts, `rank J = 104`, `dim ker K = 7` — and those are read
before any response is solved. What has not returned is the response table.

**Where the cost is — measured on the integrated tree, and it is not where this section first said
it was.** The first reading of this experiment attributed the growth to the elimination, at `N³`.
That is wrong, and the correction is the useful part of this section.

[measured] Once Wave 10's certified prime-image algebra stands under `exact_linear`, the exact
solve of this window is **6–7 ms**, and the whole `StaticResponse::solve` is still **~890 ms**: the
elimination is **0.7 % of the cost** (16 solves, 14,226 ms total, 100 ms of it exact algebra;
`exact_solve_milliseconds` is reported beside `solve_milliseconds` on every response in
`results_n_terminal_arm.json`). A certified rank of the same `K` costs **5 ms**. The algebra is not
the wall here and raising its speed again would return nothing.

[measured] **The width is the wall, and it is downstream of the algebra.** `W = diag(γ_c / (4 ℓ_c²))`
puts one squared length into the denominator of every entry, so `K`'s widest coefficient is
**122 bits** against the Jacobian's **13**. The exact algebra absorbs that — prime charts do not
care how wide an entry is once it is reduced — but everything the solve does *after* it does not:
the gauge fix, the equilibrium application and the two residual checks all run over the wide
rationals the fibre returns, and they are the remaining 99 %. Beyond the solve, the same width is
what makes the receiver expensive: the core window has `C(37,2) = 666` pairs instead of 153, each
forcing scored against 2 held-out structures plus 19 ensemble controls across 3 scopes — `666 × 63`
big-rational multiply-adds per forcing, at a per-operand width the arm never reaches.

The core window is 111 coordinates, so that width grows with it. The elimination's own `N³` factor
of about 8.7 is real and is no longer the term that matters.

**Method and placement for the return, not a promise to wait.** The same invocation with
`--window ring_core` writes the core window's block into `results.json`. The rebase that matters is
the second of the two first listed here, and the measurement above is why:

* **clear a common denominator once per response**, so the gauge fix, the equilibrium application,
  the residual checks and the 666-entry receiver dot products all run over `BigInt` rather than
  over fractions whose every operation renormalizes a 122-bit-and-growing ratio. This is the 99 %.
* batching the declared family into one augmented elimination `[K | f₁ … f_k]` remains correct and
  is still worth doing, but it now buys a share of the 0.7 %, not of the whole.

Both belong to this module and are listed as open obligations rather than claimed. Roadmap rule 12
is what this section obeyed: the run that did not return was stopped and its method reported, and
the report was then corrected by measurement rather than left as the plausible guess it was.

The one structural statement the core window already supports, from its null fibre alone: the
compact domain has **one** internal floppy mode and **52** self-stresses where the arm has **12**
floppy modes and **none**. The RING core braces itself; the arm does not. That is read from
`rank J = 104` on 111 coordinates and 156 constraints by rank–nullity, exactly.

---

## 7. The neck claim is withheld, and the counterexample is recomputed here

`holonic_chain::elastic_chain` builds `A = −J*J` with `G = I`, and `HolonicChain::transfer_at`
takes an ordinary inverse and **refuses a pole**. Rigid motions already make `K` singular — `dim
ker K` is 18 and 7 on the two windows — so `C K⁺ B` is **not** `H(0) = C(−A)⁻¹B` and the off-pole
neck theorem cannot be copied onto it.

`conditioned_static_response::neck_cross_block_counterexample` recomputes the audit's witness over
`ℚ` and the module's own test asserts it:

```text
K = [[1,−1,0,0],[−1,2,−1,0],[0,−1,2,−1],[0,0,−1,1]],   cut {1,2}|{3,4}
K⁺ = (K + 11ᵀ/4)⁻¹ − 11ᵀ/4          (all four Penrose conditions checked, exactly)
stiffness cross block rank = 1      Moore–Penrose cross block [[−3,−1],[−5,−3]]/8, rank = 2
```

Every `bounded_family_reading` in `results_n_terminal_arm.json` therefore returns
`NeckIdentification::WithheldSingularStiffness`. A gauge or a projected force changes the support
the neck theorem sees; deriving the static factorization for the anchored or projected system,
retaining its boundary reaction, is an **open obligation** and is not claimed here.

---

## 8. Results, machine-readable

`results_n_terminal_arm.json` carries every number above: every exact rational as a
`numerator/denominator` string, every exterior decimal rendered from a rational by integer division
and labelled, and every cost in whole milliseconds. It is the output of the single-window
invocation in §10 and it is complete — 4 supports, 16 forcings, **8 typed refusals**, 4 family
readings, 3 receiver scopes and 19 ensemble controls per scope, 0 unreturned readings.

The two-window invocation writes `results.json` with both windows. On this machine it had not
returned at 1 h 45 m; see §6.

**No `f32` and no `f64` exists on any path of this experiment.** `rg -n '\bf32\b|\bf64\b'` over
`conditioned_static_response.rs`, its tests, the example and `stage_partner_contacts.py` returns
nothing.

---

## 9. The intake defect, probed rather than assumed

[measured] Issue **#52 bit.** The example probes it at run time and records what it got:

```text
the structure <M5_STRUCTURE_ROOT>/3DPL.cif is malformed:
label_seq_id "." is not an integer: invalid digit found in string
```

`physical_intake::mmcif::StructurePresentation::parse` requires an integer `label_seq_id` on every
`_atom_site` row, and the deposited 3DPL and 7Z8R files carry `ZN` and `HOH` `HETATM` rows that have
none. The M5 experiment never met this because it staged only the RBX1 chain. A **partner** chain
has to be staged the same way before the library can see it, which is the whole job of
`stage_partner_contacts.py`: it reads only `ATOM` rows, with `fractions.Fraction` over the
depositor's own decimal strings, and constructs no float. The elastic run itself reads the M5
experiment's already-staged single-chain files, which carry no `HETATM` row at all.

---

## 10. Reproducing

```sh
# 1. the bound-partner contact support (exact, no float, routes around #52)
python3 research/experiments/conditioned_rbx1_static_response/stage_partner_contacts.py \
    --root <M5_STRUCTURE_ROOT> \
    --out research/experiments/conditioned_rbx1_static_response/contact_support.json

# 2. the conditioned static response on the certified window (exact, over Q; 73 s)
cargo run --release -p holonic-engine \
    --example the_declared_force_returns_its_null_fibre_and_its_residual -- \
    --structure-root <M5_STRUCTURE_ROOT> \
    --contact-support research/experiments/conditioned_rbx1_static_response/contact_support.json \
    --window n_terminal_arm \
    --out research/experiments/conditioned_rbx1_static_response/results_n_terminal_arm.json

# 3. both windows. See section 6 before running this one: the RING core had not returned
#    at 1 h 45 m on this machine, and --family-bound trades family breadth for cost.
cargo run --release -p holonic-engine \
    --example the_declared_force_returns_its_null_fibre_and_its_residual -- \
    --structure-root <M5_STRUCTURE_ROOT> \
    --contact-support research/experiments/conditioned_rbx1_static_response/contact_support.json \
    --out research/experiments/conditioned_rbx1_static_response/results.json
```

`<M5_STRUCTURE_ROOT>` is the directory the
[M5 experiment](../m5_predicted_vs_reference/README.md) stages its measured structures into: it
must hold `3DPL.cif`, `7Z8R.cif` and the staged single-chain files
`2LGV-A-model{1..20}.cif`, `3DPL-B-model1.cif`, `7Z8R-C-model1.cif`. That experiment documents
`HOLONICS_M5_STRUCTURE_ROOT` and owns the intake route; **nothing here edits it.**

| file | what it is |
|---|---|
| `stage_partner_contacts.py` | the bound-partner contact support, exact, computing no elastic quantity |
| `contact_support.json` | which M5 residues touch a partner in 3DPL and in 7Z8R, with the nearest partner quadrance |
| `results_n_terminal_arm.json` | the certified window's complete output: every declaration, response, refusal, control and cost |

---

## 11. What this does not establish

* It is **not** general structure prediction, and a bounded window is not a fold.
* One observed displacement does not read a response rank. The rank statements above are about the
  operator, read from a declared family.
* The forcing support is conditioned on the held-out entries' contact topology. The *displacement*
  is not used and the scale is not fitted, but the support's provenance is a real dependency.
* The scale `|u|/γ₀` is free. The oriented score is scale-free; a magnitude claim is not made.
* The linearized reading is a first-order model of a finite change, and the two are reported apart.
  The dropped quadratic term is returned per reading.
* 2LGV is a mutant construct measured without a cullin; 3DPL and 7Z8R are different methods in
  different assemblies at different pH. The free→bound comparison carries all three differences and
  none of them is removed.
