# Compression is a codec pivot, the invariance is additive, and nothing in this tree prices both axes

**Date:** 2026-08-14
**Genre:** research record
**Truth status:** `proved-standard` for every cited classical theorem; `interpretation` for the
holonic typing; one clause **refuted** and one **corrected in place**, both named below.
**Occasion:** Brandon supplied an ontology of compression and asked directly whether it is a
standard way of thinking. It is, substantially — and the two places it is not standard are the two
places it is *sharper*, while one clause overreaches and one sentence the assistant said in reply
was wrong in its exact form.

---

## 0. The provenance, and what was already owned

**Brandon, 2026-08-14, verbatim** (received this session; the operating contract permits the
receiving session to deposit it):

> *the compressing codec provides a function that returns the information in its prior codec where
> the chart it occupies requires a lesser quantity of bits to be represented on disk*

> *geometrically you could refer to volume or area and suppose that the compressed output would be
> a shape in the same chart with the same basis, where the limit of compression is in the
> orthonormalization of the basis vectors constituting that shape; this is linear scaling because
> the chart is invariant, it does not really mean much on its own, this only exposes a factor that
> scales the object linearly*

> *the cost to both compress and decompress is where the bits that we are saving the disk from
> baring is paid for by the runtime of the encoding & decoding algorithms; this is exactly like
> relativity and the speed of light*

> *in order to compress an object we have to pivot between codecs, because there is no form of
> information that is not innately encoded by some codec*

> *there are infinitely many distributions of compression patterns and the complexity is
> combinatorial*

> *This is what machine learning fundamentally is, it is the encoding of function distributions;
> transformers are just layered transport functions, and training just aggregates transport
> mechanisms between recurring and selected (weighted) bits of information. This is the reason we
> say "compression is intelligence".*

**The framing "we lack the holonic definition" is not accurate to the tree, and saying so is the
first obligation of this record.** Three owners already state it:

| owner | what it already says |
|---|---|
| `papers/source/holonics/computation-information.typ:232` — `H.0410`, `proved-standard` | Kolmogorov complexity **and the invariance theorem**, with the transformations field reading *"Description length is receiver-relative to a universal interpreter class; **invariance is additive, not identity of programs**"* and the boundary *"`K` is uncomputable in general and does not retain execution path, runtime, meaning, or causal provenance."* |
| `papers/source/holonics/computation-information.typ:521-534` — `H.0420` | The three species — rebase (**zero** remainder), condensation (**certified**), compression (**collapsed population, family-relative**) — plus recovery as purchase from `image ⊕ channel`. |
| `canon/THE_RECOVERED_LAW.md:170` | Brandon's own earlier hypothesis: *compression is gauge-fixing the flat directions and keeping the curvature; information is the gauge-invariant difference between entities, and the chart is arbitrary.* Corollary: **an absolute volume is the gauge violation** — every measure must be a ratio against a declared null so the Jacobian cancels. |

What is genuinely absent is **the cost**, and section 6 states it exactly.

---

## 1. The correction to what the assistant said in reply, and it is not cosmetic

In conversation the assistant said: *the decoder is the declared null, so `|encoded| + |decoder|` is
the gauge-invariant form, and that is why `K` is defined relative to a universal machine.*

**The second half is right and the first half has the wrong exchange law.** The gauge corollary
demands a **ratio** against a declared null so a Jacobian *cancels* — a multiplicative
normalisation. The invariance theorem gives an **additive** constant:

```text
K_U(x) ≤ K_V(x) + c_{U,V}          c_{U,V} = |the compiler from V to U|, independent of x
```

so `K_U(x) − K_V(x)` is the bounded quantity and `K_U(x) / K_V(x)` is **not** the invariant. For
description length the meaningful comparison is a **difference against a declared machine**, and the
**ratio** — which is what every compression benchmark in the world reports — is the frame-dependent
quantity. `H.0410`'s transformations field already carries the correct sentence and it is the one to
carry forward.

**Two further breaks in the gauge reading, both real:**

- **The universal machines do not form a group.** They form a **groupoid with an additive cocycle**:
  transitions are compilers and composition adds lengths. No continuum, no connection, no curvature,
  therefore nothing corresponding to holonomy. *"No absolute reference frame"* is a correct
  structural analogy; the exchange law and the symmetry type are both different.
- **The gauge freedom is not a small residual.** For **any** target `x` there is a universal `U` with
  `K_U(x) ≤ 1`. Declaring a null is not sufficient — the **machine** must be declared, and the theory
  has content only asymptotically in `|x|`.

---

## 2. The clauses that are standard, with their names

**"Any algorithmic implementation of π takes less byte-space than N digits."** Kolmogorov
complexity, and exactly:

```text
K(π_{1:n}) ≤ K(n) + O(1) ≤ log₂ n + 2 log₂ log₂ n + O(1)
```

**One word is refuted: "objectively."** The claim is asymptotic. Below a crossover the digits are
shorter than the program, and **the crossover is machine-dependent** — which is precisely the
quantity the invariance theorem exists to price. The correct phrasing is *asymptotically, up to a
machine constant*. Note also `O(log n)` is not `Θ(log n)`: at `n = 2^k`, `K(n) = O(log log n)`, so
the bound dips infinitely often.

**"There is no form of information not innately encoded by some codec."** Two claims run together
and only one is the theorem. *Description length exists only relative to a decoder* is the
**definition** `K_U`. *The choice of decoder costs a bounded additive constant* is the **invariance
theorem**. The theorem is uniform in `x` for a fixed pair and **unbounded over the choice of
machine** — so it does not say the codec does not matter; it says the disagreement does not grow
with the object.

**"ML is the encoding of function distributions."** This is the tightest theorem in the whole
statement, and it is an identity rather than an analogy. **Kraft** (1949) / **McMillan** (1956) make
`{code length functions} ↔ {sub-probability distributions}` a bijection up to one bit, via
`ℓ(x) = ⌈−log₂ q(x)⌉`. With Shannon source coding, `E_p[ℓ_q] − E_p[ℓ_p] = D_KL(p‖q)`:

> **Minimizing expected cross-entropy IS minimizing expected description length, exactly, with the
> excess equal to the KL divergence.**

Arithmetic coding (Rissanen 1976; Witten–Neal–Cleary 1987) realises it constructively with ≤2 bits
of total overhead, which is why the identity is practically tight and not merely asymptotic.

---

## 3. The orthonormalization ceiling: right conclusion, wrong reason, four unstated hypotheses

The limit named is the **Karhunen–Loève transform** (Karhunen 1947, Loève 1948; Hotelling 1933),
with the deterministic twin **Eckart–Young** (1936) / **Mirsky** (1960).

**Four hypotheses the statement does not carry, and the theorem does not survive without them:**

1. **Squared-error distortion.** The eigenvector is the stationary point of a *quadratic* form.
   Under a non-quadratic distortion the theorem does not weaken — it stops type-checking, because
   the optimum stops being an eigenproblem.
2. **The map is linear.** KLT is optimal among **linear** transforms only. A helix in `ℝ³` has
   full-rank covariance and one intrinsic degree of freedom: the KLT saves nothing and a nonlinear
   chart saves everything. **This is the direct counterexample to "the limit of compression is the
   orthonormalization of the basis vectors."**
3. **Second-order statistics only.** KLT **decorrelates**; independence follows only under
   Gaussianity. ICA exists because of that gap.
4. **Truncation, or high-rate Gaussian transform coding.** For actual transform *coding* — quantize
   then entropy code — with non-Gaussian sources the KLT is **provably not optimal**: Effros, Feng &
   Zeger, *Suboptimality of the Karhunen–Loève Transform for Transform Coding*, IEEE Trans. Inform.
   Theory **50**(8):1605–1619, 2004. The penalty for a worst KLT can be **arbitrarily large**, and
   with repeated eigenvalues there are many KLTs whose coding performance differs arbitrarily.

**"Linear scaling because the chart is invariant" reaches the right conclusion by the wrong
mechanism.** The KLT *is* a chart change — an orthogonal one — so chart-invariance cannot be what
bounds it. The bound comes from the **structure group**: the transform is restricted to `O(n)` acting
on a fixed vector space, and the invariant it cannot move is the **dimension**. The achievable ratio
is bounded by `n / rank Σ`. *"Linear"* is defensible as *bounded by a constant factor set by the
dimension*; the rate law itself is exponential, `D(R) = σ²·2^{−2R}` for a Gaussian source.

**And the chart-preserving/chart-pivoting split is correct, with a standard name the statement did
not use: the Shannon/Kolmogorov gap** — rate–distortion theory versus algorithmic information
theory. The bridge makes the boundary exact: for a computable source `P`,
`H(X_{1:n}) ≤ E_P[K(x_{1:n})] ≤ H(X_{1:n}) + K(P) + O(1)`. **On average, under a declared source, the
two agree up to `K(P)`; the unbounded gap is visible only on individual objects.**

**π is exactly that object, and it is the canonical textbook exhibit of the very gap the statement is
groping for.** `K(π_{1:n}) = O(log n)` as an individual string; as an ensemble, π is conjectured
normal, so every finite-order statistical model returns entropy rate ≈ `log₂ 10` bits per digit.
Choosing π to make this point is choosing the standard example without naming it, which is evidence
the reading is tracking the real structure.

---

## 4. The relativity clause overreaches, and this project's own standing bar fires on it

**A standard object exists and prices exactly the trade named — Levin (1973):**

```text
Kt_U(x) = min_p { |p| + log₂ t(p) : U(p) = x within t(p) steps }
```

`Kt` has its **own invariance theorem** and, unlike `K`, is **computable**. Two nearer relatives:
**Bennett's logical depth** (1988), whose *slow-growth law* says deep objects cannot be quickly
produced from shallow ones — literally "buying bits with time," as a theorem; and **computational
depth** `depth^t(x) = K^t(x) − K(x)` (Antunes–Fortnow–van Melkebeek–Vinodchandran 2006), whose
monotone curve in `t` *is* the exchange.

**Genuinely shared — three, and the second is not trivial:** two resources with a declared exchange
and one combined functional; **an invariance theorem making that functional machine-independent up
to an additive constant**, which is the real structural rhyme with *all frames agree on the
interval*; and universal search's unavoidable `2^{|p|}·t` overhead.

**Broken — five, and each defeats "exactly":**

1. **The exchange is asymmetric.** `|p|` enters **linearly**, `t` **logarithmically**: one extra
   program bit buys a factor-2 speedup. Minkowski is quadratic in both and symmetric under its group.
2. **No group and no orbit.** Lorentz invariance is exact under a six-parameter Lie group over a
   continuum of frames. `Kt`-invariance is up to an additive constant over a discrete family.
3. **The constant is neither small nor universal** — `c_{U,V} = |compiler|`, unbounded over `V`.
4. **There is no `c`.** `K^t → K` monotonically, and by **Blum's speedup theorem** there are
   computable functions with *no fastest program at all*, so the limiting exchange need not be
   attained. `c` being attained-and-unpassable is the entire content of the relativity claim.
5. **`log t` is a declaration, not a law.** Levin chose it so `Kt` is computable; Schmidhuber's Speed
   Prior (2002) chooses differently and gets a different theory. **Nothing in the material fixes the
   exchange rate.**

**And there is no conserved product.** What exists is problem-specific *lower bounds*: Borodin–Cook
and Beame's `T·S = Ω(n²)` for sorting on branching programs; `TS = Ω(n^{3/2}√log n)` for element
distinctness; and for SAT, **R. Ryan Williams** (2007/08) proving SAT ∉ `DTISP(n^c, n^{o(1)})` for
`c < 2cos(π/7) ≈ 1.8019`, with **Buss–Williams** showing `2cos(π/7)` is the ceiling of the
alternation-trading technique itself. These are **floors on a product**, never equalities, never
general.

**The standing bar.** `CLAUDE.md`'s mouth section refuses importing the uncertainty relation *by
resemblance* to a two-resource trade, and records that the last construction promoted into an
*"aperture law"* was withdrawn for exactly that. **This is the same species of move on the same
species of object.** It is graded `interpretation` with the five breaks attached, and the honest
object is *a machine-invariant functional up to an additive constant*, not a conserved quantity.

---

## 5. "Compression is intelligence" — and precisely where the theorem stops

**Theorem tier.** Kraft/Shannon as above. **Solomonoff's dominance theorem** — `M(x) ≥ 2^{−K(μ)}μ(x)`,
hence total KL over all predictions `≤ K(μ)·ln 2` and a bounded total expected squared prediction
error depending only on `K(μ)` (Solomonoff 1978). **MDL** (Rissanen 1978) is a principle whose
attached results are theorems: two-part-code consistency, Barron–Rissanen–Yu 1998 risk bounds,
Shtarkov 1987 NML minimax regret.

**And the sharpest finding in this record: the step from *compression is prediction* to *compression
is intelligence* is exactly the step at which the invariance theorem stops holding.**

**Leike & Hutter, *Bad Universal Priors and Notions of Optimality*, COLT 2015** (PMLR 40;
arXiv:1510.04931): for `K` and Solomonoff induction the invariance theorems hold, but **no invariance
theorem is known for AIXI**; adversarial choice of universal machine makes AIXI misbehave
drastically; Legg–Hutter intelligence and balanced Pareto optimality are *"entirely subjective"*; and
every policy is Pareto optimal in the class of all computable environments.

So the slogan is a **thesis**, and it is the one place where the machine-independence that makes the
whole subject well-posed is *known not to extend*. That is a far more interesting bound than
"unproven," and it is the sentence to carry.

**The 2023–24 empirical results are real, and one of them exhibits this project's own corollary
catching a live defect.** Delétang, Ruoss, Duquenne, Catt, Genewein, Mattern, Grau-Moya, Wenliang,
Aitchison, Orseau, Veness, Hutter, *Language Modeling Is Compression*, **ICLR 2024**
(arXiv:2309.10668): Chinchilla 70B, trained on text, compresses **ImageNet patches to 43.4%** and
**LibriSpeech to 16.4%**, beating **PNG (58.5%)** and **FLAC (30.3%)**.

> **Those ratios exclude the model's parameters.** Quoting 43.4% without the 70B-parameter decoder is
> precisely the absolute-volume error, and the paper itself reports adjusted figures under which the
> advantage largely disappears. **The Hutter Prize already enforces the fix operationally** — the
> submitted size must include the decompressor as an executable.

The gauge corollary is therefore not decorative here: it is a rule that a real competition adopted and
that a 2024 result is commonly quoted in violation of. Also real, and empirical rather than a theorem:
Huang, Zhang, Shan, He, *Compression Represents Intelligence Linearly*, COLM 2024 (arXiv:2404.09937),
31 models across 12 benchmarks, near-linear correlation of downstream score with bits-per-character.

---

## 6. "The complexity is combinatorial" — too weak, and the repair joins his own two clauses

`K` is **uncomputable** (Berry/Chaitin: a computable `K` makes `f(n) =` the first `x` with
`K(x) ≥ n` computable, and the program "run `f` on `n`" has length `≤ log₂ n + c`). The counting
bound gives `#{x ∈ {0,1}ⁿ : K(x) < n − k} < 2^{n−k}` — **fewer than one string in a thousand is
compressible by ten bits.** And **Chaitin's incompleteness** (1974): for any sound effectively
axiomatized `F` there is a constant `L ≈ K(F) + O(1)` such that `F` proves `K(x) > L` for **no** `x`.
Almost every string is incompressible; almost none is *provably* so.

**So "combinatorial" is the wrong word at the level stated.** The obstruction is not that the pattern
space is large — a combinatorial obstruction is a *cost*. It is that the optimum is **uncomputable**
and, beyond a constant, **unprovable**. Likewise *"there is no optimal compressor"* must be split:
for **effective** compressors none is best; for **descriptions up to an additive constant** the
universal machine **is** optimal, and that *is* the invariance theorem. The gap between those two
sentences is exactly the uncomputability.

**And the repair is the join of Brandon's own two clauses, which he stated separately and which are
not two observations:**

> **Bounding the runtime is exactly what converts the uncomputable question into a combinatorial
> one.** `K^t` *is* computable, and its meta-complexity problems are NP-hard or conjecturally so —
> MINKT (Ko 1991), MCSP (open), and **Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*,
> FOCS 2022**, which proves NP-hardness of the partial-function version under randomized reductions,
> overcoming Ko's relativization barrier.

The runtime clause is the **hypothesis** under which the combinatorial clause becomes true. Stated
together they are sharper than either alone, and neither the statement nor the standard exposition
puts them in that order.

---

## 7. Where the framework is genuinely sharper than the standard — two places, both real

1. **The three-species table beats "lossless/lossy."** Rebase and family-relative compression have
   standard homes — invertible transform coding, and rate–distortion at zero distortion within the
   family. **The middle term has no standard single name**: condensation-with-a-certified-remainder
   is scattered across fast-multipole-with-error-bound, sketching-with-a-guarantee, certified model
   reduction, and the Schur complement. Naming it one species is a typing gain, not a relabelling.

2. **The remainder is a witness, not a number.** Rate–distortion returns `D`, a scalar.
   `crates/holonic-engine/src/receiver_exact_compression.rs:138` returns the collapsed pairs, each
   carrying the **shortest input word that separates it** (`exhibit_collapsed`, `:316`, breadth
   first) and the receiver that saw the difference. The object has a standard name — a distinguishing
   sequence, Moore 1956 — and a standard cost, but **no compression theory reports it**, and
   requiring the remainder to be *exhibited* rather than *bounded* is strictly stronger than anything
   in the standard treatment. The module's header at `:21-29` already disowns the file-size reading:
   compression here is *"not synonymous with fewer bytes, deduplication, averaging, or a scalar
   quotient."*

---

## 8. What is measured absent, and the one buildable joint

**Measured by reading the operations, not the names** (`--include='*.rs' crates/ soma/`, zero hits
each): `kraft`, `huffman`, `arithmetic cod`, `lempel`, `lz77`, `lzw`, `prefix.free`,
`rate.distortion`, `kolmogorov`, `solomonoff`, `minimum description`, `karhunen`; and separately
`compressed_size|original_size|compression_ratio`. **There is no codec and no
compressed-versus-original comparison anywhere in the tree** — which, given the gauge corollary, is
the correct state rather than a gap.

**Three owners do price cost, and they were found by reading:**

| owner | what it prices |
|---|---|
| `crates/holonic-engine/src/interchange.rs:1480` `order_price_bits` | `⌈log₂(n!)⌉` exactly over `BigUint` — `.bits()` with a power-of-two correction at `:1489-1493`, no float, no Stirling. **`overpayment()` at `:1516` returns the bits paid when the declared receiver family provably has no distinguishing word for two orders — bits paid that buy nothing.** The only place in the tree where a paid encoding budget is compared against value received. Driver: `examples/the_order_has_a_price.rs`. |
| `crates/holonic-engine/src/surprisal.rs:157` | `S(p) = −log₂ p` as a **ℚ-linear form in `log₂` of the primes, never evaluated**; `cross_entropy(P,Q)` at `:418` is **exactly expected code length under a mismatched code**, computed symbolically and float-free; `Support::Unsupported` at `:400` refuses to smooth a zero-support event. |
| `crates/holonic-engine/src/cuda_aperture.rs:1067` `CarrierWork` | `host_evaluations`, `device_evaluations`, `transfer_bytes`, `intermediate_bits`, all `BigUint`, ordered by a **partial** product order returning `Open` rather than tie-breaking. |

**The precise absence: the tree prices the remainder exactly and prices work exactly, and has never
priced the two together on one object.** There is no `Kt`-shaped return anywhere — nothing computes
a description length and a runtime for the same construction and refuses to collapse them.

**And the joint is one declaration away, in this project's own vocabulary.**
`cuda_aperture.rs:1113-1114` already states the obstruction verbatim: *"a host evaluation and a
device evaluation are different units, and nothing in the material says how many of one buys one of
the other."* **That is precisely what Levin closes by *declaring* `log t`** — a receiver declaration,
which this framework is entitled to make explicitly or to refuse. Every piece stands:
`surprisal::cross_entropy` is the bit axis, `CarrierWork` the work axis, `ExactOrdering::Open` the
correct refusal when the two do not order, and `DeclaredCarrierMetric::cost_of` (`:1166`) already the
right shape for a declared exchange. **No new organ is required.**

---

## What this record does not claim

No new mathematics; every classical result is cited to be composed with. It does not claim the tree
implements Kolmogorov complexity, a codec, or `Kt` — `blueprint/THE_ROADMAP.md:3221` already records
`H.0410` as registered and unimplemented. It does not claim compression is intelligence, and it
records the exact theorem showing where that step loses its machine-independence. It schedules
nothing.
