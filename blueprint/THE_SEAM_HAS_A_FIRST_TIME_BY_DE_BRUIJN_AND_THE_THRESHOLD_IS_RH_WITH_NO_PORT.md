# The seam has a first time by de Bruijn, and the threshold is RH with no port

**Deposited:** 2026-09-03, on Brandon's direct request ("Proceed with the scoping"), after the
descent-route RT campaign returned `0 ≤ Λ_DN`
([`THE_DESCENT_SIDE_HAS_OFF_SEAM_ZEROS_AT_EVERY_NEGATIVE_TIME_AND_THE_THRESHOLD_IS_NONNEGATIVE.md`](THE_DESCENT_SIDE_HAS_OFF_SEAM_ZEROS_AT_EVERY_NEGATIVE_TIME_AND_THE_THRESHOLD_IS_NONNEGATIVE.md)).  
**Line:** RH, beside the engine frontier; the lines share no owner.  
**Scheduler:** [`THE_ROADMAP.md`](THE_ROADMAP.md) carries the position as `**RH line position:** DBn`.
This contract schedules nothing by itself.

## 0. The target

[definition] After RT6 the RH line holds, on `propext`, `Classical.choice`, `Quot.sound`:
`RiemannHypothesis ↔ 0 ∈ seamTimes` (`RealZeroTimes.zero_mem_iff`); `seamTimes` is a closed
up-set (`LinePreservation.seamTimes_upset`, `RealZeroTimes.isClosed_seamTimes`); and
`seamTimes ⊆ Ici 0` (`DescentZeros.Λ_DN_nonneg`). One port remains: `DeBruijnBound`, that
`½ ∈ seamTimes`. Without a seam time `Λ_DN = sInf ∅ = 0` vacuously, so the port is what makes
`Λ_DN = 0` a statement about `ξ`.

[definition] **The target of this campaign** is the port discharged from the actual kernel:

```text
(1/8 : ℝ) ∈ seamTimes,   hence   DeBruijnBound,   Λ_DN ∈ [0, 1/8],
RiemannHypothesis ↔ Λ_DN = 0      with no port,
```

together with the RH0/RH1 coordinate bridge in Lean, so that the tree's `1/8` is the
literature's `½`. The campaign does not touch `Λ_DN ≤ 0`, which is RH itself and stays the
first exact missing inequality with the conjecture's own falsifier.

## 0b. Critical scoping, source-inspected

[established-bounded; source-inspected] **The source.** N. G. de Bruijn, *The roots of
trigonometric integrals*, Duke Math. J. 17 (1950) 197–226, read in full (the TU/e version of
record). Its §7 proves `Λ ≤ ½` in four steps, none of which is Hadamard factorization, an
extremal pair, or a bound on the zeros of `ζ` beyond the Euler product:

1. **(7.1)–(7.3), the strip.** `Ξ(2z) = ∫ φ(t) e^{izt} dt` with
   `φ(t) = Σ_{n ≥ 1} (2n⁴π² e^{9t/4} − 3n²π e^{5t/4}) e^{−n²π e^{t}}`, even. "It is known from
   Euler's product expansion and from the functional equation `Ξ(z) = Ξ(−z)` that the roots of
   (7.3) lie in the strip `|Im 2z| ≤ ½` anyhow."
2. **Theorem 3 (with Lemma 1), the one-step contraction on polynomials.** For a real polynomial
   `f = A ∏ {(z − a_i)² + Δ_i²} ∏ (z − b_j)` and `λ > 0`, all roots of
   `ξ f(z + iλ) + ξ* f(z − iλ)` (`ξ ≠ 0`) lie in `S`, the real axis together with the discs
   `(x − a_i)² + y² ≤ Δ_i² − λ²` (empty when `Δ_i ≤ λ`). The proof is factorwise: Lemma 1 gives
   `|f(ζ + iλ)| > |f(ζ − iλ)|` for `ζ` in the upper half-plane outside `S`, so `ζ` is no root.
   In particular, roots in `|Im z| ≤ Δ` become roots in `|Im z| ≤ {max(Δ² − λ², 0)}^{½}`; the
   strip form iterates without de Bruijn's ellipses `S_N`.
3. **Theorems 6, 7, 8, the transport to entire functions.** A real entire function of order
   `< 2` with zeros in `|Im z| ≤ Δ` is the locally uniform limit of real polynomials with zeros
   in the strip (Theorem 6, by the genus-`≤ 1` product); the roots of a locally uniform limit lie
   in any closed set containing the roots of the approximants (Theorem 7, Hurwitz); hence
   Theorem 8: for such `f`, the roots of `T^{−Nλ} φ(T^{2λ}) f` lie in `|Im z| ≤ (Δ² − Nλ²)^{½}`
   when `Δ > λ N^{½}` and are real otherwise. Theorem 10 (Pólya) says a kernel `F` with
   `F(t) = (F(−t))*` and `F(t) = O(e^{−|t|^b})`, `b > 2`, has a transform of order `< 2`;
   Theorem 12 is Theorem 8 for the strong universal factors
   `S(t) = ∏_{k=1}^{N} (ξ_k e^{λ_k t} + ξ_k* e^{−λ_k t})`, `|ξ_k| = 1`: the strip shrinks by
   `Σ λ_k²`. With `S(t) = 2 cosh(¼ t)` and `Δ = ¼` this is (7.4): `∫ φ(t) cosh(¼t) e^{izt} dt`
   has real roots only.
4. **Theorem 13, the Gaussian as a limit of strong universal factors.** If the roots of
   `∫ F e^{izt}` lie in `|Im z| ≤ Δ`, the roots of `g(z) = ∫ F(t) e^{½λ²t²} e^{izt} dt` lie in
   `|Im z| ≤ {max(Δ² − λ², 0)}^{½}`: by Theorem 12 the roots of
   `g_N(z) = ∫ F(t) (cosh(λt/N))^{N²} e^{izt} dt` lie in that strip, `(cosh(λt/N))^{N²} → e^{½λ²t²}`
   uniformly on `ℝ` since `cosh y ≤ e^{½y²}` (his (3.9)), and Theorem 7 passes the strip to the
   limit. With `F = φ`, `Δ = λ = ¼`: `∫ φ(t) e^{t²/32} e^{izt} dt` has real roots only; in the
   variable `u = t/4` of Rodgers–Tao this is `H_{½}`, i.e. `Λ ≤ ½`.

[definition] **The same chain in the tree's coordinate.** The tree holds
`ξ(s) = ∫ e^{(s − ½)u} Φ(u) du` with `Φ(u) = e^{u/2} Ψ(e^{2u})` even and positive
(`HeatKernelPhi`, `KernelFlow.T`), and `heatE (−τ) ξ = T_{e^{τu²} Φ}` (`KernelFlow.flow`). The
seam `Re s = ½` is de Bruijn's real axis under `x = −i(s − ½)` (`PolyaLine.seamPoly`), and his
imaginary translation `z ↦ z ± iλ` is the tree's real translation `s ↦ s ± μ`:

```text
A_μ f (s) := ½ (f (s + μ) + f (s − μ)),      A_μ (T_K) = T_{cosh(μu) K}.
```

The four steps become: (1) every zero of `ξ` has `|Re s − ½| < ½`, so `Δ = ½`; (2) one
average shrinks `Δ² ↦ Δ² − μ²` for real seam polynomials; (3) the same for Foster-class members
by finite-product approximants and Hurwitz in a closed strip; hence `A_{1/(2N)}^{N²} ξ` has all
its zeros on the seam, for every `N`; (4) `A_{1/(2N)}^{N²} ξ = T_{cosh(u/(2N))^{N²} Φ} →
T_{e^{u²/8} Φ} = heatE (−1/8) ξ` locally uniformly by dominated convergence, and Hurwitz on the
seam (`HurwitzLine.zeros_on_seam`, already used by `LinePreservation`) gives
`OnSeam (heatE (−1/8) ξ)`, i.e. `1/8 ∈ seamTimes`. The bridge of the 2026-09-02 record,
`H_t(z) = ⅛ · heatE(−t/4, ξ, ½ + iz/2)`, makes `1/8` the literature's `½`; the port as written,
`½ ∈ seamTimes`, follows by the up-set law and is four times weaker than the theorem.

[counterexample; source-inspected] **Why the tree's earlier attempt failed and this one does
not.** The FT4 record withdrew "de Bruijn's bound from `PairDescent`" because a highest pair need
not exist at the entire face. De Bruijn's Theorem 3 has no extremal pair: Lemma 1 is applied to
every quadratic factor at once, and the passage to entire functions is by approximation and
Hurwitz, not by descent on a pair. Nothing in the chain uses the zeros of `ζ` beyond the strip.

[established-bounded; source-inspected] **What the tree already holds, per step.**

| Step | Source | Owner in the tree | Missing |
|---|---|---|---|
| strip of `ξ` | (7.3), Euler product, functional equation | `RiemannXi.riemannXi_eq_zero_iff_riemannZeta_eq_zero`, `riemannXi_one_sub`, `riemannXi_zero_and_one`, `TrivialZeros`, Mathlib's `ζ ≠ 0` on `Re s ≥ 1` (`LSeries/Nonvanishing`) | the one theorem `riemannXi s = 0 → |s.re − ½| < ½` |
| polynomial contraction | Lemma 1, Theorem 3 | `PolyaStep` (conjugate-pair root structure, `nonreal`), `PolyaLine.seamPoly` | Lemma 1 and Theorem 3 on `ℝ[X]` evaluated at complex points |
| approximants | Theorem 6 | `FosterClassProduct.P`, `LineApproximation.approx`, `tendsto_approx` (for `OnSeam f`) | the same for zeros in a closed strip `|Re z − ½| ≤ Δ` |
| Hurwitz in a strip | Theorem 7 | `HurwitzLine.zeros_on_seam`, `no_zero_of_eventually` | the closed-strip form |
| entire transport | Theorem 8 | `FosterClass` (order `3/2 < 2`), growth of translates | the class is closed under `A_μ`; `A_μ f (½) ≠ 0` for the iterates of `ξ` by kernel positivity |
| Gaussian limit | Theorem 13, (3.9) | `KernelFlow` (Gaussian domination after any weight), `EulerIterates` (Tannery pattern), `zeros_on_seam` | `cosh(u/(2N))^{N²} → e^{u²/8}` with the domination `cosh y ≤ e^{y²/2}`, and the locally uniform convergence of the transforms |
| seal | (7.4), §7 | `ThresholdReturn`, `RealZeroTimes.Λ_DN`, `LinePreservation.seamTimes_upset` | `1/8 ∈ seamTimes`, `DeBruijnBound`, the no-port `RiemannHypothesis ↔ Λ_DN = 0` |
| bridge | 2026-09-02 record | `HeatKernelPhi`, `KernelFlow` | `criticalChart`, `Hstd`, `Hstd_eq`, `seamTimes_std = 4 · seamTimes` |

[definition] **Jurisdiction.** The RH line is mathematics on octets in `soma/formal/`; no
Eros/Athena interior is referenced. Every process runs under the 180 s limit with the root
umbrella as the release gate.

## 1. The ordered phases

### DB0 — the manifest and the coordinate

This deposit: the source-exact chain of §0b, the owner table, and the transport to the tree's
coordinate.  
**Pass DB0:** the contract deposited with the position advanced to DB1.  
**Falsifier:** a step of §0b that the source does not contain, or an owner named that does not
hold what the table says.

### DB1 — the strip of `ξ`

`riemannXi s = 0 → |s.re − ½| < ½`, from Mathlib's nonvanishing of `ζ` on `Re s ≥ 1`, the
factorization `ξ = ½ s(s−1) Γ_ℝ(s) ζ(s)`, `ξ(0) = ξ(1) = ½`, and `ξ(1 − s) = ξ(s)`; also
`0 < ξ(σ)` for real `σ` from the positive kernel (`ξ(σ) = ∫ e^{(σ−½)u} Φ(u) du`), so no zero lies
on the real axis. Owner `RH/XiStrip.lean`.  
**Pass DB1:** both theorems formal-checked.  
**Falsifier:** a zero of `ξ` with `Re s ∉ (0, 1)` or a real zero.

### DB2 — the translation average on real polynomials

Lemma 1 and Theorem 3 in the variable `x` of `PolyaLine`: for `q : ℝ[X]`, `q ≠ 0`, with every
complex root in `|Im x| ≤ Δ`, and `λ > 0`, every root of `x ↦ q(x + iλ) + q(x − iλ)` has
`|Im x| ≤ (max(Δ² − λ², 0))^{½}`; the factorization of `q` into real linear and irreducible
quadratic factors, Lemma 1 on each quadratic, and the strict inequality outside `S`. Owner
`RH/TranslationAverage.lean`.  
**Pass DB2:** formal-checked.  
**Falsifier:** a real polynomial, a `Δ`, and a `λ` with a root of the average outside the
shrunken strip.

### DB3 — the transport to the class and the iteration

For a Foster-class member `f` with zeros in `|Re z − ½| ≤ Δ`: the finite products
`f(½) ∏_{i ∈ s} (1 + a i z)` over one member of each pair `{u, 1 − u}` converge to `f` locally
uniformly (`LineApproximation` generalized from the seam to the strip, with `zero_im_ne_zero`
replaced by "no real zero"), each is a seam-type polynomial with zeros in the strip
(`approx_eq_seamPoly` generalized), DB2 applies to each, and Hurwitz in the closed strip
(`HurwitzLine` generalized) passes the shrunken strip to `A_μ f`. Then: the class is closed under
`A_μ` (differentiable, symmetric, growth of order `3/2`), the iterates `A_μ^k ξ` have
`A_μ^k ξ (½) = ∫ e^{μu} cosh(μu)^k Φ(u) du > 0`, and by induction the `N²`-fold average with
`μ = 1/(2N)` has all its zeros on the seam. Owners `RH/StripApproximation.lean`,
`RH/StripHurwitz.lean`, `RH/StripAverage.lean`.

*Returned 2026-09-03:* DB1 (`XiStrip`: the strip and the positive real axis of `ξ`) and DB2
(`TranslationAverage`: Lemma 1 and Theorem 3 in strip form on `ℝ[X]`) passed on the way;
DB3 returned `KernelAverage` (`avg μ T_K = T_{cosh(μu)K}`, positivity and both symmetries),
`LineApproximation` generalized to `NoRealZero`, `ConjIndex` (`mult_conj`, the involution `σ'`,
symmetric finsets), `StripAverage.re_sq_le_of_avg_eq_zero` (Theorem 8 in the tree's coordinate,
proved on the infinite product's symmetric finite sections with the margin of one pair, so no
strip Hurwitz and no strip polynomial approximants were needed; the owner list is corrected),
and `DeBruijnIterate.onSeam_xiIter`: for `N ≥ 1`, `OnSeam ((avg (1/(2N)))^[N²] ξ)`; all on
`propext`, `Classical.choice`, `Quot.sound`; receipt
[`the DB3 record`](../research/records/2026-09-03_DB3_THE_AVERAGE_CONTRACTS_THE_STRIP_OF_EVERY_MEMBER_AND_N_SQUARED_AVERAGES_PUT_THE_ZEROS_OF_XI_ON_THE_SEAM.md).
**DB1, DB2, DB3 pass.**

**Pass DB3:** `OnSeam (A_{1/(2N)}^{N²} ξ)` for every `N ≥ 1`, formal-checked.  
**Falsifier:** an `N` and a zero of the iterate off the seam.

### DB4 — the Gaussian limit

`A_μ^k (T_K) = T_{cosh(μu)^k K}` (kernel calculus), `cosh(u/(2N))^{N²} → e^{u²/8}` pointwise with
`cosh(u/(2N))^{N²} ≤ e^{u²/8}` (de Bruijn's (3.9)), the transforms converge locally uniformly by
dominated convergence against the admissible weight, and `zeros_on_seam` gives
`OnSeam (heatE (−1/8) ξ)`, i.e. `(1/8 : ℝ) ∈ seamTimes`. Owner `RH/DeBruijnLimit.lean`.  
**Pass DB4:** `eighth_mem_seamTimes` formal-checked.  
**Falsifier:** a zero of `heatE (−1/8) ξ` off the seam.

### DB5 — the seal and the bridge

`deBruijnBound : DeBruijnBound` (by the up-set law), `Λ_DN_le_eighth`,
`Λ_DN_mem_Icc : Λ_DN ∈ Icc 0 (1/8)`, and **`riemannHypothesis_iff_Λ_DN_eq : RiemannHypothesis ↔ Λ_DN = 0`**
with no hypothesis; `ThresholdReturn` re-stated with no port. The bridge: `criticalChart z = ½ + iz/2`,
`Φ_std(v) = ½ Φ(2v)`, `Hstd t z = ½ ∫ e^{tv²} Φ_std(v) e^{izv} dv`,
`Hstd_eq : Hstd t z = ⅛ · heatE (−t/4) ξ (criticalChart z)`, `seamTimes_std = (4·) '' seamTimes`,
so `Λ_std = 4 Λ_DN` and the tree's `[0, 1/8]` is the literature's `[0, ½]`. Owners
`RH/DeBruijnSeal.lean`, `RH/CriticalChart.lean`, `RH/ThresholdReturn.lean` amended.  
**Pass DB5:** `#print axioms` on `riemannHypothesis_iff_Λ_DN_eq`, `Λ_DN_mem_Icc`, and `Hstd_eq`
returns the three axioms; root umbrella green under 180 s per owner; records deposited.  
**Falsifier:** any identity of the bridge failing at a point, or a port surviving in the seal.

## 2. Routes not taken, with their reasons

- **de Bruijn's Theorems 1–2** (integrals of `e^{−f(t)}` and `e^{−P(t)} Q(t)`): `φ` is a sum
  of such kernels, not one of them; de Bruijn himself records in §7 that they give "very little"
  toward RH. Not used.
- **Ki–Kim–Lee 2009 (`Λ < ½`)**: adds the simplicity of the zeros of `H_{½}` and asymptotics; a
  strict inequality is not needed for the target. Parked.
- **Polymath 15 (`Λ ≤ 0.22`)**: computer-assisted, rests on numerical verification of RH to
  large height; not needed. Parked.
- **`PairDescent`**: obstructed (FT4 record); superseded by the factorwise Lemma 1.

## 3. Open items and risks, named before construction

- DB3's approximation needs one representative per pair `{u, 1 − u}`; the seam version used
  `Im u ≠ 0`. For the strip the split is by `Im u > 0` against `Im u < 0` after excluding real
  zeros (DB1's positivity for `ξ`; for the iterates, kernel positivity). If the class-level
  statement resists, DB3 may be proved for the iterates of `ξ` only, which is all DB4 needs.
- Hurwitz in a closed strip is a new owner; the seam proof's structure (isolated zero, rectangle
  count) carries over, and the rectangle owners need entire functions, which the iterates are.
- The domination in DB4 is `|cosh(u/(2N))^{N²} Φ(u) e^{(s−½)u}| ≤ e^{u²/8} |Φ(u)| e^{|Re s − ½||u|}`,
  integrable by `KernelFlow`'s admissibility; the locally uniform convergence follows on discs.
- Nothing here bears on `Λ_DN ≤ 0`; the campaign closes with the port discharged and the
  bridge in Lean, and the RH line's next deed is then Brandon's to direct.

## 4. Relation to the standing contracts

The FT contract named the port; the RT contract discharged the other port; this contract
discharges the last one from the actual kernel by the source's own argument. Every theorem
returned here is an unconditional theorem of the tree, graded per claim.
