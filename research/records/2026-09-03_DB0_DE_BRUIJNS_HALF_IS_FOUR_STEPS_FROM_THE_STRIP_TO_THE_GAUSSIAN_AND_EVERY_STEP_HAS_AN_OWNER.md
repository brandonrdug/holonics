# DB0: de Bruijn's half is four steps from the strip to the Gaussian, and every step has an owner

**Date:** 2026-09-03  
**Truth status:** `established-bounded` (a scoping record; no theorem returned)  
**Evidence:** `source-inspected`  
**Campaign:** DB0 under
[`THE_SEAM_HAS_A_FIRST_TIME_BY_DE_BRUIJN_AND_THE_THRESHOLD_IS_RH_WITH_NO_PORT.md`](../../blueprint/THE_SEAM_HAS_A_FIRST_TIME_BY_DE_BRUIJN_AND_THE_THRESHOLD_IS_RH_WITH_NO_PORT.md).  
**Scope:** the manifest; schedules nothing beyond the directed order; the engine frontier is
unchanged.

## The source, read

[established-bounded; source-inspected] N. G. de Bruijn, *The roots of trigonometric integrals*,
Duke Math. J. 17 (1950) 197–226, DOI 10.1215/S0012-7094-50-01720-0, the TU/e version of record,
read in full on 2026-09-03. The paper is under the Taverne licence (personal study; no further
distribution), so it is cited and not copied into the tree.

The proof of `Λ ≤ ½` is §7, (7.1)–(7.4), resting on Lemma 1 and Theorem 3 (the factorwise
one-step contraction on real polynomials), Theorems 6–8 (transport to real entire functions of
order `< 2` by polynomial approximation and Hurwitz), Theorem 10 (Pólya: the transform of an
even kernel with `O(e^{−|t|^b})`, `b > 2`, has order `< 2`), Theorem 12 (the strong universal
factors `∏ (ξ_k e^{λ_k t} + ξ_k* e^{−λ_k t})` shrink the strip by `Σ λ_k²`), and Theorem 13
(`(cosh(λt/N))^{N²} → e^{½λ²t²}` dominated by `e^{½λ²t²}`, then Hurwitz). The only arithmetic
input is that the zeros of `Ξ` lie in the strip `|Im 2z| ≤ ½`, "from Euler's product expansion
and from the functional equation". De Bruijn's Theorems 1–2 (kernels `e^{−f(t)}`) are not on the
route; he records in §7 that they give "very little" toward RH.

## The transport, and the owner table

[definition] In the tree's coordinate the chain is: `ξ = T_Φ` with `Φ` even and positive; the
zeros of `ξ` in `|Re s − ½| < ½`; the real translation average
`A_μ f (s) = ½ (f(s+μ) + f(s−μ))` with `A_μ T_K = T_{cosh(μu) K}`; one average shrinks
`Δ² ↦ Δ² − μ²`; `N²` averages with `μ = 1/(2N)` put every zero on the seam;
`cosh(u/(2N))^{N²} → e^{u²/8}` gives `heatE (−1/8) ξ` with all zeros on the seam; so
`1/8 ∈ seamTimes`, which is the literature's `½` through the bridge
`H_t(z) = ⅛ · heatE(−t/4, ξ, ½ + iz/2)`. The contract's §0b carries the owner table: the strip
(`RiemannXi`, `TrivialZeros`, Mathlib's `ζ ≠ 0` on `Re s ≥ 1`), the polynomial step (`PolyaStep`,
`PolyaLine`), the approximants (`FosterClassProduct`, `LineApproximation`), Hurwitz
(`HurwitzLine`), the class (`FosterClassLandau`), the kernel calculus (`KernelFlow`,
`HeatKernelPhi`), the seal (`ThresholdReturn`, `RealZeroTimes`, `LinePreservation`). The missing
owners are the strip theorem for `ξ`, Lemma 1 and Theorem 3 on `ℝ[X]`, the strip forms of the
approximation and of Hurwitz, the closure of the class under `A_μ`, the Gaussian limit, and the
seal with the bridge.

[counterexample; source-inspected] The FT4 record's obstruction ("a highest pair need not
exist") does not touch this route: Lemma 1 is applied to all quadratic factors at once, and the
entire case is reached by approximation, not by descent on a pair.

## Pass DB0

The contract is deposited with the source-exact chain, the transport, and the owner table;
the position is DB1. **DB0 passes.** Falsifier: a step of the contract's §0b absent from the
source, or an owner named for something it does not hold.

## Boundaries

- No theorem is returned by this record. `DeBruijnBound` remains a port until DB5.
- Nothing here bears on `Λ_DN ≤ 0`.
