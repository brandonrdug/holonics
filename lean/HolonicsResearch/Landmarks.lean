import HolonicsResearch.Landmarks.ZeroPairSite
import HolonicsResearch.Landmarks.IntegralCokernel
import HolonicsResearch.Landmarks.HasseSite
import HolonicsResearch.Landmarks.PrimeCycles
import HolonicsResearch.Landmarks.Sieve

/-!
# Landmarks of the targets: the generic compression law joined to the problem owners

[definition] Rebuild step 3 (#145), "The line" (compression is intelligence is navigation) and the
null-cone record §4–§5. `Holonics.Compression` states the generic law (the face map with its
kernel and cokernel, site kinds, primitive cycles). This root joins it to the owners of the
targets, importing both sides. Each join is an instance of the generic law on the target's own
statements. Site kinds are stated with their determinant sign explicit (positive for a kind,
negative for a reflection, zero for degenerate).

| Module | Join |
|---|---|
| `Landmarks/ZeroPairSite` | RH. The reflected zero pair `(ρ, 1 − ρ̄)` is a site: its advance site has the pair power `(2σ − 1)²` as discriminant, is half the velocity navigator at `β = 2σ − 1` (the strip is the velocity cone's interior), null on the seam and, inside the strip, a boost off it (a reflection outside the closed strip, degenerate on its edges); the Foster tank is the traceless site of determinant `1/(L C)`, lossless exactly when that determinant is a positive real (a rotation at the height). The finite fold: under `heatR` the pair collides into the double root `(z − γ)²` at `t = (2σ − 1)²/8`, which is the polynomial de Bruijn–Newman threshold of the pair. |
| `Landmarks/IntegralCokernel` | BSD and integral Hodge. The ℤ face map: reachable only in a multiple ⇔ nonzero torsion cokernel class. Over ℤ the cocycle test fails; over the field it holds. Kollár classes have a nonzero integral and a zero rational cokernel class. The descent face on `y² = x³ − n²x` is additive with kernel the doubles, so `E →[2] E → (ℚˣ/ℚˣ²)²` is exact, and over `𝔽₂` the field law of `FaceMap` applies verbatim. |
| `Landmarks/HasseSite` | Hasse's bound `a_p² ≤ 4p` from the literal point counts of the congruent-number curves, hence each good local factor is a rotation site splitting through its Weil root. |
| `Landmarks/PrimeCycles` | One cycle machine (a site per primitive cycle, carrying `exp(−s·length)`) gives the return-map transfer determinant at integer lengths and the truncated Euler product at lengths `log p`, tending to `ζ(s)`; no finite return map is `ζ`'s. |
| `Landmarks/Sieve` | The sieve of Eratosthenes as a nested epoch tower of prime digit clocks; the survivors at grain `√N` are the primes in `(√N, N]`, the epoch-one first arrivals of `m ↦ m / minFac m`. |

[open] Owed in #62. The full integral cokernel ledger (a finite-dimensional `𝔽₂` ledger for `E/2E`
needs the weak Mordell–Weil bound of `Millennium/GeneralCollision` carried to the twist family
`FamilyFace.E n = GeneralFace.E n (−n)`); the per-site-clock machine for an L-function
`∏_p (1 − a_p p^(−s) + p^(1−2s))⁻¹` (the two-state sites of `Aeon/Production/Zeta.machine` with
their own clocks); the infinite product of the cycle machine beyond Mathlib's Euler product; and
the tank chart off the real locus, where `ρ′²` is not real and no ordered kind exists.
-/
