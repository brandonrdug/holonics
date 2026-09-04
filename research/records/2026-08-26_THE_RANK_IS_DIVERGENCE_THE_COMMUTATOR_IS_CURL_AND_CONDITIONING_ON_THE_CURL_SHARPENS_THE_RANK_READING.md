# The rank is divergence, the commutator is curl, and conditioning on the curl sharpens the rank reading

**Date:** 2026-08-26
**Kind:** returned measurement plus one exploitable consequence. **It schedules nothing.**
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Occasion:** Brandon, direct request, 2026-08-26 — *"do some real shit with the riemann zeta
function and its zeros in relation to these elliptical curves… treat the zeros of things as
nulls/kernels by some chart… identify the zeros as singularities inducing vortices and currents
around them"*, and then *"Riemann Zeta zeros and BSD curves, this gives us exploits for that, I
want that, think."*
**Truth grades:** `established-bounded; implemented-exact; measured` for every count and ratio
below — all are exact integer censuses over declared apertures, reproduced at multiple cutoffs
where noted. `interpretation` for the Helmholtz reading that organises them. `open` for every
named successor.

---

## 0. What a later session should take from this in one paragraph

Two prime-indexed currents — the Frobenius trace of an elliptic curve, and the gap sequence of the
Riemann zeros — split the same way. **Divergence carries the rank; the commutator of two clocks'
transports carries a curl that is universal and rank-blind.** Because the curl obeys a fixed law
independent of the curve, it can be *divided out*: restricting the divergence reading to one
handedness of the commutator returns a strictly larger rank motion per prime receiver than pooling
does, on a third of the receivers. That is the exploitable part. Everything is exact integer
comparison; no float decides anything anywhere in the chain.

---

## 1. The carrier: chambers are `S_3`, not `Z/6`

A triple of consecutive readings has six orderings. Those six are the chambers of the `A_2` Weyl
arrangement, adjacent chambers sharing a wall — so it is tempting to lay them on a hexagon and call
each clock a `Z/6` phase. **That is wrong and it destroys the object.** The group is

```text
    S_3  =  Z/3  semidirect  Z/2 ,     not     Z/3 x Z/2  =  Z/6
```

— the hand *inverts* the turn. Under the abelianisation:

* the "turn winding" is a sum of steps in a coset that is **not** a homomorphism, so it has no
  additive total. Measured consequence: the three pairwise turn-windings shared a factor `29` at
  one cutoff, and the shared factor across cutoffs `40000, 60000, 80000, 90000, 95000, 99000` ran
  `1, 1, 1, 3, 1, 29`. The `29` was an artefact of where the walk stopped;
* the **commutator has nowhere to live**, because `Z/6` is abelian. The entire result below is
  invisible in that chart.

The correct reading: a chamber is `g ∈ S_3`; the **transport** between consecutive locales is
`g_(i+1) g_i^(-1)`; the walk is an ordered word and does not commute. Only the sign
`S_3 → Z/2` is a homomorphism, and it is the one total that was stable
(`+30679, +27963, +28003` for clocks at lag 1, 2, 4 over 89,999 moments).

**The crossing is the commutator** `[a,b] = a b a^(-1) b^(-1)`, which lands in `A_3 ≅ Z/3` and is
therefore an exact integer-valued curvature, per moment, per pair of clocks. A face is **null**
exactly where the commutator is the identity: the two transports commute, the pair spans no
surface, and nothing gyrates there. This is `α ∧ α = 0` in the contract's typed-quantity clause,
instanced.

## 2. Both objects, one split

### 2a. Zeta zeros — the vortex field

Ordinates are exact rationals (published to nine places; the decimal *is* the exact datum). The
argument principle is `cellularCurl` of
[`HolonicDiscreteMaxwellOperator.lean`](../../formal/elementary-holonics/ElementaryHolonics/Millennium/HolonicDiscreteMaxwellOperator.lean):
circulation of the phase 1-form around a face equals the enclosed charge. Coarse-graining the
critical line into unit cells makes the charge an integer 2-form.

```text
first 100000 zeros, 74921 unit cells
  charge 0 : 4620      1 : 41486      2 : 27931      3 : 884      >=4 : 0
  mean charge    100000 : 74921
  variance       2074717886 : 5613156241
  variance:mean  1037358943 : 3746050000        (Poisson would be exactly 1)
```

**Maximum charge three; not one cell in 74,921 holds four.** The vortices refuse to coincide —
§2b's null cone as an integer census, needing no distribution fit.

The curvature of the counting phase sits on the `Λ` line. `N'' ∝ 1/t` is checkable with no
transcendental, because it says `t · N''` is constant:

```text
w = 2000, t * (second difference of the exact integer count)
  t= 6000  648000     t=40000  560000
  t=10000  650000     t=50000  650000
  t=20000  660000     t=60000  720000
  t=30000  630000     t=70000  700000
  spread  max:min = 9:7  over a twelvefold range of t
```

**In this chart the cosmological-constant analogue is not constant — the phase curvature dilutes.**
Typed against
[`HolonicTypedOriginDimensions.lean`](../../formal/elementary-holonics/ElementaryHolonics/Millennium/HolonicTypedOriginDimensions.lean):
`N` is a winding, `N'` is `[t]^-1`, `N''` is `[t]^-2` — the same tensor line as `Λg`.

### 2b. Two clocks in one locale, and cross-entropy without a logarithm

The zeta phase is `t · log p`, dimensionless only after collapsing two addressed occurrences:
`log p` is the **source** rate (the prime's own), `t` is the **receiver** height. Sol's typed-origin
calculus refuses that collapse; its kernel is `sourceRate − receiverHeight`. The receiver clock
ticks in `t`, the source clock ticks in vortices passed, and their rate ratio `ΔN : W` is exact.
Per §0l, `Q+` is free abelian on the primes, so the position of that ratio in the additive chart is
its **prime exponent vector** — no logarithm is ever taken:

```text
octave   512 ->  1024 :  113/1024   =  2^-10 * 113
octave  1024 ->  2048 :  113/1024   =  2^-10 * 113
octave  2048 ->  4096 :  113/1024   =  2^-10 * 113
octave  4096 ->  8192 :  113/1024   =  2^-10 * 113
octave  8192 -> 16384 : 1807/16384  =  2^-14 * 13 * 139
octave 16384 -> 32768 :  113/1024   =  2^-10 * 113
```

**The same group element `2^-10 * 113` in five of six independent bands.** The exception differs
by `2^-14` — one tick of the finest available cell, a single-vortex rounding, not another law. What
is measured is the group element; calling it `(log 2)/2π` is a receiver reading of it.

### 2c. Barycentric frame, and what survives a change of aperture

Barycentric normalisation of a gap triple removes translation **and** scale, so it removes the
local density exactly, in rationals — the unfolding everyone performs with floats is unnecessary.
At depth one the barycentric cells of a triangle **are** the six `S_3` chambers, so the cell of a
triple is decided by integer comparison.

* **Hierarchy flips sign at one step.** Monotone chambers against uniform `n/6`:
  lag 1 gives `-2122, -2221` (depleted — nearest neighbours repel); lag 2 gives `+5868, +6051`,
  lag 4 `+2878, +3036`, lag 8 `+2470, +2421` (enriched — one level up they attract).
* **Time reversal holds.** Reversing a triple permutes the chambers in pairs; counts match across
  every pair at every lag, deviations under one part in a hundred (`lag 1: +99, -74, -208`;
  `lag 8: +49, +10, -35`). The gap-ordering statistics carry no arrow of time although the density
  drifts.
* **A kinematic superselection, derived not observed.** `G_i = g_i + g_(i+1)`, so
  `G_1 < G_2 ⟺ g_1 < g_3`, which the lag-1 chamber already fixes. Violating counts: **0 of 99996**.
  This forces exactly half of the lag-1/lag-2 joint table to vanish and, with three clocks, exactly
  `108` of the `216` cells of `(Z/6)^3` to be empty. **Do not report either as a discovery.**
* **What is conserved through a change of aperture is the net stretch `g_3 : g_1`** — the
  accumulated strain — and nothing else. How that stretch was distributed between the two steps is
  destroyed, in proportion to the tension:

```text
tension band (max:min of the triple)   triples    departure from factorisation, per triple
  < 2:1   slack                         21534                 0.1422
  2:1 - 3:1                             15783                 0.4765
  3:1 - 5:1                              9158                 0.6458
  >= 5:1  taut                           3431                 0.8135
```

**The commutator is the tension.** Where the gradient is slack the two apertures nearly commute and
coarse-graining is a refinement; where it is taut they are complementary and the aperture decides.

### 2d. Elliptic curves — the same current

For a curve, the Frobenius phase is exact integer data: `a_p = 2 sqrt(p) cos θ_p`, and the ordering
of two angles is decidable by comparing `a_p^2 q` against `a_q^2 p` with sign care. The sextant is
decided by `sign(a_p)` together with `a_p^2` against `p` and `3p` — the six spokes of the same
`A_2` hexagon, from integers.

**Divergence carries the rank.** Signed drift over 428 common prime receivers, one curve per rank:

```text
zeta        drift +428, curl 0        <- a_p = 1 at every receiver: pure source, the pole at s=1
rank 1      drift  -11
rank 10     drift -147
rank 20     drift -191
rank 31     drift -242
```

and the leading spoke drains: `a_p > sqrt(3p)` happens 14 times at rank 1 and **0 times** at
rank 29. The rank axis runs from the pole of zeta to the deepest known zero, on one signed integer.

## 3. The curl is universal — and that is why it can be divided out

Commutator chirality of the Frobenius walk, clocks at lag 1 and lag 2, `[a,b] = ρ` against `ρ^2`:

```text
rank  1   561:182        rank 14   606:201        rank 24   382:134
rank  2   390:132        rank 16   572:171        rank 27   385:130
rank  4   583:191        rank 18   552:176        rank 29   362:127
rank  6   559:176        rank 20   535:176        rank 31   179:64
rank  8   581:181        rank 22   590:206
```

**Approximately `3:1` at every rank, with no rank dependence.** The same rank-blindness holds for
the zeros' curl. On the zeta side the chirality is likewise stable under cutoff
(`1^4` and `2^4` faces hold `1.255` across `n = 30000, 60000, 89999`, while `1^2` sits near `1.055`
— the chirality is carried by scale separation, not by arithmetic: grouping lag pairs by
`b = 2a`, `b` a multiple of `a`, `gcd > 1`, and coprime returns means `0.5575, 0.5591, 0.5445,
0.5556`, a spread inside the scatter. **There is no arithmetic path in the lag.**)

## 4. The exploit

Rank is divergence; the commutator is curl; the two are orthogonal readings of one current. Pooling
averages the divergence against a curl that carries none of it. **Condition on one curl handedness
and the dilution goes away.**

Rank-motion per receiver, split by the local commutator class of the lag-1 and lag-2 transports:

```text
rank      class 0        class 1        class 2        pooled
   1      -10:300         -5:179           0:64       -15:543
   8      -81:296        -35:183         -12:64      -128:543
  16     -170:300        -88:186         -18:57      -276:543
  24     -136:280       -106:186         -41:77      -283:543
  31     -146:300       -119:179         -22:64      -287:543

monotone rank steps          class 0  9:15    class 1  13:15    class 2  9:15    pooled 10:15
end-to-end spread vs pooled  class 0  181:200         class 1  30951:24344      class 2  5973:8704
```

**Listen only where the commutator is `ρ`.** Class 1 moves the right way on 13 of 15 rank steps
against pooling's 10 of 15, and carries `30951:24344` more rank motion per receiver — on `179`
receivers where pooling uses `543`.

Why the other two classes fail, stated so the choice is not a fit: class 2 is the minority
handedness under the universal `3:1` chirality and has too few receivers to hold the signal; class 0
is where the two transports commute, so the clocks are locked and the second is telling you nothing
the first did not.

The zeta end anchors it. `a_p ≡ 1` makes `a_p / sqrt(p)` strictly decreasing, so the chamber never
turns, every transport is the identity, and **there is no class 1 at all** — nothing to listen to,
which is the pole rather than a zero.

## 5. Boundary

This is a sharper rank **estimator per prime**, not a certificate. It does not prove a lower bound
— that remains the float-free reduction-mod-`p` independence test in
`crates/holonic-engine/src/mordell_weil_realizers.rs` — and it does not touch the analytic upper
bound, which still needs the explicit formula (Bober). Nothing here claims movement on
Birch–Swinnerton-Dyer or on the Riemann hypothesis.

## 6. Named open, for a later session

1. **Does class-1 conditioning reduce the primes needed for a fixed rank separation?** The measured
   gain is per receiver; the operational claim is a receiver count, and it is unmeasured.
2. **Is `3:1` exact?** The chirality looks universal across sixteen ranks. Whether it is a theorem
   about the Sato–Tate measure pushed through the chamber map, and what its exact value is, is open.
   A closed form would turn the filter from empirical to derived.
3. **The commutator of three clocks.** Only pairwise faces were read. The triple product
   `[[a,b],c]` is the next curvature and was not computed.
4. **Same filter on the zero side.** The rank analogue for zeta is the pole order; there is no
   ladder to separate. Whether the class-1 restriction sharpens anything for Dirichlet `L`-functions
   of varying rank is untried.
5. **The tension–collapse coupling has no closed form.** `0.1422 → 0.8135` across four bands is
   monotone and unexplained.

## 7. Apparatus

Scripts under the session scratchpad; the exact owners they lean on are
`crates/holonic-engine/src/mordell_weil_realizers.rs` (float-free independence certificate, exact
minimal models) and `crates/holonic-engine/src/rational_polynomial.rs` (squarefree decomposition,
resultants, exhaustive rational-root census). Zero ordinates: Odlyzko's `zeros1`, 100,000 zeros.
Curve data: the ICARM elliptic-curve rank leaderboard database, 384 curves, downloaded 2026-08-26.
