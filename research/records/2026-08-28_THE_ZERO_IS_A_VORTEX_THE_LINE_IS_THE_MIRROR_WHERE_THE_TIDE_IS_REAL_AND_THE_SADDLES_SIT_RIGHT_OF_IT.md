# The zero is a vortex, the line is the mirror where the tide is real, and the saddles sit right of it

**Date:** 2026-08-28
**Kind:** the physical reading of the Riemann receiver question, in this framework's species, with
the two measurements that make it checkable — the exact tide and the saddle census — and the
positive form it reduces to. **Schedules nothing.** [`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md)
and [`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Provenance:** Brandon, 2026-08-27, on the winding atlas: *"the winding being the zeros is like
saying 'there's a current that describes the motion between these things' … the whole point is
physical cycles, cross-entropy (literally, different axes of time; parameters). what is the critical
line in that sense, it's like a tide or flow … the zeroes themselves are pinholes, and it's like a
bunch of cones connected to each other funneling water. the critical line isn't a line, it's like a
loop or a spiral, something like a double helix (go for tori, parametrons, lattices, fractals)."*
And: *"take them, I want a physical RH interpretation, that's how we'd solve."* Everything below that
is not his is the assistant's reading and is graded as such. Predecessor:
[`2026-08-27_THE_ZERO_IS_A_WINDING_THE_START_IS_READ_OFF_THE_HEIGHT_AND_THE_SECTIONS_ARE_LIFTED_FROM_ONE_PRIME.md`](2026-08-27_THE_ZERO_IS_A_WINDING_THE_START_IS_READ_OFF_THE_HEIGHT_AND_THE_SECTIONS_ARE_LIFTED_FROM_ONE_PRIME.md).
**Truth grades:** each claim carries its own. Nothing here claims the conjecture.

---

## 1. The winding is a circulation, and the zero is a vortex with a hand

[proved-standard] `log η` is a complex potential. `∮ η'/η ds = ∮ d(log|η|) + i ∮ d(arg η)`: the
real part `log|η|` is the magnitude potential, the imaginary part `arg η` is the phase potential,
and they are conjugate (Cauchy–Riemann). A zero is a **source of the magnitude gradient** and a
**vortex of the phase gradient** at the same point — flux `2π` for one, circulation `2π` for the
other. The winding the atlas certifies is the circulation of the phase current around the box.
Drain or fountain is a hand — the two arms `with_the_turn` / `against_the_turn` retained in every
`WindingReceipt`. A pole would be a vortex of the opposite hand.

[established-bounded; implemented-exact; measured] `η` is entire; every one of the 988 band
windings in `[12, 1000]` is non-negative and their sum is the closure count, 649
(`winding_sum = closures` in every verification). **All the pinholes turn the same way.** The
spiral into each is printed by `verify` as the turn word of the 96-term partial current at the
zero (`turns=+91/−4` at `γ₁`, `+82/−13` at `γ₁₅`).

## 2. The line is the mirror where the tide is real

[proved-standard] On `σ = 1/2`, `ζ(1/2+it) = e^{−iθ(t)} Z(t)` with `Z` real (Hardy) and
`θ(t) = Im log Γ(1/4 + it/2) − (t/2) log π` the tide (Riemann–Siegel). The phase current along
the line is the smooth tide plus a half turn at every zero, the map `t ↦ e^{iθ(t)}` is a helix
over the line, and the zeros are where it crosses the axis. The functional equation supplies the
second helix: `ζ(1−s)` winds oppositely and `ζ(s)/ζ(1−s) = χ(s)` has `χ(1/2+it) = e^{−2iθ(t)}` —
the double helix winds twice as fast as the tide. The zero count is exactly

```text
    N(T) = θ(T)/π + 1 + S(T),        S(T) = (1/π) arg ζ(1/2 + iT)
```

tide plus eddy. The symmetry group of the zero set is `{s, 1−s, s̄, 1−s̄}`: the half-turn about
`1/2` quotients the strip to a **cone** (cone point at `1/2`), the reflection makes the line a
**mirror**. There is no glide, so there is no Klein bottle in the object; a cone with a mirror is.

[established-bounded; implemented-exact; measured] The tide is now exact:
`relational_geometry::riemann_siegel_theta` — Stirling's series at the config's order after a
shift of sixteen, with the remainder disc `|B_{2m+2}| / ((2m+1)(2m+2)|z|^{2m+1}) · 2^{m+1}`
(`sec²(arg z/2) ≤ 2` on the right half-plane), `π` by Machin, arctangent by Euler's series with the
term count taken until the next term is under the grain, principal logarithms. Driver
`crates/relational-geometry/examples/the_tide_is_exact_and_the_eddy_is_the_count_minus_the_tide.rs`
reads the twenty-two verified atlas artifacts and returns `S(T)` as an exact rational interval at
every integer `T ∈ [12, 1000]`: 989 evaluations in 55.7 s; **`max |S(T)| ≤ 0.970`** over the whole
range; `S(100) ∈ [−0.4437, −0.4436]`, `S(999) ∈ [0.3837, 0.3838]`, and `N = θ/π + 1 + S` closes
exactly at every height because `N` is the certified count. Artifact
`output/the_tide_is_exact_and_the_eddy_is_the_count_minus_the_tide/tide.tsv`.

[established-bounded; measured] The band-level ledger of Gram points (half turns of the tide in a
band) against windings: 445 of 988 bands agree, 543 differ — the differences come in matched
pairs (a band with a zero and no half turn, then a band with a half turn and no zero), which is
what Gram's law — zeros and Gram points *alternate* — looks like when read on integer bands
rather than on the merged sequence. The alternation itself, exact, needs the Gram points located
(the tide is monotone, so one bisection each) against the lineage intervals; it is a named next
measurement, not made here.

## 3. Cones connected to each other — the saddles, and Speiser

[proved-standard] The basins of the flow down `log|ζ|` tile the strip, one cone per zero; two
cones meet at a **saddle of the potential**, a zero of `ζ'`. Speiser (1934): **RH holds if and
only if `ζ'` has no zero with `0 < σ < 1/2`** — every saddle lies to the right of the mirror.
Levinson–Montgomery (1974) made it quantitative: the zeros of `ζ'` left of the line and the zeros
of `ζ` off the line are counted together.

[established-bounded; implemented-exact; measured] The jets now carry `ζ''`
(`relational_geometry::ComplexJet2`; the head `Σ log²n · n^{−s}` is the third accumulator of
`kernels/exact_eta_head.cu`), so the same winding law certifies the boundary of `ζ'`, transported
by `ζ''` at every midpoint with a uniform Euler–Maclaurin bound on `ζ'''`
(`zeta_derivative_bound_uniform`). Driver
`crates/holonic-engine/examples/the_saddles_sit_right_of_the_mirror.rs` counts `ζ'` windings per
integer band around `[1/10, 1/2]` and `[1/2, 3]` (`ζ'` has no zero with `σ ≥ 3`, so the right box
holds every saddle on the right); control at `[36,37]`: serial and resident windings agree on both
boxes with identical point counts, the card 7–9× faster.

| range | bands | saddles with 1/10 ≤ σ < 1/2 | saddles with 1/2 ≤ σ ≤ 3 | cumulative right | seconds | artifact bytes |
|---|---|---|---|---|---|---|
| [12,40] | 28 | 0 | 3 | 3 | 25.7 | 4,261,457 |
| [40,120] | 80 | 0 | 23 | 26 | 101.5 | 21,457,542 |
| [120,200] | 80 | 0 | 32 | 58 | 157.1 | 32,176,206 |
| [200,250] | 50 | 0 | 23 | 81 | 138.9 | 23,660,283 |
| [250,300] | 50 | 0 | 24 | 105 | 153.1 | 27,256,983 |
| [300,345] | 45 | 0 | 24 | 129 | 146.8 | 26,856,142 |
| [345,385] | 40 | 0 | 21 | 150 | 141.7 | 26,212,848 |
| [385,425] | 40 | 0 | 23 | 173 | 147.3 | 26,902,402 |
| [425,465] | 40 | 0 | 22 | 195 | 158.2 | 29,012,223 |
| [465,500] | 35 | 0 | 20 | 215 | 138.4 | 26,210,553 |
| [500,535] | 35 | 0 | 21 | 236 | 151.3 | 26,996,980 |
| [535,570] | 35 | 0 | 22 | 258 | 151.8 | 28,139,036 |
| [570,600] | 30 | 0 | 18 | 276 | 147.0 | 24,873,263 |
| [600,630] | 30 | 0 | 18 | 294 | 156.1 | 25,312,738 |
| [630,660] | 30 | 0 | 19 | 313 | 159.5 | 26,485,586 |
| [660,685] | 25 | 0 | 16 | 329 | 130.0 | 20,952,975 |
| [685,710] | 25 | 0 | 16 | 345 | 135.2 | 23,050,092 |
| [710,735] | 25 | 0 | 15 | 360 | 124.8 | 21,954,578 |
| [735,760] | 25 | 0 | 17 | 377 | 137.4 | 23,907,520 |
| [760,785] | 25 | 0 | 17 | 394 | 157.2 | 24,026,933 |
| [785,810] | 25 | 0 | 16 | 410 | 158.0 | 22,330,181 |
| [810,830] | 20 | 0 | 13 | 423 | 156.5 | 21,135,088 |
| [830,850] | 20 | 0 | 14 | 437 | 141.9 | 20,312,220 |
| [850,870] | 20 | 0 | 13 | 450 | 119.0 | 19,013,584 |
| [870,890] | 20 | 0 | 13 | 463 | 135.9 | 19,561,617 |
| [890,910] | 20 | 0 | 14 | 477 | 143.6 | 22,330,171 |
| [910,930] | 20 | 0 | 14 | 491 | 126.5 | 20,112,001 |
| [930,950] | 20 | 0 | 13 | 504 | 134.7 | 21,110,793 |
| [950,970] | 20 | 0 | 14 | 518 | 141.6 | 22,691,340 |
| [970,990] | 20 | 0 | 14 | 532 | 133.9 | 20,890,856 |
| [990,1000] | 10 | 0 | 7 | 539 | 89.8 | 11,071,113 |
| **[12,1000]** | **988** | **0** | **539** | **539** | **4240** | **710,265,304** |

Every band of `[12, 1000]` returns **winding zero for the derivative on `[1/10, 1/2]`**: no saddle
sits left of the mirror in the scanned strip, which is Speiser's equivalent of RH there, measured.
The right count, **539**, sits against Berndt's asymptotic for the zeros of `ζ'`,
`N₁(T) ≈ N(T) − (T/2π) log 2 = 649 − 110.3 = 538.7` at `T = 1000` — the census and the classical
count agree to the integer. Thirty-one verified compact artifacts, 710 MB, about
71 minutes of wall time on twelve workers sharing the card, chunks shrinking from
eighty to ten bands as the per-band cost grew toward the 175 s aperture. Artifacts under
`output/the_saddles_sit_right_of_the_mirror/`, each re-verified (`... verify <artifact>`: half
boxes as declared, starts re-derived from the whole box `[1/10, 3] × [τ, τ+1]`, every stored
winding re-derived from its polygon, no negative winding).

## 4. Torus, lattice, fractal — the prime clocks

[proved-standard] The prime clocks `p^{−it} = e^{−it log p}` are the torus: `t ↦ (t log p)_p mod
2π` is a Kronecker flow, dense because the `log p` are linearly independent over `ℚ` — unique
factorization, the tree's *"`ℚ⁺` is the free abelian group on the primes; `log` is its additive
chart"*. Each head term `n = ∏ p^a` is a lattice point of the exponent lattice acting on that torus
(`EtaChainTerm` retains amplitude, turn and prime address). The `η` factor `1 − 2^{1−s}` is the
rebase by the prime 2. The zeros and the primes are Fourier-dual through the explicit formula:
`γ` and `log p` are conjugate variables, each zero is a mode `x^{ρ}/ρ` in the prime current, and
on the line every mode decays as `x^{1/2}` — the unbiased landmark field.

## 5. What "physical RH" is, in this framework, and what solving it would take

[interpretation] The physical statement is the **Weil pairing**: for `h = g ∗ g̃`,

```text
    Σ_ρ h(γ_ρ)  =  (receiver terms) − Σ_p Σ_k (log p) p^{−k/2} ĝ(k log p)
```

is the cross-entropy between a receiver's test function and the zero measure, and RH is
equivalent to its **positivity** — a zero off the line is a null direction of that form
(`FRONTIER.md`, Riemann row: *"Weil pairing on the explicit formula's test functions — positive
— a zero off the line is a null direction"*). That is exactly the tree's open fourth row: *the
demanded form is one whose positivity CAN fail*, and here it is the pairing whose non-negativity
on every `g ∗ g̃` is the conjecture. In the flow picture: every vortex sits on the mirror iff the
energy the receiver reads off the prime current is never negative for any admissible aperture.

[interpretation] What the measurements bound: in the strip `[12, 1000]`, every one of the 649
vortices is on the mirror (winding one in a reflection-symmetric box), the eddy never exceeds
0.970, and every one of the 539 saddles found lies right of the mirror, none between `1/10` and it. None of that is the conjecture; all of it
is what the conjecture looks like where it can be seen, and each figure is a falsifier of a
specific reading: a negative winding (a pole), a left saddle (Speiser), an eddy growing without
bound (the count leaving the tide).

[open] Solving physically, in this framework's terms, is exhibiting the Weil pairing as a
**realized positive form** — a supported realizer population whose Gram form is that pairing,
with its null cone proved empty on the admissible test functions — the same species as the
positivity `TraceForm`/`HodgeIndex` already carry in Lean, transplanted to the archimedean place.
The tree's own words for this are in `CLAUDE.md`'s standing mathematics: *"the critical line is the
unitary seam, not a singularity … the open content is 'does a passage exist in the cone' — a
search for an object."* Nothing built here supplies that realizer; what is built is the exact
apparatus that would test one.

## 6. Boundaries

- The saddle census covers `1/10 ≤ σ ≤ 3`; a saddle with `σ < 1/10` is outside it and not claimed.
  A saddle on the mirror would make the certification refuse by name (`unresolved at depth`), not
  count.
- The tide's enclosure is `2^{−96}`-grained after a Stirling remainder near `2^{−69}`; the eddy's
  width is the count's exactness plus that.
- The serial controls for `ζ'` were run at `[36,37]` and the left box of `[100,101]`; the right box
  at 100 exceeds the process aperture serially and was not controlled there.
