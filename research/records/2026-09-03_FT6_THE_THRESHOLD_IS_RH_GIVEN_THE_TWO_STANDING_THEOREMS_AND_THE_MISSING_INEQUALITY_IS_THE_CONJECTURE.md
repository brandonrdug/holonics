# FT6: the threshold is RH given the two standing theorems, and the missing inequality is the conjecture

**Date:** 2026-09-03  
**Truth status:** `proved-derived` for the returned theorems; `open` for the named ports.  
**Evidence:** `formal-checked`, `source-inspected`  
**Campaign:** FT6 under
[`THE_FLOW_CARRIES_THE_ZEROS_AS_FOSTER_TANKS_AND_THE_THRESHOLD_IS_THE_TARGET.md`](../../archive/plans/THE_FLOW_CARRIES_THE_ZEROS_AS_FOSTER_TANKS_AND_THE_THRESHOLD_IS_THE_TARGET.md).  
**Owner:** `RH/ThresholdReturn.lean` under `soma/formal/elementary-holonics/ElementaryHolonics/`,
registered in the root umbrella.  
**Scope:** the phase's return under the contract's second clause: the first exact missing
inequality, with its falsifier, deposited. The campaign closes with this record.

## The exact form of the target

[proved-derived; formal-checked] With `seamTimes` and `Λ_DN = sInf seamTimes` of FT4 (iv)–(v):

- `riemannHypothesis_iff_Λ_DN_le_of : DeBruijnBound → (RiemannHypothesis ↔ Λ_DN ≤ 0)`;
- `Λ_DN_le_half : DeBruijnBound → Λ_DN ≤ ½`;
- **`riemannHypothesis_iff_Λ_DN_eq : DeBruijnBound → RodgersTaoNonneg → (RiemannHypothesis ↔ Λ_DN = 0)`**,
  the target's exact form.

[open; project-postulate] The two ports are the standing theorems of the literature that this
line does not return, and neither is the target nor implies it: `DeBruijnBound` (`½ ∈ seamTimes`:
every zero of `H_{1/2}` lies on the seam, de Bruijn 1950) and `RodgersTaoNonneg` (`0 ≤ Λ_DN`,
Rodgers–Tao 2018). Their obstructions under this contract are recorded: de Bruijn's bound does
not transport from `PairDescent`, since a highest pair need not exist at the entire face
(FT4 record); Rodgers–Tao's argument runs on the descent side, where FT5 shows the flowed integer
events do not separate.

## The first exact missing inequality, deposited

[definition] Given the two ports, the target `Λ_DN = 0` is equivalent to **`Λ_DN ≤ 0`**, and
`Λ_DN ≤ 0 ⟺ 0 ∈ seamTimes ⟺ RH` (`RealZeroTimes.zero_mem_iff`, `LinePreservation`). The
inequality the campaign is missing is therefore `Λ_DN ≤ 0` itself: there is no further exact
inequality between it and the conjecture. Its falsifier is the null falsifier of the conjecture,
which the contract names: a zero of `ξ` off the seam — equivalently a zero of `H_0` with
`Re z ≠ ½`, which by the up-set law would keep `Λ_DN > 0`. The contract's proposed sharper form,
"the inequality the bound integer side violates that the free one satisfies", cannot be formed on
the integer side, since on the descent side the flowed events diverge (FT5); it would have to be
formed on the kernel side, as an inequality of `∫ e^{τ u²} e^{(z−½)u} Φ(u) du` along a descending
pair, and no such inequality is returned here.

`#print axioms` on `riemannHypothesis_iff_Λ_DN_eq` and `Λ_DN_le_half` returns `propext`,
`Classical.choice`, `Quot.sound`. The owner builds alone and inside the root umbrella
(9,812 jobs).

## Pass FT6

The named missing inequality `Λ_DN ≤ 0`, with the null falsifier of the conjecture, is deposited
as the phase's return, and the target's exact form is formal-checked against the two named
standing theorems. **FT6 passes at the deposited-inequality scope; the campaign closes.** Nothing
here places a zero or moves the Riemann Hypothesis.

## What the campaign returned, in one place

- FT0–FT3: the tanks, the count, the paired product, Hadamard `ξ² = ξ(½)² P`, the Foster form,
  the comb flux at every simple zero.
- FT4: the Foster class for every symmetric entire function of order below two with a centre
  value; the kernel `Φ` even and positive; `ξ(s) = ∫ e^{(s−½)u} Φ(u) du`;
  `heatE t ξ (z) = ∫ e^{−t u²} e^{(z−½)u} Φ(u) du`; the RT3 port as a theorem; the semigroup at
  the entire face; Hurwitz on rectangles; the Pólya step at the entire face; the seam times as a
  closed up-set with `0 ∈ seamTimes ↔ RH`; `Λ_DN`; `seamTimes.Nonempty → (RH ⟺ Λ_DN ≤ 0)`.
- FT5: the flowed events and their weights; the identity on `t ≥ 0`; the divergence on `t < 0`.
- FT6: `RH ⟺ Λ_DN = 0` given de Bruijn and Rodgers–Tao; the missing inequality named.

## Reproduction

```bash
cd soma/formal/elementary-holonics
timeout 180s lake build ElementaryHolonics.RH.ThresholdReturn
timeout 180s lake build ElementaryHolonics
```
