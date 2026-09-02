# Band-limited relevance: nothing feeds the far tail but the tail itself

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 4093 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, closing the relevance theorem Brandon asked for in its cleanest form. Assistant derivation for the proofs on the feed comb and the Kirchhoff law.
**Band:** BAND-LIMITED SLICE / EVERY FEED TOOTH INTO THE FAR TAIL VANISHES / ADVECTION MODE AND TRANSFER VANISH BEYOND 2N / CURRENT INTO THE COMPLEMENT OF THE DOUBLE CUBE IS ZERO / TRANSFER CONSERVED WITHIN 2N / DOUBLE-CUBE MASS DISSIPATES WITHOUT EXCHANGE / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesBandLimitedRelevance.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`BandLimited N` (`û_p = 0` off the cube of radius `N`); `jacobianMode_eq_zero_of_bandLimited`;
`feedTerm_eq_zero_of_bandLimited` (every tooth into a receiver outside the double cube vanishes,
through `transported_not_mem`); `advectionMode_eq_zero_of_bandLimited`;
`transfer_eq_zero_of_bandLimited`; `tsum_compl_transfer_eq_zero` (no current beyond `2N`);
`sum_transfer_cube_eq_zero` (the transfer is conserved within the double cube);
`hasDerivAt_bandMass_of_bandLimited`: `d/dt E_{cube 2N} = −2ν D_{cube 2N}` at a band-limited time.

## Reading

[definition] This is the relevance theorem as a statement about the current: the far tail is not
fed by anything but the tail. A slice whose modes live in the cube of radius `N` has a transfer
comb whose every tooth into a receiver beyond `2N` carries a participant beyond `N`, hence zero;
the whole current beyond `2N` vanishes, and the mass in the double cube can only dissipate.
Growth of the tail is therefore always a chain: each step reaches at most twice the previous
band, and each step is paid through the frontier current of the band below it. The
`reach_subset_frequencyCube` law (`2^m N` after `m` steps) is the same statement iterated.

[established-bounded] Next in the loop: Hodge, then the NS frontier chain quantitatively
(the current into `(cube 2N)ᶜ` bounded by the shell `N < |·| ≤ 2N` masses), then BSD sign law.

## Evidence

- `lake build ElementaryHolonics.Millennium.NavierStokesBandLimitedRelevance` green within the 180 s bound.
- Axiom audits: `feedTerm_eq_zero_of_bandLimited`, `sum_transfer_cube_eq_zero`,
  `hasDerivAt_bandMass_of_bandLimited` each depend on `[propext, Classical.choice, Quot.sound]`.
