# The finite chart fibre streamed through one aperture and the admitted image returned its receivers before the source was released

**Date:** 2026-08-27  
**Roadmap locus:** MEM6-R4Q2C--R4Q2D  
**Source owners:** `crates/holonic-engine/src/factored_moment.rs`,
`crates/holonic-engine/src/cuda_refine.rs`, and
`crates/holonic-engine/kernels/refine_shell.cu`

## Exact construction

[proved-derived] Let `X in Z^(m x n)`, `q = min(m,n)`, and `A = max |X_ij|`. The integral
Leibniz bound `D_X = (q A)^q` bounds every minor of `X`. A finite family of distinct word-prime
receiver charts whose product exceeds `D_X` therefore returns the exact rational rank: if every
chart lowered one fixed maximal nonzero minor, their product would divide that minor while being
strictly larger than its absolute value.

[proved-derived] For a selected rank-attaining minor with determinant `D`, the joining numerator
`J`, source constitution `N/d`, and target constitution numerator `J^T N J`, the implementation
derives one reconstruction bound `U` covering determinant, coordinates, constitution, and the
factorization difference. It extends the chart product until the product of charts not dividing
`D` is greater than `2U`. Centered CRT is therefore unique for every reconstructed signed integer.
Denominators never enter modular inversion.

[proved-derived] Exact device verification of `D X = J B` and
`numerator(H_target) = J^T N J` in every sufficient chart closes the integral squares because the
combined chart product exceeds the derived bound on every possible nonzero difference. This is a
complete finite reconstruction fibre, not probabilistic agreement.

## Resident realization

[implemented-exact] One reusable device residue aperture streams one chart at a time into resident
mixed-radix accumulators. The implementation does not retain a
`chart_population x value_population` residue tensor. Limb populations and chart populations are
derived from the entering extents and bounds; overflow is an obstruction.

[implemented-exact] The source image remains immutable standing while the reconstructed target is
a staged delta. The card gathers the target incidence and constitutive numerator only after the
exact-square obstruction remains zero. Every already-mounted primitive sparse integral receiver is
then contracted directly against the target factorization `B^T H B`; no ambient factor-by-factor
covariance is materialized. One terminal return admits or refuses the entire word. On admission it
releases the source and moves the already-produced target buffers into the sole continuing
resident image at generation one.

[proved-derived] The device may choose a different full-row-rank image chart from a cold founder.
Literal coordinate equality between those charts is not the equality obligation. Equality is the
complete admitted incidence square, constitutive pullback square, and every declared receiver
consequence, with each chart's reconstruction fibre retained.

## Measured return

[established-bounded; implemented-exact; measured] The focused production test
`cuda_refine::tests::factored_moment_descent_contracts_receivers_and_atomically_continues` passed
on the RTX card. The kernel word itself returned in 1.88 seconds after compilation. It reported:

- exact target rank equal to the cold direct construction;
- exact target receiver coordinates equal to every direct primitive-form contraction;
- zero intermediate host egress;
- no host pivot, host CRT, or host rational continuation;
- no ambient factor square;
- atomic image replacement; and
- source release only after device admission.

The bounded command was:

```text
timeout -k 2s 175s cargo test -p holonic-engine cuda_refine::tests::factored_moment_descent_contracts_receivers_and_atomically_continues --lib -- --ignored --exact
```

`cargo check -p holonic-engine --lib` also passed. The remaining construction is not another
reconstruction owner: MEM6-R4Q3 must compose this owner with the actual Athena membrane and close
foundation plus two successor squares before the unchanged R4Q4 world-tube may run.
