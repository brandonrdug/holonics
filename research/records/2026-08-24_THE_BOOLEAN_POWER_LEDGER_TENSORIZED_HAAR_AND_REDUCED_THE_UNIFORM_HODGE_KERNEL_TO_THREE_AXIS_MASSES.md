# The Boolean power ledger tensorized Haar and reduced the uniform Hodge kernel to three-axis masses

**Date:** 2026-08-24  
**Scope:** exterior Lean theorem station; this record schedules no Rust/GPU deed and does not move
`CONSTRUCTION_STATE.md`.  
**Truth status:** each material claim is graded locally under `canon/EPISTEMIC_GRADES.md`.

## 1. Development card

[definition] The source owners are the coordinate Boolean lattice, finite character synthesis,
zero-padded Abel differences, the dyadic Hodge coefficient cube, normalized circle Haar measure,
the returned low-scale kernel bound, and the terminal-half continuation passage. The new
consequence is one specialization-independent coordinate Haar receiver and its first direct Hodge
composition.

[definition] The event occurrence is a receiver choice at one torus point: for each coordinate it
uses either the undifferenced near estimate or the second-Abel far estimate. Its predecessor is the
complete family of eight coefficient returns. Its local constitutive law is exact finite Abel
summation; its receiver is normalized Haar `L¹`; and its returned consequence is a physical-kernel
bound with the complete coefficient-side residual retained as a named proposition.

[definition] The falsifiers are a singular character division, a subset exponent which leaves
uncancelled radial growth after Haar integration, a six-letter stencil estimate which forgets that
the letters lie on three distinct axes, or a continuation theorem which silently assumes the
coefficient return it is meant to construct.

## 2. The coordinate receiver is a Boolean power ledger

[proved-derived; formal-checked] `Foundation/CoordinateSubsetReceiver.lean` defines the complete
coordinate-face population as the powerset of `Fin n` and proves that it has `2^n` members. In
three dimensions the receiver therefore has exactly eight faces. An active coordinate carries
second difference order two; its complement carries the near-window coordinates.

[proved-derived; formal-checked] For a face `S` in three dimensions, Lean proves the coefficient
mass exponent

```text
3 - 2 |S|
```

and the exact receiver balance

```text
(3 - 2 |S|) + |S| - (3 - |S|) = 0.
```

The four cardinality classes are consequently `R^3`, `R`, `R^-1`, and `R^-3`. The far-coordinate
Haar volume restores one power while its Abel denominator spends one power; the inactive near
window spends the complementary dimension. No asymptotic step occurs in this ledger.

[proved-derived; formal-checked] The constants appearing in this station retain distinct typed
origins:

```text
3^3 = 27                         Hodge entry addresses
2^3 = 8                          near/far coordinate faces
(2^(s+3) - 1)^3                 finite aperture population
27 * 8 = 216                    entrywise Haar assembly
27 * 31^3 = 804357              exact scales zero through two
```

Equal numerical bases or exponents do not identify those populations. `3^3` is a product of
component, derivative-coordinate, and input-coordinate addresses; `2^3` is a Boolean receiver over
three geometric coordinates.

[definition] Large decimal constants use the exact radix-magnitude chart
`mantissa * 10^magnitude`, never floating scientific notation. The magnitude is a natural-number
index. For a canonical nonzero chart, take the greatest magnitude whose power of ten divides the
integer, leaving a mantissa not divisible by ten; zero uses magnitude zero. This face is useful for
scale comparison but does not replace the structural factor ledger: `10^magnitude` itself carries
the paired prime valuations `2^magnitude * 5^magnitude`.

[interpretation] This supplies a precise part of the proposed holonic exponent tower. A factor
`A^B` is a receiver shadow only after the carrier counted by `A` and the independent/addressed rank
counted by `B` have been forgotten. Coarse graining may make one completed population the base of a
later power, but a lawful tower must retain the rebase map, orientation, difference order, and
reconstruction fibre. This is compatible with the existing exact rank/difference material in
`Towers.lean` and the prime/modulus records; it is not by itself a theorem about primes or Fermat
curves.

## 3. One circle returns the global analytic constant

[proved-derived; formal-checked] `Foundation/CoordinateHaarReceiver.lean` defines the continuous
totalized penalty

```text
E_R(z) = R / max(1, R^2 |1 - exp(2 pi i z)|^2).
```

The unit-circle chord inequality and a Lorentz majorant give

```text
integral E_R <= arctan(2R) < pi/2 <= 2
```

for every `R >= 1`. Fubini on the three-torus then proves the tensor-product integral is at most
`2^3 = 8`.

[proved-derived; formal-checked] The same file constructs the unique pointwise far face and proves
that if every coordinate subset `S` returns mass

```text
C * R^(3-|S|) * (R^-1)^|S|,
```

then the original value is bounded by `C` times the product of the three totalized penalties. The
proof never divides by a character on its singular subtorus.

## 4. The direct Hodge specialization composes

[proved-derived; formal-checked]
`NavierStokesDyadicHodgeSubsetReceivers.lean` proves the exact finite Abel identity for all eight
coordinate faces and bounds each character-weighted physical kernel entry by the complete absolute
mass of its zero-padded coefficient population.

[proved-derived; formal-checked] `NavierStokesDyadicHodgeHaarReceiver.lean` defines
`DyadicHodgeSubsetMassReturn` and proves that all eight returns for one entry imply physical Haar
`L¹` mass at most `8 C`. A common large-scale return for all twenty-seven entries therefore gives

```text
dyadicHodgeJacobianKernelL1 scale <= 216 C.
```

Joining that theorem to the exact three low scales constructs

```text
UniformDyadicHodgeJacobianKernelBound (804357 + 216 C).
```

[proved-derived; formal-checked]
`NavierStokesDyadicHodgeHaarContinuation.lean` transports the constructed uniform witness into the
existing terminal-half continuation theorem. It introduces no new analytic premise; the resulting
extension remains explicitly conditional on the critical-vorticity interval integral and the
declared high-order restart supply.

## 5. The six-letter support objection is closed by typing the axes

[proved-derived; formal-checked]
`NavierStokesThreeAxisDyadicHodgeSupportStencil.lean` proves that a nonzero three-axis scalar
difference contains an actual direct-band support pin. Although the complete second-order word has
six occurrences, every occurrence remains addressed to axis zero, one, or two, and each individual
coordinate changes by at most two across the full scalar/complementary pair.

[proved-derived; formal-checked] The coordinatewise pin theorem proves the complete complementary
Hodge stencil retains lower denominator `(2^s-3)^2` and upper aperture
`outer(scale+1)+4`. The coarser untyped estimate by total word length would have suggested an
unnecessary `2^s-5` lower scale. This is an exact example of why a product or power count cannot
replace the oriented/addressed population which produced it.

[proved-derived; formal-checked]
`NavierStokesThreeAxisScalarSubsetVariation.lean` separately returns the scalar Fubini envelope for
all twenty-seven allocations `(a,b,c)` with each order in `{0,1,2}`, including the top scalar mass
`72/R^3`. `NavierStokesThreeAxisHodgeSubsetEnvelope.lean` returns the first genuinely three-axis
Hodge entry face `(1,1,1)` and its explicit `(226 * 10^6)/R^3` envelope. The exact allocation
ledgers for `(1,1,2)` and `(1,2,2)` have also been defined and checked at scales
`(46 * 10^9)/R^4` and `(12 * 10^12)/R^5`; their pointwise identification with the corresponding
Hodge differences remains open.

## 6. Exact residual and cross-problem use

[open] The coefficient interface `UniformLargeScaleDyadicHodgeSubsetMassReturn C` is not yet
inhabited. Two of its eight faces already have the required scale from checked owners: the empty
face follows from coefficient norm at most one, aperture count at most `8 R`, and hence mass at
most `512 R^3`; the addressed pair `{0,1}` has mass at most `(34 * 10^12) / R`. The other two pair
addresses are not silently identified with `{0,1}`: either their transported chart square or the
common three-axis chart must be returned.

[open] The shortest remaining owner is a generic three-coordinate zero-padded frequency/reindex
construction. It must join the scalar allocations to every complementary Hodge allocation, prove
the actual pointwise `(1,1,2)` and `(1,2,2)` Hodge-difference identities, return both aperture
flanks, and dispatch the six still-open Boolean faces into one common constant `C`. The current
envelope arithmetic supplies `42 * 10^17` as a deliberately coarse candidate magnitude for that
dispatch; this numeral is not promoted to a mass theorem until the finite population assembly has
been checked. The coordinatewise support theorem closes the former aperture ambiguity; it does not
perform this assembly.

[open] This station is not a Navier--Stokes regularity proof. Even after the coefficient return
constructs the uniform kernel witness, the official global theorem still requires finiteness of
the critical-vorticity time integral for arbitrary smooth periodic data and the typed restart
passage consumed by the continuation seam.

[interpretation] The reusable theorem is broader than fluid dynamics: a Boolean family of local
returns with exact scale balance can be tensorized through a positive receiver without erasing its
singular faces. Hodge theory may instantiate the faces by chart/cell differences, Yang--Mills by
covariant word defects, RH by prime-local Euler/Mellin returns, and BSD by valuation and local-height
returns. Each line still owes its own constitutive map, positivity theorem, and global falsifier;
the coordinate Haar theorem supplies the composition pattern, not those missing Millennium
conclusions.

[open] The arithmetic tower suggested by the factor patterns should next be formalized only after
the current coefficient mass closes: its owner must distinguish population base, independent rank,
difference order, receiver quotient, and rebase lineage. A bare nested numeral such as
`(A^B)(C^D)^(E^F)(G^H)` does not determine its association or its geometry. Decimal coarse
constants should therefore be displayed exactly as `mantissa * 10^magnitude`; the magnitude is an
index, while the uncondensed structural factorization remains separate testimony.
