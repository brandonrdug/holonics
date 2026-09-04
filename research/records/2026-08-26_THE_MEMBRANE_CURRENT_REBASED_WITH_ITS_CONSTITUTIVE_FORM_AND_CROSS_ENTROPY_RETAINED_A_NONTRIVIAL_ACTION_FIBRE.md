# The membrane current rebased with its constitutive form and cross-entropy retained a nontrivial action fibre

**Date:** 2026-08-26  
**Phase:** MEM0  
**Truth status:** `[proved-derived; formal-checked]`  
**Evidence:** focused theorem build, complete library import build, and explicit axiom audit.  
**Artifact:**
[`HolonicMembraneActionTransport.lean`](../../formal/elementary-holonics/ElementaryHolonics/Millennium/HolonicMembraneActionTransport.lean)

## Returned construction

[proved-derived; formal-checked] `AddressedMembraneContact` retains one crossing occurrence, both
boundary faces, exterior and interior potentials, the additive chart transport, and the
constitutive admittance. `returnedPotential` is formed in the interior target fibre as

```text
interior - transport(exterior),
```

and `returnedCurrent` applies the admittance only after that complete difference exists. An
arbitrary scalar receiver is downstream and retains its complete contact reconstruction fibre.

[proved-derived; formal-checked] `membraneCurrent_rebase` proves naturality only when the exterior/
interior transport square and the constitutive/current square both commute. Moving incidence,
potential, or constitution alone is therefore not mislabeled a rebase.

[proved-derived; formal-checked] `localMembraneMixing_reorient` composes the existing two-index
Complex-Parametron response: incidence and its full coupling table reorient together.
`localMembraneMixing_zero_of_couplingRow_zero` is the disjoint-contact negative control. These
theorems support arbitrary codec crossing through founded contact; they do not assert all-to-all
mixing.

[proved-derived; formal-checked] `FiniteCrossEntropyReceiver` admits conventional
`-sum p_i log q_i` only after reference normalization, emitted positivity, and emitted normalization
are supplied. Its face retains the complete action fibre. `quarterTailEmission` and
`splitTailEmission` are distinct, strictly positive normalized three-member sections with the same
cross-entropy under `firstOnlyReference`; the equal face therefore has a concrete nontrivial fibre.
`no_successor_factor_of_equal_face` proves that any later receiver which separates such actions
cannot factor through the scalar. The binary normalized-exponential common-shift gauge is inherited
from the exact difference receiver.

## Verification

[measured] The focused file check completed successfully in 3.7 seconds. The module build plus the
complete `ElementaryHolonics.lean` import check completed successfully in 11.4 seconds. The source
artifact SHA-256 is
`cd518d695ac71431542d6942b2f4add5699575c0570e728e5f7d34d9a01d7f69`.

[formal-checked] Every new `#print axioms` result contains only `propext`, `Classical.choice`, and
`Quot.sound`. No project axiom, probability governor, physical calibration, unrestricted-contact
law, or software/physics identity was introduced.

## Boundary

[open] MEM0 does not prove a partial/noninvertible fibre transport, a full complex sesquilinear
`B^dagger M B` storage theorem, durable morphology, arbitrary-organ ingress, native radiation, or
the integrated qualitative receiver. MEM1 is now the next deed and must compose the existing
atomic membrane with the native conducted section rather than found a new semantic owner.
