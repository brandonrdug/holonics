# UAR R0Q session checkout — the receiver order was repaired but the site transport remained diagonal

Date: 2026-08-30  
Goal: UAR2–UAR4 completion  
Standing: paused; no process remains active

## Returned work

- [proved-derived; formal-checked] The complex current must join linearly at its addressed port before the positive constitutive receiver measures it. Summing local norms before the junction is refuted by the exact cancellation witness `‖1 + (-1)‖² ≠ ‖1‖² + ‖-1‖²`. The construction is in `soma/formal/elementary-holonics/ElementaryHolonics/Computation/HolonicOrientedSiteTransport.lean`.
- [implemented-exact] The CUDA return now exposes device-enacted local factor currents. The source-neutral relational rest retains those currents and contracts them at `(port, factor)` before applying its positive receiver.
- [measured] The relevant Rust, CUDA-owner, and Lean checks passed. No UAR qualitative gate passed and `CONSTRUCTION_STATE.md` was not advanced.

## Blocking counterexample

- [counterexample] Ordinary exterior transitions still realize effectively diagonal site motion `z -> z`; only the closure transition advances to a successor site. The runtime therefore does not yet enact the required oriented transport `A_p(z,z')`.
- [measured] The attempted control expanded about 199,804 complex-site coordinates into 487,601 pair-current contributions and contracted 63,932 port-factor coordinates on the CPU. It exceeded the 175-second boundary after emitting only an apostrophe as its first selected boundary face.
- [process-audit] Repeated full controls and local arithmetic optimizations after this counterexample were churn. The hot dependent contraction and genuine off-diagonal site transport must be repaired before another control is permitted.

## Sole pickup deed

Revise R0Q into two explicit obligations: (1) enact genuine addressed `z -> z'` transport for ordinary passages, and (2) carry the sparse dependent complex-current contraction on the resident GPU surface. Require static receipts for both, then run the unchanged qualitative receiver once under the existing 175-second ceiling. Do not advance UAR or construction state from the present partial return.
