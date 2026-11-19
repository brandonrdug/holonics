import Holonics.Physics.Information.CrossEntropyRate
import Holonics.Physics.Information.PortWork
import Holonics.Physics.Information.ClockJoin

/-!
# Physics.Information: the ratio covector at a physical port, and the plural-clock return

[definition] Rebuild step 6, K4 (#75; restructure plan §3.6 at `13f8c734`; CLAUDE.md, "loss is the
logarithm of a ratio of Holons"). Cross-entropy acts physically only through a stated material or
port return. This root gathers that return, its rate on plural clocks and the join of the clocks.
Rust owners `holonics::physics::information` and `holonics::aeon::join_axes`.

- `Information/CrossEntropyRate`: `dC/dλ = −Σ ṗ log q − Σ p q̇/q` over the owner's
  `finiteCrossEntropy`, the rate of the first law's continuous chart
  (`Aeon/Production/FirstLaw.hasDerivAt_crossEntropy`: exchange plus deposition), on sections and
  with each motion's clock-rate map; the normalization of a moving aperture; the
  relative entropy's rate; the reference's motion is load-bearing.
- `Information/PortWork`: a thermal port constituted by its levels (partition function and computed
  canonical state); a covector reaches it as a level shift; quench, relaxation and quasi-static
  restoration return work, heat and production `D(p‖q′)`, with the restoring leg's zero production
  a theorem of the computed end states; the work extracted is the free-energy drop less the
  production; the matched covector, the modulus face `log(q/p)` of the full ratio covector, is
  reversible and extracts `F(p) − F(q) = θ D(p‖q)` (`InformationDifference`); free relaxation
  produces exactly `D(p‖q)`; a scalar face does not determine the effort.
- `Information/ClockJoin`: a join of clock axes exists exactly when every cycle of declared rates
  reads trivially, otherwise the cycle is its defect; the two-parameter flow square commutes or
  returns its commutator, and a non-commuting square changes the cross-entropy return.

The finite-step quasi-static limit (the restoring leg as `N` quench-and-relax steps whose production
`Σ D(qₖ‖qₖ₊₁)` is at most `(b − a)²/(8Nθ²)` and tends to the restoring leg's zero), a moving support
(edge transport of the aperture, an entrance's one-sided rates), a ring port that receives the
covector's phase face, and `R⁻¹dR` read at the two ports stand in
`HolonicsResearch/Physics/InformationPort` (#410). The Rust consumer `physics::information::apply`
retired with `crates/holonics` (C8 of #603).
-/
