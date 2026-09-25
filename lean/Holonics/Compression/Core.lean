import Holonics.Compression.Core.FaceMap
import Holonics.Compression.Core.Resonance
import Holonics.Compression.Core.Cost
import Holonics.Compression.Core.Keys

/-!
# Holonic Compression: the law over its owners

[definition] Rebuild step 3 (#145): **compression is intelligence is navigation**. Holonic
Compression couples a navigator's resonating modes with terrain; a compression is a codec pivot
carrying its decoder. This root states that law once, over the existing owners, in four parts.
Namespaces: `Holonics.Compression.Core.{FaceMap, Resonance, Cost, Keys}`.

1. `Core/FaceMap`: the face map `F x (ρ, w) = ρ(T_w x)` of a navigator family against terrain and
   a receiver family. Its kernel is `CausalRelevance.futureCollapsed` (the kernel of a product map),
   and quotienting by it is the coarsest lawful retention
   (`Standing.standingLaw_exists_iff_future_factors`), on which every navigator runs. Words of
   length at most `dim X − 1` read the whole kernel, and that bound is attained. The finite face
   map keeps the ledger `rank + dim ker = dim X`, `dim coker = dim faces − rank` (horizon-relative),
   and a face is reachable exactly when its cokernel class is zero, exactly when every cocycle
   vanishes on it (`Objects/Pairing`). Over ℤ a class can be reachable only in a multiple: that
   join is `HolonicsResearch/Landmarks/IntegralCokernel.reachableOnlyInMultiple_iff` (a nonzero
   torsion cokernel class, which the ℤ- and ℚ-valued cocycles miss).
2. `Core/Resonance`: the unique `C`-orthogonal split of a drive at `ω²` into its resonating part
   (in `ker(K − ω²C)`, RIDE) and its emanating part (FOUND). RIDE keeps the exchange law
   (`Parametron.modeEnergy_conserved`) and needs zero effort. FOUND needs nonzero effort, and the
   work it exchanges is an exact quadratic form of the emanating part alone. Every motion keeps the
   balance `dE/dt = ⟨C ẍ + K x, ẋ⟩`, so founding a mode from rest takes exactly its energy as port
   work. The clamp witness shows that effort need not do work, so no fixed price is asserted. In the
   learning chart (`Aeon/Production/FirstLaw`), deposition onto the arrived source is zero exactly
   at resonance.
3. `Core/Cost`: a navigator codec is named by an actual code over a declared codec family, read
   back by its decoder; its cost is `Kt = |code| + ⌈log₂ t⌉` against the literal code, and it pays
   off exactly when `Kt < ℓ`, an integer comparison of two codes. The partial pivot prices RIDE and
   FOUND in bits: regenerated faces ride on the description, each founded face adds one patch. The
   Perron navigator's code of a walk telescopes (`Foundation/ReceiverCodeCost`). Witnesses: the
   alternator pays off exactly from length `10`; one founded face in `64` still pays off; material
   outside the family's image stays literal.
4. `Core/Keys`: locating keys. The consistent keys are the fibre of the loop-closure map, joined to
   the Bombe's test by `HelicalPairInteraction.menu_loop_closure`; each added loop only shrinks it.
   The fibre is a union of gauge orbits, no menu separates the true key from its gauge image, and
   when the menu pins the boundary at each key the survivors are one gauge orbit. In a reflector
   machine the candidates prune `18 → 6 → 3`, the three survivors are one orbit, and one loop
   leaves a survivor off it.

[open] Obligations left for #62. The integral cokernel ledger (a finite-dimensional ledger for an
integral face map, beyond the reachability join above). The RIDE/FOUND split is stated for the
parametron's diagonal constitution without dissipation: with `D ⪰ 0` the steady driven response
`(K − ω²C + iωD)⁻¹` and its dissipated work per cycle are owed. The linear face map's cokernel
residual has no bit price here; only a codec's residual patches are priced. Key inference is stated
for permutation stage words (the Bombe); its extension to continuous navigator configurations
(screw and phase keys) is owed, together with the joint description of key and gauge.
-/
