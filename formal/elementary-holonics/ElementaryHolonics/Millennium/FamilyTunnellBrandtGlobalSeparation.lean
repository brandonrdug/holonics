import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighbors
import ElementaryHolonics.Millennium.FamilyTunnellNormOneReturn

/-!
# The odd-prime local chart does not identify the global Brandt classes

The two ternary lattices are exactly equivalent after reduction at every odd
prime.  They are nevertheless not globally equivalent as integral quadratic
receivers: the first has norm-one occurrences and the second has none.

This is the receiver-insufficiency separator for the next Brandt deed.  A
destination classifier may use the local chart to transport directions, but it
must retain the global class fibre; it cannot declare the two classes equal.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtGlobalSeparation

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors
open Soma.Holonics.Millennium.FamilyTunnellNormOneReturn

variable {p : ℕ} [Fact p.Prime]

/-- Even an arbitrary bijection of integral occurrences cannot identify the
two quadratic receivers.  Additivity is not needed for this obstruction. -/
theorem no_integral_receiver_equivalence :
    ¬ ∃ e : IntTriple ≃ IntTriple,
      ∀ m : IntTriple, brandtSecondQuadratic (e m) = brandtFirstQuadratic m := by
  rintro ⟨e, he⟩
  have hone : brandtSecondQuadratic (e (0, 1, 0)) = 1 := by
    rw [he]
    norm_num [brandtFirstQuadratic]
  exact brandtSecondQuadratic_ne_one (e (0, 1, 0)) hone

/-- At every odd prime the residue receiver still has an exact equivalence.
The conjunction with the previous theorem is the explicit local/global
separator. -/
theorem oddPrime_local_equivalence_global_separation (hp2 : p ≠ 2) :
    (∀ v : ResidueTriple (p := p),
      reducedBrandtSecondQuadratic (brandtFirstSecondEquiv hp2 v) =
        reducedBrandtFirstQuadratic v) ∧
    ¬ ∃ e : IntTriple ≃ IntTriple,
      ∀ m : IntTriple, brandtSecondQuadratic (e m) = brandtFirstQuadratic m := by
  constructor
  · exact reducedBrandtSecondQuadratic_brandtFirstSecondEquiv hp2
  · exact no_integral_receiver_equivalence

#print axioms no_integral_receiver_equivalence
#print axioms oddPrime_local_equivalence_global_separation

end Soma.Holonics.Millennium.FamilyTunnellBrandtGlobalSeparation
