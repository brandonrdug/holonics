import Holonics.Foundation.TowerCarrier
import Mathlib.Data.ZMod.Basic

/-! Refs #62. The existing padicTower, moved unchanged; no parallel tower. -/
namespace Holonics.Foundation.ContinuingTower
variable (p : ℕ) [Fact p.Prime]

/-- [definition] The `ℤ/p^n` tower under the canonical cast maps. -/
def padicTower : Tower.{0, 0} ℕ where
  Face := fun n => ZMod (p ^ n)
  restrict := fun {m _} h x => ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m)) x
  restrict_refl := by
    intro n x
    simp
  restrict_trans := by
    intro i j k hij hjk x
    show ZMod.castHom (pow_dvd_pow p hij) (ZMod (p ^ i))
        (ZMod.castHom (pow_dvd_pow p hjk) (ZMod (p ^ j)) x) =
      ZMod.castHom (pow_dvd_pow p (le_trans hij hjk)) (ZMod (p ^ i)) x
    rw [← RingHom.comp_apply, ZMod.castHom_comp]

end Holonics.Foundation.ContinuingTower
