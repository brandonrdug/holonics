import HolonicsResearch.Geometry.CyclicGrover.TowerCover
import Mathlib.Data.ZMod.Basic

/-! Refs #62. The finite graph's residue chart intertwines the actual castHom
operation used by ContinuingTower.padicTower at positive levels. The full
ContinuingTower import itself remains outside this bounded private check. -/
namespace Holonics.Epime.GroverTower

instance count_neZero (n : ℕ) : NeZero (count n) :=
  ⟨by have := count_ge_three n; omega⟩

def vertexChart (n : ℕ) : Fin (chart n+2) ≃+* ZMod (count n) :=
  (ZMod.finEquiv (chart n+2)).trans (ZMod.ringEquivCongr (chart_size n))

theorem vertexChart_val (n : ℕ) (x : Fin (chart n+2)) :
    (vertexChart n x).val = x.val := by
  change (ZMod.ringEquivCongr (chart_size n) (ZMod.finEquiv (chart n+2) x)).val = x.val
  rw [ZMod.ringEquivCongr_val]
  rfl

theorem vertexChart_natCast (n : ℕ) (x : Fin (chart n+2)) :
    vertexChart n x = (x.val : ZMod (count n)) := by
  rw [← vertexChart_val n x, ZMod.natCast_zmod_val]

theorem residue_restriction {m n : ℕ} (h : m ≤ n) (x : Fin (chart n+2)) :
    vertexChart m (FiniteCover.vertexRestriction (chart m) (chart n) x) =
      ZMod.castHom (m := count m) (n := count n)
        (pow_dvd_pow 3 (Nat.add_le_add_right h 1)) (ZMod (count m))
        (vertexChart n x) := by
  rw [vertexChart_natCast, vertexChart_natCast, map_natCast]
  apply ZMod.val_injective (count m)
  simp only [ZMod.val_natCast, FiniteCover.vertexRestriction, Fin.val_ofNat]
  calc
    x.val % (chart m+2) % count m = x.val % count m % count m :=
      congrArg (fun k : ℕ => x.val % k % count m) (chart_size m)
    _ = _ := Nat.mod_mod _ _

end Holonics.Epime.GroverTower

#print axioms Holonics.Epime.GroverTower.residue_restriction
