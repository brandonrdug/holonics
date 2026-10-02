import Holonics.Foundation.PadicTower
import HolonicsResearch.Geometry.CyclicGrover.ResidueChart
import HolonicsResearch.Geometry.CyclicGrover.TraceComposition

/-! Refs #62. Actual named ContinuingTower restriction and integral trace consumers. -/
namespace Holonics.Epime.GroverTower
open Matrix Polynomial

abbrev TowerDart (n : ℕ) :=
  (Holonics.Foundation.ContinuingTower.padicTower 3).Face (n+1) × Bool

instance towerDart_fintype (n : ℕ) : Fintype (TowerDart n) := by
  change Fintype (ZMod (3^(n+1)) × Bool)
  infer_instance

instance towerDart_decidableEq (n : ℕ) : DecidableEq (TowerDart n) := by
  change DecidableEq (ZMod (3^(n+1)) × Bool)
  infer_instance

def dartChart (n : ℕ) : Dart n ≃ TowerDart n :=
  Equiv.prodCongr (vertexChart n).toEquiv (Equiv.refl Bool)

def ownerRestriction {m n : ℕ} (h : m ≤ n) (d : TowerDart n) : TowerDart m :=
  ((Holonics.Foundation.ContinuingTower.padicTower 3).restrict
    (Nat.add_le_add_right h 1) d.1, d.2)

theorem ownerRestriction_chart {m n : ℕ} (h : m ≤ n) (d : Dart n) :
    dartChart m (restriction m n d) = ownerRestriction h (dartChart n d) := by
  apply Prod.ext
  · change vertexChart m (FiniteCover.vertexRestriction (chart m) (chart n) d.1) =
      (Holonics.Foundation.ContinuingTower.padicTower 3).restrict
        (Nat.add_le_add_right h 1) (vertexChart n d.1)
    exact (residue_restriction h d.1).trans (by rfl)
  · rfl

def ownerFibreChart {m n : ℕ} (h : m ≤ n) :
    Fin (3^(n-m)) × TowerDart m ≃ TowerDart n :=
  ((Equiv.prodCongr (Equiv.refl (Fin (3^(n-m)))) (dartChart m).symm).trans
    (FiniteCover.fibreChart (3^(n-m)) (chart m) (chart n) (fibre_size h))).trans
      (dartChart n)

theorem ownerFibre_projection {m n : ℕ} (h : m ≤ n) (d : TowerDart n) :
    ((ownerFibreChart h).symm d).2 = ownerRestriction h d := by
  change dartChart m (((FiniteCover.fibreChart (3^(n-m)) (chart m) (chart n)
    (fibre_size h)).symm ((dartChart n).symm d)).2) = ownerRestriction h d
  rw [FiniteCover.fibre_projection]
  simpa only [Equiv.apply_symm_apply, restriction] using
    ownerRestriction_chart h ((dartChart n).symm d)

def ownerTrace {R : Type*} [AddCommMonoid R] {m n : ℕ} (h : m ≤ n)
    (f : TowerDart n → R) : TowerDart m → R := IntegralTrace.trace (ownerRestriction h) f

def ownerPullback {R : Type*} [AddCommMonoid R] {m n : ℕ} (h : m ≤ n)
    (f : TowerDart m → R) : TowerDart n → R := IntegralTrace.pullback (ownerRestriction h) f

theorem owner_trace_pullback {R : Type*} [AddCommMonoid R] {m n : ℕ} (h : m ≤ n)
    (f : TowerDart m → R) : ownerTrace h (ownerPullback h f) = fun d => 3^(n-m) • f d := by
  have hp : (fun d => ((ownerFibreChart h).symm d).2) = ownerRestriction h := by
    funext d; exact ownerFibre_projection h d
  simpa only [hp, ownerTrace, ownerPullback] using
    IntegralTrace.trace_pullback_scale (3^(n-m)) (ownerFibreChart h) f

theorem owner_trace_composes {R : Type*} [AddCommMonoid R] {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) (f : TowerDart n → R) :
    ownerTrace hlm (ownerTrace hmn f) = ownerTrace (hlm.trans hmn) f := by
  change IntegralTrace.trace (ownerRestriction hlm)
    (IntegralTrace.trace (ownerRestriction hmn) f) =
      IntegralTrace.trace (ownerRestriction (hlm.trans hmn)) f
  rw [IntegralTrace.trace_comp]
  congr 1
  funext d
  apply Prod.ext
  · exact (Holonics.Foundation.ContinuingTower.padicTower 3).restrict_trans
      (Nat.add_le_add_right hlm 1) (Nat.add_le_add_right hmn 1) d.1
  · rfl

end Holonics.Epime.GroverTower

#print axioms Holonics.Epime.GroverTower.owner_trace_pullback
#print axioms Holonics.Epime.GroverTower.owner_trace_composes
