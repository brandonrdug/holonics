import HolonicsResearch.Geometry.CyclicGrover.GroverAction
import HolonicsResearch.Geometry.CyclicGrover.IntegralTrace

/-! Refs #62. Euclidean residue is the cover, and Euclidean carry is its fibre.
The actual degree-two Grover matrices consume both integral cover maps. -/
namespace Holonics.Epime.FiniteCover
open GroverCycle Matrix

def vertexRestriction (c f : ℕ) (x : Fin (f+2)) : Fin (c+2) :=
  Fin.ofNat (c+2) x.val

def restriction (c f : ℕ) (d : Dart f) : Dart c :=
  (vertexRestriction c f d.1, d.2)

theorem rotation_natural (c f : ℕ) (hd : c+2 ∣ f+2) (x : Fin (f+2)) :
    vertexRestriction c f (finRotate (f+2) x) =
      finRotate (c+2) (vertexRestriction c f x) := by
  apply Fin.ext
  simp only [vertexRestriction, finRotate_apply, Fin.val_ofNat, Fin.val_add, Fin.val_one]
  rw [Nat.mod_mod_of_dvd _ hd]
  exact (Nat.mod_add_mod _ _ _).symm

theorem inverse_rotation_natural (c f : ℕ) (hd : c+2 ∣ f+2) (x : Fin (f+2)) :
    vertexRestriction c f ((finRotate (f+2)).symm x) =
      (finRotate (c+2)).symm (vertexRestriction c f x) := by
  apply (finRotate (c+2)).injective
  rw [Equiv.apply_symm_apply, ← rotation_natural c f hd, Equiv.apply_symm_apply]

theorem motion_natural (c f : ℕ) (hd : c+2 ∣ f+2) (d : Dart f) :
    restriction c f (motion f d) = motion c (restriction c f d) := by
  rcases d with ⟨x,b⟩
  cases b <;> apply Prod.ext
  · exact inverse_rotation_natural c f hd x
  · rfl
  · exact rotation_natural c f hd x
  · rfl

theorem predecessor_natural (c f : ℕ) (hd : c+2 ∣ f+2) (d : Dart f) :
    restriction c f ((motion f).symm d) = (motion c).symm (restriction c f d) := by
  apply (motion c).injective
  rw [Equiv.apply_symm_apply, ← motion_natural c f hd, Equiv.apply_symm_apply]

def fibreChart (k c f : ℕ) (h : f+2 = k*(c+2)) : Fin k × Dart c ≃ Dart f :=
  (Equiv.prodAssoc (Fin k) (Fin (c+2)) Bool).symm.trans
    (Equiv.prodCongr (finProdFinEquiv.trans (finCongr h.symm)) (Equiv.refl Bool))

theorem fibre_projection (k c f : ℕ) (h : f+2 = k*(c+2)) (d : Dart f) :
    ((fibreChart k c f h).symm d).2 = restriction c f d := by
  apply Prod.ext
  · apply Fin.ext; rfl
  · rfl

variable {R : Type*} [CommRing R]

def pullback (c f : ℕ) (v : Dart c → R) : Dart f → R :=
  IntegralTrace.pullback (restriction c f) v

def trace (c f : ℕ) (v : Dart f → R) : Dart c → R :=
  IntegralTrace.trace (restriction c f) v

theorem actual_operator_pullback (c f : ℕ) (hd : c+2 ∣ f+2) (v : Dart c → R) :
    (grover f).mulVec (pullback c f v) = pullback c f ((grover c).mulVec v) := by
  simp only [actual_mulVec, pullback, IntegralTrace.pullback]
  funext d
  exact congrArg v (predecessor_natural c f hd d)

theorem actual_operator_trace (c f : ℕ) (hd : c+2 ∣ f+2) (v : Dart f → R) :
    trace c f ((grover f).mulVec v) = (grover c).mulVec (trace c f v) := by
  simp only [actual_mulVec, trace]
  exact IntegralTrace.trace_action (restriction c f) (motion f) (motion c)
    (motion_natural c f hd) v

theorem trace_pullback_scale (k c f : ℕ) (h : f+2 = k*(c+2)) (v : Dart c → R) :
    trace c f (pullback c f v) = fun d => k • v d := by
  have hp : (fun d => ((fibreChart k c f h).symm d).2) = restriction c f := by
    funext d; exact fibre_projection k c f h d
  simpa only [hp, trace, pullback] using
    IntegralTrace.trace_pullback_scale k (fibreChart k c f h) v

end Holonics.Epime.FiniteCover

#print axioms Holonics.Epime.FiniteCover.actual_operator_pullback
#print axioms Holonics.Epime.FiniteCover.actual_operator_trace
#print axioms Holonics.Epime.FiniteCover.trace_pullback_scale
