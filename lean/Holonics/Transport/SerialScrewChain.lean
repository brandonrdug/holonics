import Holonics.Geometry.ScrewGeometry
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Finite exact affine charts for an ordered screw chain

This owner formalizes the finite part of the serial campaign. An affine chart is a rational
linear map followed by a rational translation; composition is ordered and acts on points. A
finite Cayley z chart and a translation chart are supplied as exact matrices. The chain law is
the prefix/product law for these finite actions. No finite chart is silently identified with an
exponential of an infinitesimal screw, and no Jacobian theorem is claimed without a supplied
parameter differential.

[established-bounded; formal-checked] Scope: exact rational affine algebra over `Fin 3`, ordered
finite composition, and translation recharting. General proper-rotation cross-product covariance
and continuous chain derivatives remain the concrete remainder for #62.
-/

open scoped BigOperators Matrix
open Matrix

namespace Holonics.Transport.SerialScrewChain

open Holonics.Geometry.ScrewGeometry

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℚ

/-- A finite exact affine action in the shared rational frame. -/
structure AffineMap3 where
  linear : Mat3
  translation : Vec

/-- Application of an affine chart to a point. -/
def AffineMap3.apply (f : AffineMap3) (x : Vec) : Vec := f.linear *ᵥ x + f.translation

/-- Ordered composition: `compose f g` applies `f`, then `g`. -/
def AffineMap3.compose (f g : AffineMap3) : AffineMap3 where
  linear := g.linear * f.linear
  translation := g.linear *ᵥ f.translation + g.translation

/-- The neutral finite chart. -/
def AffineMap3.identity : AffineMap3 where
  linear := 1
  translation := 0

@[simp] theorem AffineMap3.identity_apply (x : Vec) :
    AffineMap3.identity.apply x = x := by
  simp [AffineMap3.apply, AffineMap3.identity]

@[simp] theorem AffineMap3.compose_identity (f : AffineMap3) :
    f.compose AffineMap3.identity = f := by
  cases f
  simp [AffineMap3.compose, AffineMap3.identity]

@[simp] theorem AffineMap3.identity_compose (f : AffineMap3) :
    AffineMap3.identity.compose f = f := by
  cases f
  simp [AffineMap3.compose, AffineMap3.identity]

/-- [proved-derived; formal-checked] Affine composition acts by function composition. -/
theorem AffineMap3.compose_apply (f g : AffineMap3) (x : Vec) :
    (f.compose g).apply x = g.apply (f.apply x) := by
  simp only [AffineMap3.apply, AffineMap3.compose, Matrix.mulVec_add,
    Matrix.mulVec_mulVec]
  abel

/-- [proved-derived; formal-checked] Ordered affine composition is associative. -/
theorem AffineMap3.compose_assoc (f g h : AffineMap3) :
    (f.compose g).compose h = f.compose (g.compose h) := by
  cases f with
  | mk F f =>
    cases g with
    | mk G g =>
      cases h with
      | mk H h =>
        apply congrArg₂ AffineMap3.mk
        · simp [AffineMap3.compose, Matrix.mul_assoc]
        · simp only [AffineMap3.compose, Matrix.mulVec_mulVec, Matrix.mulVec_add]
          abel

/-- A pure translation chart. -/
def translationChart (t : Vec) : AffineMap3 where
  linear := 1
  translation := t

/-- [proved-derived; formal-checked] Translation charts compose by addition in action order. -/
theorem translationChart_compose (s t : Vec) :
    (translationChart s).compose (translationChart t) = translationChart (s + t) := by
  apply congrArg₂ AffineMap3.mk
  · simp [translationChart]
  · simp [translationChart]

/-- The rational Cayley half-angle circle coordinates. -/
def cayleyCos (q : ℚ) : ℚ := (1 - q ^ 2) / (1 + q ^ 2)

def cayleySin (q : ℚ) : ℚ := (2 * q) / (1 + q ^ 2)

/-- [proved-derived; formal-checked] The Cayley circle coordinates satisfy the unit-circle law.
The parameter is a half-angle chart, not a rational turn rate. -/
theorem cayleyCos_sq_add_sin_sq (q : ℚ) :
    cayleyCos q ^ 2 + cayleySin q ^ 2 = 1 := by
  simp [cayleyCos, cayleySin]
  field_simp
  ring

/-- An exact rational rotation about the shared z axis. -/
def cayleyZChart (q : ℚ) : AffineMap3 where
  linear := !![cayleyCos q, -cayleySin q, 0;
               cayleySin q, cayleyCos q, 0;
               0, 0, 1]
  translation := 0

/-- [proved-derived; formal-checked] The Cayley z chart preserves the Euclidean quadratic form
on its finite rational domain. -/
theorem cayleyZChart_preserves_quad (q : ℚ) (x : Vec) :
    (cayleyZChart q).apply x ⬝ᵥ (cayleyZChart q).apply x = x ⬝ᵥ x := by
  simp [AffineMap3.apply, cayleyZChart, dotProduct, Fin.sum_univ_succ]
  have hc := cayleyCos_sq_add_sin_sq q
  ring_nf
  linear_combination (x 0 ^ 2 + x 1 ^ 2) * hc

/-- The finite ordered configuration of a serial joint list. The list order is the order of
application, so later joints act on the already composed prefix. -/
def configuration : List AffineMap3 → AffineMap3
  | [] => AffineMap3.identity
  | f :: fs => f.compose (configuration fs)

/-- [proved-derived; formal-checked] The configuration of an appended chain is the ordered
composition of its two configurations. -/
theorem configuration_append (xs ys : List AffineMap3) :
    configuration (xs ++ ys) = (configuration xs).compose (configuration ys) := by
  induction xs with
  | nil => simp [configuration, AffineMap3.compose, AffineMap3.identity]
  | cons f xs ih =>
    simp only [List.cons_append, configuration]
    rw [ih, AffineMap3.compose_assoc]

/-- [proved-derived; formal-checked] Applying a serial configuration is the corresponding
ordered prefix action on the initial point. -/
theorem configuration_apply_append (xs ys : List AffineMap3) (x : Vec) :
    (configuration (xs ++ ys)).apply x
      = (configuration ys).apply ((configuration xs).apply x) := by
  rw [configuration_append, AffineMap3.compose_apply]

/-! The native serial convention is kept as a separate owner. Its list is a base-to-tip local-joint
list, while `serialConfiguration [f,g]` applies `f (g x)`: the rightmost local map acts first on
coordinates. It is therefore the reverse of the application-order helper above. -/

/-- The finite local-joint configuration consumed by the serial chain. -/
def serialConfiguration (fs : List AffineMap3) : AffineMap3 := configuration fs.reverse

/-- [proved-derived; formal-checked] A local-joint cons updates the accumulated product on the
right side of the ordered affine word. -/
theorem serialConfiguration_cons (f : AffineMap3) (fs : List AffineMap3) :
    serialConfiguration (f :: fs) = (serialConfiguration fs).compose f := by
  unfold serialConfiguration
  rw [List.reverse_cons, configuration_append]
  simp [configuration]

/-- The fold used by the native serial loop: each local joint updates the accumulated affine
chart by `f.compose acc`. -/
def serialFoldl (base : AffineMap3) (fs : List AffineMap3) : AffineMap3 :=
  fs.foldl (fun acc f => f.compose acc) base

/-- [proved-derived; formal-checked] The native foldl and the finite serial configuration are the
same ordered affine product, for every initial base chart. -/
theorem serialFoldl_eq_configuration (base : AffineMap3) (fs : List AffineMap3) :
    serialFoldl base fs = (serialConfiguration fs).compose base := by
  induction fs generalizing base with
  | nil =>
    change base = AffineMap3.identity.compose base
    simp
  | cons f fs ih =>
    change serialFoldl (f.compose base) fs = (serialConfiguration (f :: fs)).compose base
    rw [ih (base := f.compose base), serialConfiguration_cons, AffineMap3.compose_assoc]

/-- [proved-derived; formal-checked] Local-joint serial products preserve list concatenation,
with the right-hand local segment acting first on coordinates. -/
theorem serialConfiguration_append (xs ys : List AffineMap3) :
    serialConfiguration (xs ++ ys) =
      (serialConfiguration ys).compose (serialConfiguration xs) := by
  induction xs with
  | nil =>
    change configuration ys.reverse = (configuration ys.reverse).compose AffineMap3.identity
    rw [AffineMap3.compose_identity]
  | cons f xs ih =>
    change serialConfiguration (f :: (xs ++ ys)) = _
    rw [serialConfiguration_cons, ih, serialConfiguration_cons, AffineMap3.compose_assoc]

/-- [proved-derived; formal-checked] The local-joint serial endpoint acts by the same ordered
prefix convention as the native affine chart. -/
theorem serialConfiguration_apply_append (xs ys : List AffineMap3) (x : Vec) :
    (serialConfiguration (xs ++ ys)).apply x =
      (serialConfiguration xs).apply ((serialConfiguration ys).apply x) := by
  rw [serialConfiguration_append, AffineMap3.compose_apply]

/-- The accumulated prefix charts, retaining the initial chart as prefix zero. -/
def prefixes : AffineMap3 → List AffineMap3 → List AffineMap3
  | acc, [] => [acc]
  | acc, f :: fs => acc :: prefixes (acc.compose f) fs

/-- [proved-derived; formal-checked] One prefix step advances the accumulated chart by exactly
the next finite joint action. -/
theorem prefixes_succ (acc f : AffineMap3) (fs : List AffineMap3) :
    prefixes acc (f :: fs) = acc :: prefixes (acc.compose f) fs := rfl

/-- Local-joint prefix accumulation used by `serialConfiguration`: adding a joint `f` updates
the current chart to `f.compose acc`. -/
def serialPrefixes : AffineMap3 → List AffineMap3 → List AffineMap3
  | acc, [] => [acc]
  | acc, f :: fs => acc :: serialPrefixes (f.compose acc) fs

/-- [proved-derived; formal-checked] One local-joint prefix step retains the exact affine product
and its action order. -/
theorem serialPrefixes_succ (acc f : AffineMap3) (fs : List AffineMap3) :
    serialPrefixes acc (f :: fs) = acc :: serialPrefixes (f.compose acc) fs := rfl

end Holonics.Transport.SerialScrewChain
