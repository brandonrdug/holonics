import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Abel

/-!
# Gyrogroups and the gyroparallelogram completion

This file records the algebraic core needed to speak literally about a
gyroparallelogram.  A `Gyrogroup` owns its operation, zero, inverse, gyration
equivalences, the left gyroassociative law, the gyration-automorphism law, and
the left loop law.  `Gyrocommutative` is an additional property rather than a
silent field of every gyrogroup.

Coaddition and based gyroparallelogram completion are then constructions of
that core.  The final instance proves that every additive commutative group is
the zero-gyration case and that its gyroparallelogram has the familiar fourth
vertex `left + right - source`.
-/

namespace Soma.Holonics

/--
The left-axiomatized algebraic core of a gyrogroup.

The laws are fields because a generic gyrogroup supplies them as structure.
Concrete instances, such as `Gyrogroup.ofAddCommGroup`, must prove each field.
-/
class Gyrogroup (G : Type*) where
  op : G → G → G
  zero : G
  inv : G → G
  gyr : G → G → Equiv G G
  zero_op : ∀ a, op zero a = a
  inv_op : ∀ a, op (inv a) a = zero
  gyroassociative :
    ∀ a b c, op a (op b c) = op (op a b) (gyr a b c)
  gyr_automorphism :
    ∀ a b c d, gyr a b (op c d) = op (gyr a b c) (gyr a b d)
  loop : ∀ a b, gyr a b = gyr (op a b) b

namespace Gyrogroup

variable {G : Type*} [Gyrogroup G]

/-- The gyrocommutative law, retained as a named strengthening of a gyrogroup. -/
def Gyrocommutative : Prop :=
  ∀ a b : G, op a b = gyr a b (op b a)

/--
Gyrogroup coaddition: the right input is first returned through the gyration
determined by the left input and the inverse of the right input.
-/
def coadd (a b : G) : G :=
  op a (gyr a (inv b) b)

/--
The fourth vertex of the gyroparallelogram based at `source`, with adjacent
vertices `left` and `right`.
-/
def gyroparallelogram (source left right : G) : G :=
  op source (coadd (op (inv source) left) (op (inv source) right))

/-- Every additive commutative group is a gyrogroup with identity gyrations. -/
instance ofAddCommGroup (G : Type*) [AddCommGroup G] : Gyrogroup G where
  op := fun a b => a + b
  zero := 0
  inv := fun a => -a
  gyr := fun _ _ => Equiv.refl G
  zero_op := zero_add
  inv_op := neg_add_cancel
  gyroassociative := by
    intro a b c
    simp only [Equiv.refl_apply]
    exact (add_assoc a b c).symm
  gyr_automorphism := by
    intro a b c d
    rfl
  loop := by
    intro a b
    rfl

@[simp]
theorem additive_op {A : Type*} [AddCommGroup A] (a b : A) :
    Gyrogroup.op a b = a + b :=
  rfl

@[simp]
theorem additive_inv {A : Type*} [AddCommGroup A] (a : A) :
    Gyrogroup.inv a = -a :=
  rfl

@[simp]
theorem additive_gyr {A : Type*} [AddCommGroup A] (a b c : A) :
    Gyrogroup.gyr a b c = c :=
  rfl

theorem additive_gyrocommutative (A : Type*) [AddCommGroup A] :
    Gyrocommutative (G := A) := by
  intro a b
  simp only [additive_op, additive_gyr]
  exact add_comm a b

@[simp]
theorem additive_coadd {A : Type*} [AddCommGroup A] (a b : A) :
    coadd a b = a + b := by
  rfl

/--
In the flat zero-gyration instance, the gyroparallelogram is exactly the
ordinary based parallelogram completion.
-/
theorem additive_gyroparallelogram
    {A : Type*} [AddCommGroup A] (source left right : A) :
    gyroparallelogram source left right = left + right - source := by
  simp only [gyroparallelogram, additive_coadd, additive_op, additive_inv]
  abel

#print axioms additive_gyrocommutative
#print axioms additive_coadd
#print axioms additive_gyroparallelogram

end Gyrogroup

end Soma.Holonics
