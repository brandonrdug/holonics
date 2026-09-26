import Holonics.Transport.SerialScrewChain
import Mathlib.Tactic

/-!
# Navigator-machine spatial and current charts

This packet is the small chart joining a situated navigator's initial spatial point to its
resident complex current.  A current has real and imaginary `Vec` components; only its real
component enters the spatial chart.  An affine frame acts linearly on both components, while its
anchor correction is real and depends on the source and receiving initial points.

The laws below are exact rational affine algebra.  The frame is supplied by the machine boundary;
this file does not identify a finite affine step with a screw exponential or infer a clock/rate.
Mixtures keep current values and spatial points as separate constructions.  The affine covariance
of a mixture uses the explicit normalization equation `∑ w = 1`.
-/

open scoped BigOperators Matrix
open Matrix

namespace Holonics.Transport.NavigatorMachineCharts

open Holonics.Geometry.ScrewGeometry
open Holonics.Transport.SerialScrewChain

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℚ

/-- The resident current chart at one navigator: three real and three imaginary coordinates. -/
structure ComplexCurrent3 where
  real : Vec
  imaginary : Vec

@[ext] theorem ComplexCurrent3.ext {q₁ q₂ : ComplexCurrent3}
    (hreal : q₁.real = q₂.real) (himag : q₁.imaginary = q₂.imaginary) : q₁ = q₂ := by
  cases q₁
  cases q₂
  simp_all

/-- A navigator's fixed initial spatial point. -/
structure NavigatorSite where
  initial : Vec
  current : ComplexCurrent3

/-- The spatial chart reads the initial point plus the real current component. -/
def spatialChart (p : Vec) (q : ComplexCurrent3) : Vec := p + q.real

/-- The receiving spatial face of a situated navigator site. -/
def NavigatorSite.spatialFace (site : NavigatorSite) : Vec :=
  spatialChart site.initial site.current

/-- The componentwise linear action induced by a spatial matrix. -/
def currentLinear (R : Mat3) (q : ComplexCurrent3) : ComplexCurrent3 where
  real := R *ᵥ q.real
  imaginary := R *ᵥ q.imaginary

/-- The source-to-receiver current map induced by an affine spatial frame.

The bias is the real anchor correction `R p_s + t - p_r`; it is not applied to the imaginary
current directions. -/
def inducedCurrentMap (p_s p_r : Vec) (T : AffineMap3) : ComplexCurrent3 → ComplexCurrent3 :=
  fun q => {
    real := T.linear *ᵥ q.real + (T.linear *ᵥ p_s + T.translation - p_r)
    imaginary := T.linear *ᵥ q.imaginary
  }

@[simp] theorem spatialChart_currentLinear (p : Vec) (R : Mat3) (q : ComplexCurrent3) :
    spatialChart p (currentLinear R q) = p + R *ᵥ q.real := by
  rfl

/-- [proved-derived; formal-checked] The current map realizes its affine spatial transport. -/
theorem spatialChart_inducedCurrentMap (p_s p_r : Vec) (T : AffineMap3)
    (q : ComplexCurrent3) :
    spatialChart p_r (inducedCurrentMap p_s p_r T q) =
      T.apply (spatialChart p_s q) := by
  simp only [spatialChart, inducedCurrentMap, AffineMap3.apply, add_assoc,
    Matrix.mulVec_add]
  abel

/-- [proved-derived; formal-checked] Changing the intermediate initial point gives the expected
ordered composition of induced current maps. -/
theorem inducedCurrentMap_compose (p_s p_m p_r : Vec) (T₁ T₂ : AffineMap3)
    (q : ComplexCurrent3) :
    inducedCurrentMap p_s p_r (T₁.compose T₂) q =
      inducedCurrentMap p_m p_r T₂ (inducedCurrentMap p_s p_m T₁ q) := by
  have hchart :
      spatialChart p_r (inducedCurrentMap p_s p_r (T₁.compose T₂) q) =
        spatialChart p_r
          (inducedCurrentMap p_m p_r T₂ (inducedCurrentMap p_s p_m T₁ q)) := by
    rw [spatialChart_inducedCurrentMap, spatialChart_inducedCurrentMap,
      spatialChart_inducedCurrentMap, AffineMap3.compose_apply]
  apply ComplexCurrent3.ext
  · have hrealChart :
        p_r + (inducedCurrentMap p_s p_r (T₁.compose T₂) q).real =
          p_r + (inducedCurrentMap p_m p_r T₂
            (inducedCurrentMap p_s p_m T₁ q)).real := by
      simpa [spatialChart] using hchart
    exact add_left_cancel hrealChart
  · simp [inducedCurrentMap, AffineMap3.compose, Matrix.mulVec_mulVec]

/-- [proved-derived; formal-checked] The induced identity map leaves both current components
unchanged when source and receiver charts share the same initial point. -/
@[simp] theorem inducedCurrentMap_identity (p : Vec) (q : ComplexCurrent3) :
    inducedCurrentMap p p AffineMap3.identity q = q := by
  apply ComplexCurrent3.ext <;> simp [inducedCurrentMap, AffineMap3.identity]

/-- The current-space pairing is the sum of the real and imaginary Euclidean pairings. -/
def currentPairing (q₁ q₂ : ComplexCurrent3) : ℚ :=
  q₁.real ⬝ᵥ q₂.real + q₁.imaginary ⬝ᵥ q₂.imaginary

/-- The transpose action is the identity-metric adjoint of `currentLinear`. -/
def currentAdjoint (R : Mat3) : ComplexCurrent3 → ComplexCurrent3 :=
  currentLinear Rᵀ

/-- [proved-derived; formal-checked] Real and imaginary channels share the same linear adjoint. -/
theorem currentLinear_pairing_adjoint (R : Mat3) (q₁ q₂ : ComplexCurrent3) :
    currentPairing (currentLinear R q₁) q₂ =
      currentPairing q₁ (currentAdjoint R q₂) := by
  have hreal : (R *ᵥ q₁.real) ⬝ᵥ q₂.real =
      q₁.real ⬝ᵥ (Rᵀ *ᵥ q₂.real) := by
    rw [Matrix.dotProduct_mulVec]
    rw [← Matrix.vecMul_transpose]
  have himag : (R *ᵥ q₁.imaginary) ⬝ᵥ q₂.imaginary =
      q₁.imaginary ⬝ᵥ (Rᵀ *ᵥ q₂.imaginary) := by
    rw [Matrix.dotProduct_mulVec]
    rw [← Matrix.vecMul_transpose]
  simp only [currentPairing, currentLinear, currentAdjoint]
  rw [hreal, himag]

/-! ## Pullback and mixtures -/

/-- A geometry covector on current space has an independent real and imaginary component. -/
structure CurrentCovector where
  real : Vec
  imaginary : Vec

def covectorPairing (q : ComplexCurrent3) (c : CurrentCovector) : ℚ :=
  c.real ⬝ᵥ q.real + c.imaginary ⬝ᵥ q.imaginary

/-- Pulling a spatial covector through the real projection gives no imaginary covector. -/
def realProjectionPullback (geometry : Vec) : CurrentCovector :=
  { real := geometry, imaginary := 0 }

@[simp] theorem realProjectionPullback_imaginary (geometry : Vec) :
    (realProjectionPullback geometry).imaginary = 0 := rfl

@[simp] theorem realProjectionPullback_pairing (geometry : Vec) (q : ComplexCurrent3) :
    covectorPairing q (realProjectionPullback geometry) = geometry ⬝ᵥ q.real := by
  simp [covectorPairing, realProjectionPullback]

def weightedCurrent {ι : Type*} [Fintype ι] (w : ι → ℚ)
    (q : ι → ComplexCurrent3) : ComplexCurrent3 where
  real := ∑ i, w i • (q i).real
  imaginary := ∑ i, w i • (q i).imaginary

/-- A spatial point mixture is kept separate from a current mixture. -/
def weightedPoint {ι : Type*} [Fintype ι] (w : ι → ℚ) (x : ι → Vec) : Vec :=
  ∑ i, w i • x i

/-- [proved-derived; formal-checked] A normalized affine current map commutes with a current
mixture.  The hypothesis is the exact place where the real affine bias cancels. -/
theorem inducedCurrentMap_weightedCurrent_covariant
    {ι : Type*} [Fintype ι] (w : ι → ℚ) (hweight : ∑ i, w i = 1)
    (p_s p_r : Vec) (T : AffineMap3) (q : ι → ComplexCurrent3) :
    weightedCurrent w (fun i => inducedCurrentMap p_s p_r T (q i)) =
      inducedCurrentMap p_s p_r T (weightedCurrent w q) := by
  have hlin (R : Mat3) (x : ι → Vec) :
      (∑ i, w i • (R *ᵥ x i)) = R *ᵥ (∑ i, w i • x i) := by
    rw [Matrix.mulVec_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Matrix.mulVec_smul]
  have hconst (b : Vec) : (∑ i, w i • b) = b := by
    calc
      (∑ i, w i • b) = (∑ i, w i) • b := by
        symm
        simpa using (Finset.sum_smul (s := Finset.univ) (f := w) (x := b))
      _ = b := by rw [hweight, one_smul]
  apply ComplexCurrent3.ext
  · simp only [weightedCurrent, inducedCurrentMap]
    simp_rw [smul_add]
    rw [Finset.sum_add_distrib]
    rw [hlin, hconst]
  · simp only [weightedCurrent, inducedCurrentMap]
    rw [hlin]

/-- [proved-derived; formal-checked] The corresponding spatial point mixture is covariant under
the same affine frame, with current and spatial values remaining distinct. -/
theorem weightedPoint_spatialChart_inducedCurrentMap_covariant
    {ι : Type*} [Fintype ι] (w : ι → ℚ) (hweight : ∑ i, w i = 1)
    (p_s p_r : Vec) (T : AffineMap3) (q : ι → ComplexCurrent3) :
    weightedPoint w (fun i => spatialChart p_r
        (inducedCurrentMap p_s p_r T (q i))) =
      T.apply (weightedPoint w (fun i => spatialChart p_s (q i))) := by
  classical
  simp only [weightedPoint, spatialChart_inducedCurrentMap]
  simp only [AffineMap3.apply]
  simp_rw [smul_add]
  rw [Finset.sum_add_distrib]
  have hlin (R : Mat3) (x : ι → Vec) :
      (∑ i, w i • (R *ᵥ x i)) = R *ᵥ (∑ i, w i • x i) := by
    rw [Matrix.mulVec_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Matrix.mulVec_smul]
  have hconst (b : Vec) : (∑ i, w i • b) = b := by
    calc
      (∑ i, w i • b) = (∑ i, w i) • b := by
        symm
        simpa using (Finset.sum_smul (s := Finset.univ) (f := w) (x := b))
      _ = b := by rw [hweight, one_smul]
  rw [hlin, hconst]

def covectorPullback (R : Mat3) (c : CurrentCovector) : CurrentCovector where
  real := Rᵀ *ᵥ c.real
  imaginary := Rᵀ *ᵥ c.imaginary

/-- [proved-derived; formal-checked] Distinct maps from one source add their pulled-back
covectors exactly as the differential of their summed receiving face. -/
theorem commonSource_sum_pullbacks
    {ι : Type*} [Fintype ι] (w : ι → ℚ) (R : ι → Mat3)
    (c : ι → CurrentCovector) (q : ComplexCurrent3) :
    (∑ i, w i • covectorPairing (currentLinear (R i) q) (c i)) =
      covectorPairing q
        { real := ∑ i, w i • (covectorPullback (R i) (c i)).real
          imaginary := ∑ i, w i • (covectorPullback (R i) (c i)).imaginary } := by
  classical
  simp only [covectorPairing, currentLinear, covectorPullback]
  simp_rw [smul_add]
  rw [Finset.sum_add_distrib]
  have hsum_smul_dot (v : ι → Vec) (z : Vec) :
      (∑ i, w i • (v i ⬝ᵥ z)) = (∑ i, w i • v i) ⬝ᵥ z := by
    rw [sum_dotProduct]
    apply Finset.sum_congr rfl
    intro i hi
    simp [smul_eq_mul]
  rw [show (∑ i, w i • ((c i).real ⬝ᵥ (R i *ᵥ q.real))) =
      (∑ i, w i • ((R i)ᵀ *ᵥ (c i).real)) ⬝ᵥ q.real by
        calc
          (∑ i, w i • ((c i).real ⬝ᵥ (R i *ᵥ q.real))) =
              ∑ i, w i • (((R i)ᵀ *ᵥ (c i).real) ⬝ᵥ q.real) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose]
                simp only [Matrix.transpose_transpose]
          _ = _ := hsum_smul_dot _ _]

  rw [show (∑ i, w i • ((c i).imaginary ⬝ᵥ (R i *ᵥ q.imaginary))) =
      (∑ i, w i • ((R i)ᵀ *ᵥ (c i).imaginary)) ⬝ᵥ q.imaginary by
        calc
          (∑ i, w i • ((c i).imaginary ⬝ᵥ (R i *ᵥ q.imaginary))) =
              ∑ i, w i • (((R i)ᵀ *ᵥ (c i).imaginary) ⬝ᵥ q.imaginary) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose]
                simp only [Matrix.transpose_transpose]
          _ = _ := hsum_smul_dot _ _]

/-! ## Explicit six-real-channel native chart -/

abbrev Flat6 := Fin 6 → ℚ
abbrev Mat6 := Matrix (Fin 6) (Fin 6) ℚ

/-- A native complex channel kept at the rational algebra boundary.  `im = 0` is a source
constraint of the real-coded chart, not a claim about all native complex rows. -/
structure NativeComplexChannel where
  re : ℚ
  im : ℚ

@[ext] theorem NativeComplexChannel.ext {z₁ z₂ : NativeComplexChannel}
    (hre : z₁.re = z₂.re) (him : z₁.im = z₂.im) : z₁ = z₂ := by
  cases z₁
  cases z₂
  simp_all

abbrev NativeComplexRow6 := Fin 6 → NativeComplexChannel

/-- The explicit interleaving order is `(re0, im0, re1, im1, re2, im2)`. -/
def flattenCurrent (q : ComplexCurrent3) : Flat6 :=
  ![q.real 0, q.imaginary 0, q.real 1, q.imaginary 1, q.real 2, q.imaginary 2]

/-- Decode the six real coordinates back into the paired three-channel current. -/
def unflattenCurrent (x : Flat6) : ComplexCurrent3 where
  real := ![x 0, x 2, x 4]
  imaginary := ![x 1, x 3, x 5]

/-- [proved-derived; formal-checked] Flattening and decoding are inverse on the physical current
chart. -/
theorem unflattenCurrent_flattenCurrent (q : ComplexCurrent3) :
    unflattenCurrent (flattenCurrent q) = q := by
  apply ComplexCurrent3.ext <;> funext i <;> fin_cases i <;> rfl

/-- Embed a flattened real row as a native six-complex row with zero native imaginary parts. -/
def nativeEncode (x : Flat6) : NativeComplexRow6 :=
  fun i => { re := x i, im := 0 }

/-- Read the real coordinate of a native row. -/
def nativeDecode (z : NativeComplexRow6) : Flat6 := fun i => (z i).re

/-- The source constraint selecting real-coded native rows. -/
def IsRealCoded (z : NativeComplexRow6) : Prop := ∀ i, (z i).im = 0

@[simp] theorem nativeDecode_encode (x : Flat6) : nativeDecode (nativeEncode x) = x := by
  rfl

/-- [proved-derived; formal-checked] A real-coded native row is exactly recovered by the explicit
encode/decode chart. -/
theorem nativeEncode_decode_of_realCoded (z : NativeComplexRow6)
    (hz : IsRealCoded z) : nativeEncode (nativeDecode z) = z := by
  funext i
  apply NativeComplexChannel.ext
  · rfl
  · simpa [nativeEncode, nativeDecode] using (hz i).symm

/-- Real six-coordinate Euclidean pairing. -/
def flatPairing (x y : Flat6) : ℚ := x ⬝ᵥ y

/-- The native pairing used by the real-coded chart reads only native real coordinates. -/
def nativeRealPairing (z₁ z₂ : NativeComplexRow6) : ℚ :=
  nativeDecode z₁ ⬝ᵥ nativeDecode z₂

/-- [proved-derived; formal-checked] The interleaved chart preserves the real/imaginary current
pairing. -/
theorem flattenCurrent_pairing (q₁ q₂ : ComplexCurrent3) :
    flatPairing (flattenCurrent q₁) (flattenCurrent q₂) = currentPairing q₁ q₂ := by
  simp [flatPairing, flattenCurrent, currentPairing, dotProduct, Fin.sum_univ_succ]
  ring

/-- [proved-derived; formal-checked] The chart preserves the corresponding Euclidean norm. -/
theorem flattenCurrent_norm (q : ComplexCurrent3) :
    flatPairing (flattenCurrent q) (flattenCurrent q) = currentPairing q q := by
  exact flattenCurrent_pairing q q

@[simp] theorem nativeRealPairing_encode (x y : Flat6) :
    nativeRealPairing (nativeEncode x) (nativeEncode y) = flatPairing x y := by
  rfl

/-- Real-linear action on the flattened six-coordinate chart. -/
def flatLinear (A : Mat6) (x : Flat6) : Flat6 := A *ᵥ x

/-- Complexification of a real matrix on a native six-complex row.  The same real coefficients
act independently on the native real and imaginary channel coordinates. -/
def nativeComplexify (A : Mat6) (z : NativeComplexRow6) : NativeComplexRow6 :=
  fun i => {
    re := (A *ᵥ (fun j => (z j).re)) i
    im := (A *ᵥ (fun j => (z j).im)) i
  }

/-- [proved-derived; formal-checked] Realification commutes with a real matrix action on the
real-coded native source chart. -/
theorem nativeComplexify_encode (A : Mat6) (x : Flat6) :
    nativeComplexify A (nativeEncode x) = nativeEncode (flatLinear A x) := by
  funext i
  apply NativeComplexChannel.ext
  · rfl
  · simp [nativeComplexify, nativeEncode, Matrix.mulVec, dotProduct]

/-- [proved-derived; formal-checked] Decoding the real side of a complexified action commutes
with the same real matrix for arbitrary native rows. -/
theorem nativeDecode_complexify (A : Mat6) (z : NativeComplexRow6) :
    nativeDecode (nativeComplexify A z) = flatLinear A (nativeDecode z) := by
  funext i
  rfl

/-- Flatten a current-space covector in the same interleaved order. -/
def flattenCovector (c : CurrentCovector) : Flat6 :=
  ![c.real 0, c.imaginary 0, c.real 1, c.imaginary 1, c.real 2, c.imaginary 2]

@[simp] theorem flattenCurrent_covectorPairing (q : ComplexCurrent3) (c : CurrentCovector) :
    flatPairing (flattenCurrent q) (flattenCovector c) = covectorPairing q c := by
  simp [flatPairing, flattenCurrent, flattenCovector, covectorPairing, dotProduct,
    Fin.sum_univ_succ]
  ring

/-- The real transpose pullback on the flattened source covector chart. -/
def flatCovectorPullback (A : Mat6) (c : Flat6) : Flat6 := Aᵀ *ᵥ c

/-- [proved-derived; formal-checked] A real flattened action pulls back a source covector by the
transpose action, including the original imaginary components in the odd flat slots. -/
theorem flatLinear_pairing_adjoint (A : Mat6) (x c : Flat6) :
    flatPairing (flatLinear A x) c = flatPairing x (flatCovectorPullback A c) := by
  simp only [flatPairing, flatLinear, flatCovectorPullback]
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose]

end Holonics.Transport.NavigatorMachineCharts
