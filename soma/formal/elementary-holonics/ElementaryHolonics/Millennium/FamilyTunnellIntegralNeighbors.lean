import ElementaryHolonics.Millennium.FamilyTunnellProjectiveNeighbors

/-!
# Integral odd-prime neighbor lattices for the Tunnell test vector

The projective conic carrier gives the `p+1` residue directions.  This file lifts
each direction to an actual integral vector whose Tunnell norm is divisible by
`p²`, and then constructs the corresponding rational `p`-neighbor lattice.

The lift is not assumed.  Starting with the normalized residue vector `v₀`, its
norm is `p k`.  In the affine chart we correct the first coordinate by `p t` with
`k + 4t = 0 (mod p)`; in the infinity chart we correct the second coordinate with
`k + 2t = 0 (mod p)`.  These are the two local swings obtained by differentiating
`2x²+y²+Cz²` along the chart pivot.  The corrected norm is then divisible by
`p²` exactly.

The neighbor itself is retained as the addressed rational population

`{m + a v/p | m ∈ ℤ³, B(m,v) = 0 (mod p), a ∈ ℤ}`,

where `B` is the integral polar form.  This is the source carrier needed by the
later Brandt/Hecke double count; no modular-form library object is used.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors

open Soma.Holonics.Millennium.FamilyTunnellProjectiveNeighbors

variable {p : ℕ} [Fact p.Prime]

/-- Integral coordinate triples and their rational ambient realization. -/
abbrev IntTriple := CoordinateTriple ℤ
abbrev RatTriple := CoordinateTriple ℚ

/-- The integral Tunnell quadratic form with third coefficient `C`. -/
def intTunnellQuadratic (C : ℤ) (v : IntTriple) : ℤ :=
  2 * v.1 ^ 2 + v.2.1 ^ 2 + C * v.2.2 ^ 2

/-- Its integral polar form. -/
def intTunnellPolar (C : ℤ) (v w : IntTriple) : ℤ :=
  4 * v.1 * w.1 + 2 * v.2.1 * w.2.1 + 2 * C * v.2.2 * w.2.2

/-- Coordinatewise reduction into the odd-prime receiver. -/
def reduceTriple (v : IntTriple) : CoordinateTriple (ZMod p) :=
  ((v.1 : ZMod p), (v.2.1 : ZMod p), (v.2.2 : ZMod p))

/-- The least-nonnegative integral lift of the normalized projective chart. -/
def baseDirectionLift :
    ((ZMod p × ZMod p) ⊕ ZMod p) → IntTriple
  | .inl q => (1, (q.1.val : ℤ), (q.2.val : ℤ))
  | .inr z => (0, 1, (z.val : ℤ))

/-- The basic lift returns the exact normalized residue vector. -/
theorem reduce_baseDirectionLift
    (d : ((ZMod p × ZMod p) ⊕ ZMod p)) :
    reduceTriple (p := p) (baseDirectionLift d) = projectiveDirectionVector d := by
  cases d with
  | inl q =>
      apply Prod.ext
      · simp [reduceTriple, baseDirectionLift, projectiveDirectionVector]
      · apply Prod.ext <;>
          simp [reduceTriple, baseDirectionLift, projectiveDirectionVector,
            ZMod.natCast_zmod_val]
  | inr z =>
      apply Prod.ext
      · simp [reduceTriple, baseDirectionLift, projectiveDirectionVector]
      · apply Prod.ext <;>
          simp [reduceTriple, baseDirectionLift, projectiveDirectionVector,
            ZMod.natCast_zmod_val]

/-- Reduction commutes with the quadratic receiver. -/
theorem cast_intTunnellQuadratic (C : ℤ) (v : IntTriple) :
    (intTunnellQuadratic C v : ZMod p) =
      reducedTunnellQuadratic (C : ZMod p) (reduceTriple (p := p) v) := by
  simp [intTunnellQuadratic, reducedTunnellQuadratic, reduceTriple]

/-- Isotropy of the projective occurrence means that the basic integral norm has
one complete factor of `p`. -/
theorem prime_dvd_baseDirectionLift_norm (C : ℤ)
    (d : ProjectiveConicDirection (p := p) (C : ZMod p)) :
    (p : ℤ) ∣ intTunnellQuadratic C (baseDirectionLift d.1) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [cast_intTunnellQuadratic, reduce_baseDirectionLift]
  exact projectiveDirectionVector_isotropic d

/-- The first derivative coefficient at either normalized pivot is invertible at
an odd prime. -/
private theorem two_ne_zero (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  apply Ring.two_ne_zero
  rw [ZMod.ringChar_zmod_n]
  exact hp2

private theorem four_ne_zero (hp2 : p ≠ 2) : (4 : ZMod p) ≠ 0 := by
  rw [show (4 : ZMod p) = 2 ^ 2 by norm_num]
  exact pow_ne_zero 2 (two_ne_zero hp2)

/-- An exact integral representative of `-k / derivative` modulo `p`. -/
def pivotCorrection (derivative : ZMod p) (k : ℤ) : ℤ :=
  (((-(k : ZMod p)) / derivative).val : ℤ)

theorem prime_dvd_add_four_pivotCorrection (hp2 : p ≠ 2) (k : ℤ) :
    (p : ℤ) ∣ k + 4 * pivotCorrection (p := p) 4 k := by
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_
  have ht : (pivotCorrection (p := p) 4 k : ZMod p) = -(k : ZMod p) / 4 := by
    simpa [pivotCorrection] using
      ZMod.natCast_zmod_val (-(k : ZMod p) / 4)
  rw [Int.cast_add, Int.cast_mul, Int.cast_ofNat, ht]
  field_simp [four_ne_zero hp2]
  ring

theorem prime_dvd_add_two_pivotCorrection (hp2 : p ≠ 2) (k : ℤ) :
    (p : ℤ) ∣ k + 2 * pivotCorrection (p := p) 2 k := by
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_
  have ht : (pivotCorrection (p := p) 2 k : ZMod p) = -(k : ZMod p) / 2 := by
    simpa [pivotCorrection] using
      ZMod.natCast_zmod_val (-(k : ZMod p) / 2)
  rw [Int.cast_add, Int.cast_mul, Int.cast_ofNat, ht]
  field_simp [two_ne_zero hp2]
  ring

/-- The quotient of the basic norm after its founded first `p` factor. -/
def baseNormQuotient (C : ℤ)
    (d : ProjectiveConicDirection (p := p) (C : ZMod p)) : ℤ :=
  intTunnellQuadratic C (baseDirectionLift d.1) / (p : ℤ)

/-- The chart-pivot correction applied to the integral lift. -/
def adjustedDirectionLift (C : ℤ)
    (d : ProjectiveConicDirection (p := p) (C : ZMod p)) : IntTriple :=
  match d.1 with
  | .inl _ =>
      let t := pivotCorrection (p := p) 4 (baseNormQuotient C d)
      let v := baseDirectionLift d.1
      (v.1 + (p : ℤ) * t, v.2.1, v.2.2)
  | .inr _ =>
      let t := pivotCorrection (p := p) 2 (baseNormQuotient C d)
      let v := baseDirectionLift d.1
      (v.1, v.2.1 + (p : ℤ) * t, v.2.2)

/-- The correction changes no residue coordinate. -/
theorem reduce_adjustedDirectionLift (hp2 : p ≠ 2) (C : ℤ)
    (d : ProjectiveConicDirection (p := p) (C : ZMod p)) :
    reduceTriple (p := p) (adjustedDirectionLift C d) =
      projectiveDirectionVector d.1 := by
  rw [← reduce_baseDirectionLift (p := p) d.1]
  rcases d with ⟨d, hd⟩
  cases d <;>
    simp [adjustedDirectionLift, reduceTriple, baseDirectionLift, ZMod.natCast_self]

/-- **EVERY PROJECTIVE DIRECTION LIFTS TO A `p²`-ISOTROPIC INTEGRAL VECTOR.** -/
theorem prime_sq_dvd_adjustedDirectionLift_norm (hp2 : p ≠ 2) (C : ℤ)
    (d : ProjectiveConicDirection (p := p) (C : ZMod p)) :
    (p : ℤ) ^ 2 ∣ intTunnellQuadratic C (adjustedDirectionLift C d) := by
  have hdiv := prime_dvd_baseDirectionLift_norm (p := p) C d
  have hquotient :
      intTunnellQuadratic C (baseDirectionLift d.1) =
        (p : ℤ) * baseNormQuotient C d := by
    simpa [baseNormQuotient, mul_comm] using (Int.ediv_mul_cancel hdiv).symm
  rcases d with ⟨d, hd⟩
  cases d with
  | inl q =>
      let t := pivotCorrection (p := p) 4
        (baseNormQuotient C ⟨Sum.inl q, hd⟩)
      have ht := prime_dvd_add_four_pivotCorrection (p := p) hp2
        (baseNormQuotient C ⟨Sum.inl q, hd⟩)
      obtain ⟨s, hs⟩ := ht
      change baseNormQuotient C ⟨Sum.inl q, hd⟩ + 4 * t = (p : ℤ) * s at hs
      refine ⟨2 * t ^ 2 + s, ?_⟩
      change intTunnellQuadratic C
          (1 + (p : ℤ) * t, (q.1.val : ℤ), (q.2.val : ℤ)) =
        (p : ℤ) ^ 2 * (2 * t ^ 2 + s)
      have hbase :
          2 * (1 : ℤ) ^ 2 + (q.1.val : ℤ) ^ 2 +
              C * (q.2.val : ℤ) ^ 2 =
            (p : ℤ) * baseNormQuotient C ⟨Sum.inl q, hd⟩ := by
        simpa [intTunnellQuadratic, baseDirectionLift] using hquotient
      calc
        intTunnellQuadratic C
            (1 + (p : ℤ) * t, (q.1.val : ℤ), (q.2.val : ℤ)) =
            (2 * (1 : ℤ) ^ 2 + (q.1.val : ℤ) ^ 2 +
                C * (q.2.val : ℤ) ^ 2) +
              4 * (p : ℤ) * t + 2 * (p : ℤ) ^ 2 * t ^ 2 := by
                unfold intTunnellQuadratic
                ring
        _ = (p : ℤ) * baseNormQuotient C ⟨Sum.inl q, hd⟩ +
              4 * (p : ℤ) * t + 2 * (p : ℤ) ^ 2 * t ^ 2 := by rw [hbase]
        _ =
            (p : ℤ) *
                (baseNormQuotient C ⟨Sum.inl q, hd⟩ + 4 * t) +
              2 * (p : ℤ) ^ 2 * t ^ 2 := by ring
        _ = (p : ℤ) ^ 2 * (2 * t ^ 2 + s) := by rw [hs]; ring
  | inr z =>
      let t := pivotCorrection (p := p) 2
        (baseNormQuotient C ⟨Sum.inr z, hd⟩)
      have ht := prime_dvd_add_two_pivotCorrection (p := p) hp2
        (baseNormQuotient C ⟨Sum.inr z, hd⟩)
      obtain ⟨s, hs⟩ := ht
      change baseNormQuotient C ⟨Sum.inr z, hd⟩ + 2 * t = (p : ℤ) * s at hs
      refine ⟨t ^ 2 + s, ?_⟩
      change intTunnellQuadratic C
          (0, 1 + (p : ℤ) * t, (z.val : ℤ)) =
        (p : ℤ) ^ 2 * (t ^ 2 + s)
      have hbase :
          2 * (0 : ℤ) ^ 2 + (1 : ℤ) ^ 2 + C * (z.val : ℤ) ^ 2 =
            (p : ℤ) * baseNormQuotient C ⟨Sum.inr z, hd⟩ := by
        simpa [intTunnellQuadratic, baseDirectionLift] using hquotient
      calc
        intTunnellQuadratic C
            (0, 1 + (p : ℤ) * t, (z.val : ℤ)) =
            (2 * (0 : ℤ) ^ 2 + (1 : ℤ) ^ 2 + C * (z.val : ℤ) ^ 2) +
              2 * (p : ℤ) * t + (p : ℤ) ^ 2 * t ^ 2 := by
                unfold intTunnellQuadratic
                ring
        _ = (p : ℤ) * baseNormQuotient C ⟨Sum.inr z, hd⟩ +
              2 * (p : ℤ) * t + (p : ℤ) ^ 2 * t ^ 2 := by rw [hbase]
        _ =
            (p : ℤ) *
                (baseNormQuotient C ⟨Sum.inr z, hd⟩ + 2 * t) +
              (p : ℤ) ^ 2 * t ^ 2 := by ring
        _ = (p : ℤ) ^ 2 * (t ^ 2 + s) := by rw [hs]; ring

/-! ## The actual rational neighbor population -/

/-- Coordinatewise rational inclusion. -/
def intTripleToRat (v : IntTriple) : RatTriple :=
  ((v.1 : ℚ), (v.2.1 : ℚ), (v.2.2 : ℚ))

/-- Coordinatewise addition and scalar multiplication, kept explicit to retain the
three addressed lattice coordinates. -/
def ratTripleAdd (v w : RatTriple) : RatTriple :=
  (v.1 + w.1, v.2.1 + w.2.1, v.2.2 + w.2.2)

def ratTripleScale (a : ℚ) (v : RatTriple) : RatTriple :=
  (a * v.1, a * v.2.1, a * v.2.2)

/-- The rational quadratic receiver on the common ambient coordinate space. -/
def ratTunnellQuadratic (C : ℤ) (v : RatTriple) : ℚ :=
  2 * v.1 ^ 2 + v.2.1 ^ 2 + (C : ℚ) * v.2.2 ^ 2

/-- The index-`p` integral kernel cut out by the polar incidence with `v`. -/
def polarKernel (C : ℤ) (v : IntTriple) : Set IntTriple :=
  {m | (p : ℤ) ∣ intTunnellPolar C m v}

/-- Reduction of the integral polar form is twice the reduced half-polar
coordinate pairing.  This is the exact incidence bridge used by neighbor points. -/
theorem cast_intTunnellPolar (C : ℤ) (m v : IntTriple) :
    (intTunnellPolar C m v : ZMod p) =
      2 * (2 * (m.1 : ZMod p) * (v.1 : ZMod p) +
        (m.2.1 : ZMod p) * (v.2.1 : ZMod p) +
        (C : ZMod p) * (m.2.2 : ZMod p) * (v.2.2 : ZMod p)) := by
  simp [intTunnellPolar]
  ring

/-- The rational `p`-neighbor generated by the polar kernel and the corrected
fractional direction.  Its additive closure is proved componentwise; the
occurrence population is not merely named as a set. -/
def integralNeighbor (C : ℤ)
    (d : ProjectiveConicDirection (p := p) (C : ZMod p)) : AddSubgroup RatTriple where
  carrier :=
    {x | ∃ m : IntTriple,
        m ∈ polarKernel (p := p) C (adjustedDirectionLift C d) ∧
        ∃ a : ℤ,
          x = ratTripleAdd (intTripleToRat m)
            (ratTripleScale ((a : ℚ) / (p : ℚ))
              (intTripleToRat (adjustedDirectionLift C d)))}
  zero_mem' := by
    refine ⟨(0, 0, 0), ?_, 0, ?_⟩
    · simp [polarKernel, intTunnellPolar]
    · change (0, 0, 0) = _
      simp [ratTripleAdd, ratTripleScale, intTripleToRat]
  add_mem' := by
    rintro x y ⟨m, hm, a, rfl⟩ ⟨n, hn, b, rfl⟩
    refine ⟨m + n, ?_, a + b, ?_⟩
    · change (p : ℤ) ∣ intTunnellPolar C (m + n) (adjustedDirectionLift C d)
      have hadd :
          (p : ℤ) ∣ intTunnellPolar C m (adjustedDirectionLift C d) +
            intTunnellPolar C n (adjustedDirectionLift C d) := dvd_add hm hn
      convert hadd using 1 <;> simp [intTunnellPolar] <;> ring
    · apply Prod.ext
      · simp [ratTripleAdd, ratTripleScale, intTripleToRat]
        ring
      · apply Prod.ext <;>
          simp [ratTripleAdd, ratTripleScale, intTripleToRat] <;> ring
  neg_mem' := by
    rintro x ⟨m, hm, a, rfl⟩
    refine ⟨-m, ?_, -a, ?_⟩
    · change (p : ℤ) ∣ intTunnellPolar C (-m) (adjustedDirectionLift C d)
      have hneg : (p : ℤ) ∣ -intTunnellPolar C m (adjustedDirectionLift C d) :=
        dvd_neg.mpr hm
      convert hneg using 1 <;> simp [intTunnellPolar] <;> ring
    · apply Prod.ext
      · simp [ratTripleAdd, ratTripleScale, intTripleToRat]
        ring
      · apply Prod.ext <;>
          simp [ratTripleAdd, ratTripleScale, intTripleToRat] <;> ring

/-- The corrected fractional generator is an actual occurrence of its neighbor. -/
theorem fractionalGenerator_mem_integralNeighbor (hp2 : p ≠ 2) (C : ℤ)
    (d : ProjectiveConicDirection (p := p) (C : ZMod p)) :
    ratTripleScale ((1 : ℚ) / (p : ℚ))
        (intTripleToRat (adjustedDirectionLift C d)) ∈
      integralNeighbor (p := p) C d := by
  refine ⟨(0, 0, 0), ?_, 1, ?_⟩
  · simp [polarKernel, intTunnellPolar]
  · simp [ratTripleAdd, intTripleToRat]

/-- An integral vector whose polar reading vanishes modulo `p` is an actual
occurrence of the corresponding rational neighbor (the scalar coordinate is zero). -/
theorem intTripleToRat_mem_integralNeighbor_of_polar_zero (hp2 : p ≠ 2)
    (C : ℤ) (d : ProjectiveConicDirection (p := p) (C : ZMod p))
    (m : IntTriple)
    (hpolar : (intTunnellPolar C m (adjustedDirectionLift C d) : ZMod p) = 0) :
    intTripleToRat m ∈ integralNeighbor (p := p) C d := by
  refine ⟨m, ?_, 0, ?_⟩
  · change (p : ℤ) ∣ intTunnellPolar C m (adjustedDirectionLift C d)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hpolar
  · simp [ratTripleAdd, ratTripleScale, intTripleToRat]

/-- Polarization of the rational neighbor coordinates. -/
theorem ratTunnellQuadratic_neighbor_coordinates (C : ℤ)
    (m v : IntTriple) (a : ℤ) :
    ratTunnellQuadratic C
        (ratTripleAdd (intTripleToRat m)
          (ratTripleScale ((a : ℚ) / (p : ℚ)) (intTripleToRat v))) =
      (intTunnellQuadratic C m : ℚ) +
        ((a : ℚ) / (p : ℚ)) * (intTunnellPolar C m v : ℚ) +
        ((a : ℚ) ^ 2 / (p : ℚ) ^ 2) * (intTunnellQuadratic C v : ℚ) := by
  simp [ratTunnellQuadratic, ratTripleAdd, ratTripleScale, intTripleToRat,
    intTunnellQuadratic, intTunnellPolar]
  ring

/-- **THE QUADRATIC RECEIVER OF EVERY NEIGHBOR OCCURRENCE IS INTEGRAL.**

The first quotient is supplied by the polar-kernel incidence; the second is the
`p²` lift theorem.  No rounding or rational approximation appears. -/
theorem integralNeighbor_norm_is_integer (hp2 : p ≠ 2) (C : ℤ)
    (d : ProjectiveConicDirection (p := p) (C : ZMod p))
    {x : RatTriple} (hx : x ∈ integralNeighbor (p := p) C d) :
    ∃ N : ℤ, ratTunnellQuadratic C x = (N : ℚ) := by
  rcases hx with ⟨m, hm, a, rfl⟩
  change (p : ℤ) ∣ intTunnellPolar C m (adjustedDirectionLift C d) at hm
  obtain ⟨b, hb⟩ := hm
  obtain ⟨q, hq⟩ := prime_sq_dvd_adjustedDirectionLift_norm (p := p) hp2 C d
  refine ⟨intTunnellQuadratic C m + a * b + a ^ 2 * q, ?_⟩
  rw [ratTunnellQuadratic_neighbor_coordinates]
  have hpQ : (p : ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hbQ : (intTunnellPolar C m (adjustedDirectionLift C d) : ℚ) =
      (p : ℚ) * (b : ℚ) := by exact_mod_cast hb
  have hqQ : (intTunnellQuadratic C (adjustedDirectionLift C d) : ℚ) =
      (p : ℚ) ^ 2 * (q : ℚ) := by exact_mod_cast hq
  rw [hbQ, hqQ]
  push_cast
  field_simp

#print axioms prime_dvd_baseDirectionLift_norm
#print axioms prime_sq_dvd_adjustedDirectionLift_norm
#print axioms fractionalGenerator_mem_integralNeighbor
#print axioms integralNeighbor_norm_is_integer

end Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
