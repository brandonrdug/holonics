import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# The exact prime-valuation and radix atlas

[definition] A numeral is a receiver face of a finite causal population.  Changing the radix
changes that face, but it does not authorize rounding the population or replacing it by a nearby
bound.  This file gives the exact return carried by a radix chart:

* `primeValuation n p` is the complete exponent of the prime direction `p` in `n`;
* `ExactRadixChart b n` returns an equality `n = b^k * rho`, together with the proof that `k` is
  the greatest exponent for which `b^k` divides `n`; and
* `AdditivePrimeCaustic p a b` records an exact valuation jump created when two equally situated
  `p`-faces are added.

[proved-derived; formal-checked] The returned residual is terminal, exact radix charts are unique,
every prime coordinate balances through the chart, and an additive caustic transports exactly
through multiplication by a positive common population.  No real number, logarithm, estimate,
rounding convention, or probabilistic choice occurs in the definitions or proofs.
-/

namespace Soma.Holonics.Foundation.PrimeValuationRadixAtlas

/-- [definition] The exponent of the prime direction `p` in the finite population `n`. -/
def primeValuation (n p : ℕ) : ℕ := n.factorization p

/-- [definition] The complete finite prime face of a population. -/
def primeValuationAtlas (n : ℕ) : ℕ →₀ ℕ := n.factorization

@[simp] theorem primeValuationAtlas_apply (n p : ℕ) :
    primeValuationAtlas n p = primeValuation n p := rfl

/-- [proved-derived; formal-checked] The complete prime face reconstructs every nonzero natural
population exactly. -/
theorem thePrimeValuationAtlasReconstructs {n : ℕ} (hn : n ≠ 0) :
    (primeValuationAtlas n).prod (fun p k => p ^ k) = n := by
  exact Nat.factorization_prod_pow_eq_self hn

/-- [proved-derived; formal-checked] Exact divisibility by `p^k`, followed by refusal of
`p^(k+1)`, determines the prime-valuation face without evaluating a factorization algorithm. -/
theorem primeValuation_eq_of_pow_dvd_not_dvd {n p k : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hdiv : p ^ k ∣ n) (hnext : ¬ p ^ (k + 1) ∣ n) : primeValuation n p = k := by
  have hlo : k ≤ n.factorization p := (hp.pow_dvd_iff_le_factorization hn).mp hdiv
  have hhi : ¬ k + 1 ≤ n.factorization p := by
    intro h
    exact hnext ((hp.pow_dvd_iff_le_factorization hn).mpr h)
  unfold primeValuation
  omega

/-- [definition] An exact radix return.  `maximal` makes `depth` a theorem about divisibility,
not a display convention or a chosen magnitude. -/
structure ExactRadixChart (radix value : ℕ) where
  depth : ℕ
  residual : ℕ
  radix_nontrivial : 2 ≤ radix
  value_nonzero : value ≠ 0
  decomposition : value = radix ^ depth * residual
  maximal : ∀ k : ℕ, radix ^ k ∣ value → k ≤ depth

namespace ExactRadixChart

variable {radix value : ℕ}

/-- [proved-derived; formal-checked] The returned radix power really divides the source. -/
theorem theReturnedPowerDivides (C : ExactRadixChart radix value) :
    radix ^ C.depth ∣ value := by
  exact ⟨C.residual, C.decomposition⟩

/-- [proved-derived; formal-checked] A nonzero source has a nonzero exact residual. -/
theorem theResidualIsNonzero (C : ExactRadixChart radix value) : C.residual ≠ 0 := by
  intro h
  apply C.value_nonzero
  rw [C.decomposition, h, mul_zero]

/-- [proved-derived; formal-checked] The residual is terminal: one more whole radix cannot be
removed from it. -/
theorem theResidualIsTerminal (C : ExactRadixChart radix value) : ¬ radix ∣ C.residual := by
  rintro ⟨q, hq⟩
  have hnext : radix ^ (C.depth + 1) ∣ value := by
    refine ⟨q, ?_⟩
    calc
      value = radix ^ C.depth * C.residual := C.decomposition
      _ = radix ^ C.depth * (radix * q) := by rw [hq]
      _ = radix ^ (C.depth + 1) * q := by rw [pow_succ]; ac_rfl
  have := C.maximal (C.depth + 1) hnext
  omega

/-- [proved-derived; formal-checked] Exact charts of one population in one radix have the same
depth and the same residual. -/
theorem theExactChartIsUnique (C D : ExactRadixChart radix value) :
    C.depth = D.depth ∧ C.residual = D.residual := by
  have hCD : C.depth ≤ D.depth := D.maximal C.depth C.theReturnedPowerDivides
  have hDC : D.depth ≤ C.depth := C.maximal D.depth D.theReturnedPowerDivides
  have hd : C.depth = D.depth := Nat.le_antisymm hCD hDC
  refine ⟨hd, ?_⟩
  have hmul : radix ^ C.depth * C.residual = radix ^ C.depth * D.residual := by
    calc
      radix ^ C.depth * C.residual = value := C.decomposition.symm
      _ = radix ^ D.depth * D.residual := D.decomposition
      _ = radix ^ C.depth * D.residual := by rw [hd]
  have hb : radix ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) C.radix_nontrivial)
  exact mul_left_cancel₀ (pow_ne_zero C.depth hb) hmul

/-- [proved-derived; formal-checked] Every prime coordinate is transported exactly through the
radix decomposition. -/
theorem thePrimeValuationBalances (C : ExactRadixChart radix value) (p : ℕ) :
    primeValuation value p =
      C.depth * primeValuation radix p + primeValuation C.residual p := by
  have hr : C.residual ≠ 0 := C.theResidualIsNonzero
  have hb : radix ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) C.radix_nontrivial)
  calc
    primeValuation value p = primeValuation (radix ^ C.depth * C.residual) p :=
      congrArg (fun n => primeValuation n p) C.decomposition
    _ = C.depth * primeValuation radix p + primeValuation C.residual p := by
      simp [primeValuation, Nat.factorization_mul (pow_ne_zero C.depth hb) hr,
        Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply]

/-- [proved-derived; formal-checked] The coordinate laws assemble into equality of the complete
prime-valuation atlases. -/
theorem thePrimeValuationAtlasBalances (C : ExactRadixChart radix value) :
    primeValuationAtlas value =
      C.depth • primeValuationAtlas radix + primeValuationAtlas C.residual := by
  apply Finsupp.ext
  intro p
  simpa [primeValuationAtlas, primeValuation, Finsupp.add_apply, Finsupp.smul_apply] using
    C.thePrimeValuationBalances p

/-- [proved-derived; formal-checked] A prime coordinate of the radix whose valuation already equals
the proposed depth certifies maximality. -/
def ofPrimeWitness {p depth residual : ℕ}
    (hradix : 2 ≤ radix) (hvalue : value ≠ 0)
    (hdecomp : value = radix ^ depth * residual)
    (hp : p.Prime) (hpRadix : p ∣ radix)
    (hpValue : primeValuation value p = depth) : ExactRadixChart radix value where
  depth := depth
  residual := residual
  radix_nontrivial := hradix
  value_nonzero := hvalue
  decomposition := hdecomp
  maximal := by
    intro k hk
    have hpkRadix : p ^ k ∣ radix ^ k := pow_dvd_pow_of_dvd hpRadix k
    have hpkValue : p ^ k ∣ value := hpkRadix.trans hk
    have hkValuation : k ≤ value.factorization p :=
      (hp.pow_dvd_iff_le_factorization hvalue).mp hpkValue
    simpa [primeValuation] using hpValue ▸ hkValuation

end ExactRadixChart

/-- [definition] An additive prime caustic is an exact increase of a prime valuation when two
positive populations occupying the same incoming valuation face are added. -/
structure AdditivePrimeCaustic (p left right entryDepth : ℕ) : Prop where
  prime : p.Prime
  left_positive : 0 < left
  right_positive : 0 < right
  left_entry : primeValuation left p = entryDepth
  right_entry : primeValuation right p = entryDepth
  return_jump : entryDepth < primeValuation (left + right) p

namespace AdditivePrimeCaustic

/-- [proved-derived; formal-checked] Multiplying both incident populations by the same positive
population transports the caustic and adds precisely that population's prime valuation to the
incoming depth. -/
theorem theCausticTransportsThroughCommonScale {p left right entryDepth : ℕ}
    (C : AdditivePrimeCaustic p left right entryDepth) {scale : ℕ} (hscale : 0 < scale) :
    AdditivePrimeCaustic p (scale * left) (scale * right)
      (primeValuation scale p + entryDepth) := by
  have hs : scale ≠ 0 := hscale.ne'
  have hl : left ≠ 0 := C.left_positive.ne'
  have hr : right ≠ 0 := C.right_positive.ne'
  have hlr : left + right ≠ 0 := by omega
  refine
    { prime := C.prime
      left_positive := mul_pos hscale C.left_positive
      right_positive := mul_pos hscale C.right_positive
      left_entry := ?_
      right_entry := ?_
      return_jump := ?_ }
  · calc
      primeValuation (scale * left) p =
          primeValuation scale p + primeValuation left p := by
            simp [primeValuation, Nat.factorization_mul hs hl]
      _ = primeValuation scale p + entryDepth := by rw [C.left_entry]
  · calc
      primeValuation (scale * right) p =
          primeValuation scale p + primeValuation right p := by
            simp [primeValuation, Nat.factorization_mul hs hr]
      _ = primeValuation scale p + entryDepth := by rw [C.right_entry]
  · rw [← Nat.mul_add]
    calc
      primeValuation scale p + entryDepth <
          primeValuation scale p + primeValuation (left + right) p :=
            Nat.add_lt_add_left C.return_jump _
      _ = primeValuation (scale * (left + right)) p := by
        simp [primeValuation, Nat.factorization_mul hs hlr]

end AdditivePrimeCaustic

end Soma.Holonics.Foundation.PrimeValuationRadixAtlas

#print axioms Soma.Holonics.Foundation.PrimeValuationRadixAtlas.primeValuation_eq_of_pow_dvd_not_dvd
#print axioms Soma.Holonics.Foundation.PrimeValuationRadixAtlas.thePrimeValuationAtlasReconstructs
#print axioms Soma.Holonics.Foundation.PrimeValuationRadixAtlas.ExactRadixChart.theResidualIsTerminal
#print axioms Soma.Holonics.Foundation.PrimeValuationRadixAtlas.ExactRadixChart.theExactChartIsUnique
#print axioms Soma.Holonics.Foundation.PrimeValuationRadixAtlas.ExactRadixChart.thePrimeValuationBalances
#print axioms Soma.Holonics.Foundation.PrimeValuationRadixAtlas.ExactRadixChart.thePrimeValuationAtlasBalances
#print axioms Soma.Holonics.Foundation.PrimeValuationRadixAtlas.AdditivePrimeCaustic.theCausticTransportsThroughCommonScale
