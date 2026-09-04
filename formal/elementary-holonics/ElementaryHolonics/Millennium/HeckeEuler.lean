import ElementaryHolonics.Millennium.HeckeTheta
import ElementaryHolonics.Millennium.GaussCoefficient
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# HeckeEuler: the coefficient stream is multiplicative

**The Euler structure of the Hecke coefficients**, through the Gaussian integers.  The
shell class `re + im ≡ 1 (mod 4)`, `im` even is rigid under the four units of `ℤ[i]`
and closed under multiplication, and the norm of `gcd(z, m)` for `N(z) = mn` with
`m, n` coprime is exactly `m` — by pure Bézout algebra, no factorization theory:
writing `gcd = z·x + m·y` gives `m ∣ gcd·(gcd)*` because `z·z* = mn`, while the norm
divides `gcd(m², mn) = m`.  The unique class-normalized factorization follows, and
with it the multiplicativity of the shell sums.
-/

namespace Soma.Holonics.Millennium.HeckeEuler

open Finset GaussianInt
open Soma.Holonics.Millennium.HeckeTheta
open Soma.Holonics.Millennium.GaussCoefficient

local notation "ℤ[i]" => GaussianInt

/-- The Hecke class on the Gaussian integers: `re + im ≡ 1 (mod 4)`, `im` even. -/
def inClass (z : ℤ[i]) : Prop := (z.re + z.im) % 4 = 1 ∧ z.im % 2 = 0

instance : DecidablePred inClass := fun z => by unfold inClass; infer_instance

private lemma cast4_of_mod {x r : ℤ} (h : x % 4 = r % 4) : (x : ZMod 4) = (r : ZMod 4) := by
  rw [ZMod.intCast_eq_intCast_iff]
  show x % 4 = r % 4
  exact h

private lemma mod4_of_cast {x r : ℤ} (h : (x : ZMod 4) = (r : ZMod 4)) : x % 4 = r % 4 := by
  rwa [ZMod.intCast_eq_intCast_iff] at h

/-- The class is closed under multiplication. -/
theorem inClass_mul {z w : ℤ[i]} (hz : inClass z) (hw : inClass w) : inClass (z * w) := by
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hw1, hw2⟩ := hw
  have hre : (z * w).re = z.re * w.re - z.im * w.im := by
    rw [Zsqrtd.re_mul]
    ring
  have him : (z * w).im = z.re * w.im + z.im * w.re := by
    rw [Zsqrtd.im_mul]
  constructor
  · rw [hre, him]
    have key : ∀ a b c d : ZMod 4, a + b = 1 → (b = 0 ∨ b = 2) → c + d = 1 →
        (d = 0 ∨ d = 2) → a * c - b * d + (a * d + b * c) = 1 := by decide
    have hb2 : z.im % 4 = 0 ∨ z.im % 4 = 2 := by omega
    have hd2 : w.im % 4 = 0 ∨ w.im % 4 = 2 := by omega
    have hcast := key (z.re : ZMod 4) (z.im : ZMod 4) (w.re : ZMod 4) (w.im : ZMod 4)
      (by
        have h := cast4_of_mod (show (z.re + z.im) % 4 = (1 : ℤ) % 4 by omega)
        push_cast at h
        linear_combination h)
      (by
        rcases hb2 with h | h
        · left
          have h' := cast4_of_mod (show z.im % 4 = (0 : ℤ) % 4 by omega)
          push_cast at h'
          exact h'
        · right
          have h' := cast4_of_mod (show z.im % 4 = (2 : ℤ) % 4 by omega)
          push_cast at h'
          exact h')
      (by
        have h := cast4_of_mod (show (w.re + w.im) % 4 = (1 : ℤ) % 4 by omega)
        push_cast at h
        linear_combination h)
      (by
        rcases hd2 with h | h
        · left
          have h' := cast4_of_mod (show w.im % 4 = (0 : ℤ) % 4 by omega)
          push_cast at h'
          exact h'
        · right
          have h' := cast4_of_mod (show w.im % 4 = (2 : ℤ) % 4 by omega)
          push_cast at h'
          exact h')
    have h4 : ((z.re * w.re - z.im * w.im + (z.re * w.im + z.im * w.re) : ℤ) : ZMod 4)
        = ((1 : ℤ) : ZMod 4) := by
      push_cast
      linear_combination hcast
    have := mod4_of_cast h4
    omega
  · rw [him]
    obtain ⟨u, hu⟩ : ∃ u, z.im = 2 * u := ⟨z.im / 2, by omega⟩
    obtain ⟨v, hv⟩ : ∃ v, w.im = 2 * v := ⟨w.im / 2, by omega⟩
    rw [hu, hv, show z.re * (2 * v) + 2 * u * w.re = 2 * (z.re * v + u * w.re) from by ring]
    omega

/-- The four units of the Gaussian integers, by norm enumeration. -/
private lemma unit_cases {u : ℤ[i]} (hu : IsUnit u) :
    u = 1 ∨ u = -1 ∨ u = ⟨0, 1⟩ ∨ u = ⟨0, -1⟩ := by
  have hn : u.norm = 1 := (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) u).mpr hu
  have hre : u.re * u.re + u.im * u.im = 1 := by
    have h := hn
    rw [Zsqrtd.norm_def] at h
    linarith [h]
  have h1 : -1 ≤ u.re ∧ u.re ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (u.re + 1), sq_nonneg (u.re - 1), sq_nonneg u.im]
  have h2 : -1 ≤ u.im ∧ u.im ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (u.im + 1), sq_nonneg (u.im - 1), sq_nonneg u.re]
  obtain ⟨a, b⟩ := u
  simp only [Zsqrtd.ext_iff]
  obtain ⟨h1l, h1r⟩ := h1
  obtain ⟨h2l, h2r⟩ := h2
  interval_cases a <;> interval_cases b <;> simp_all

/-- **Class rigidity**: on odd norms, no nontrivial unit multiple stays in the class. -/
theorem inClass_rigid {z u : ℤ[i]} (hu : IsUnit u) (hodd : z.norm % 2 = 1)
    (hz : inClass z) (huz : inClass (u * z)) : u = 1 := by
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hu1, hu2⟩ := huz
  have hreodd : z.re % 2 = 1 := by
    rcases Int.even_or_odd z.re with ⟨s, hs⟩ | ⟨s, hs⟩
    · exfalso
      obtain ⟨t, ht⟩ : ∃ t, z.im = 2 * t := ⟨z.im / 2, by omega⟩
      have hnorm : z.norm = 2 * (2 * s * s + 2 * t * t) := by
        rw [Zsqrtd.norm_def, hs, ht]
        ring
      omega
    · omega
  rcases unit_cases hu with rfl | rfl | rfl | rfl
  · rfl
  · exfalso
    have hre : ((-1 : ℤ[i]) * z).re = -z.re := by
      rw [Zsqrtd.re_mul]
      show (-1 : ℤ[i]).re * z.re + (-1) * (-1 : ℤ[i]).im * z.im = -z.re
      norm_num
    have him : ((-1 : ℤ[i]) * z).im = -z.im := by
      rw [Zsqrtd.im_mul]
      show (-1 : ℤ[i]).re * z.im + (-1 : ℤ[i]).im * z.re = -z.im
      norm_num
    rw [hre] at hu1
    rw [him] at hu1
    omega
  · exfalso
    have him : ((⟨0, 1⟩ : ℤ[i]) * z).im = z.re := by
      rw [Zsqrtd.im_mul]
      norm_num
    rw [him] at hu2
    omega
  · exfalso
    have him : ((⟨0, -1⟩ : ℤ[i]) * z).im = -z.re := by
      rw [Zsqrtd.im_mul]
      norm_num
    rw [him] at hu2
    omega

/-- **The norm of the gcd, by Bézout alone**: if `N(z) = mn` with `m, n` coprime, then
`N(gcd(z, m)) = m`.  Writing `gcd = z·A + m·B`, the product `gcd·(gcd)*` expands with
`z·z* = mn` into visibly `m`-divisible terms; the reverse divisibility is the norm law
against `gcd(m², mn) = m`. -/
theorem norm_gcd_eq {z : ℤ[i]} {m n : ℕ} (hmn : Nat.Coprime m n)
    (hz : z.norm = (m : ℤ) * n) :
    (EuclideanDomain.gcd z ((m : ℕ) : ℤ[i])).norm = (m : ℤ) := by
  set d := EuclideanDomain.gcd z ((m : ℕ) : ℤ[i]) with hd_def
  have hdz : d ∣ z := EuclideanDomain.gcd_dvd_left _ _
  have hdm : d ∣ ((m : ℕ) : ℤ[i]) := EuclideanDomain.gcd_dvd_right _ _
  have hnorm_dvd : ∀ {x y : ℤ[i]}, x ∣ y → x.norm ∣ y.norm := by
    rintro x y ⟨e, rfl⟩
    exact ⟨e.norm, Zsqrtd.norm_mul x e⟩
  have h1 : d.norm ∣ (m : ℤ) * m := by
    have h := hnorm_dvd hdm
    rwa [Zsqrtd.norm_natCast] at h
  have h2 : d.norm ∣ (m : ℤ) * n := hz ▸ hnorm_dvd hdz
  have hnn : 0 ≤ d.norm := Zsqrtd.norm_nonneg (by norm_num) d
  have h3 : d.norm ∣ (m : ℤ) := by
    obtain ⟨e, he⟩ : ∃ e : ℕ, d.norm = e := ⟨d.norm.toNat, by omega⟩
    rw [he] at h1 h2 ⊢
    have he1 : e ∣ m * m := by exact_mod_cast h1
    have he2 : e ∣ m * n := by exact_mod_cast h2
    have he3 : e ∣ m := by
      have h := Nat.dvd_gcd he1 he2
      rwa [Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hmn, mul_one] at h
    exact_mod_cast he3
  have h4 : (m : ℤ) ∣ d.norm := by
    have hbez := EuclideanDomain.gcd_eq_gcd_ab z ((m : ℕ) : ℤ[i])
    set A := EuclideanDomain.gcdA z ((m : ℕ) : ℤ[i]) with hA_def
    set B := EuclideanDomain.gcdB z ((m : ℕ) : ℤ[i]) with hB_def
    have hzz : z * star z = (((m : ℤ) * n : ℤ) : ℤ[i]) := by
      rw [← Zsqrtd.norm_eq_mul_conj, hz]
    have hgauss : (((m : ℕ)) : ℤ[i]) ∣ d * star d := by
      rw [show d = z * A + ((m : ℕ) : ℤ[i]) * B from hbez]
      refine ⟨((n : ℕ) : ℤ[i]) * (A * star A) +
        (z * A * star B + star z * star A * B + ((m : ℕ) : ℤ[i]) * (B * star B)), ?_⟩
      have hstar : star (z * A + ((m : ℕ) : ℤ[i]) * B)
          = star z * star A + ((m : ℕ) : ℤ[i]) * star B := by
        rw [star_add, star_mul, star_mul, star_natCast]
        ring
      rw [hstar]
      have hexpand : (z * A + ((m : ℕ) : ℤ[i]) * B) *
          (star z * star A + ((m : ℕ) : ℤ[i]) * star B)
          = (z * star z) * (A * star A) + ((m : ℕ) : ℤ[i]) *
            (z * A * star B + star z * star A * B + ((m : ℕ) : ℤ[i]) * (B * star B)) := by
        ring
      rw [hexpand, hzz]
      have hsplit : (((m : ℤ) * n : ℤ) : ℤ[i]) = ((m : ℕ) : ℤ[i]) * ((n : ℕ) : ℤ[i]) := by
        push_cast
        ring
      rw [hsplit]
      ring
    have hcast : (((m : ℕ) : ℤ) : ℤ[i]) ∣ ((d.norm : ℤ) : ℤ[i]) := by
      rw [Zsqrtd.norm_eq_mul_conj]
      have : (((m : ℕ) : ℤ) : ℤ[i]) = ((m : ℕ) : ℤ[i]) := by push_cast; rfl
      rw [this]
      exact hgauss
    exact (Zsqrtd.intCast_dvd_intCast _ _).mp hcast
  exact Int.dvd_antisymm hnn (Int.natCast_nonneg m) h3 h4

/-- The Gaussian shell: the image of the plane shell in `ℤ[i]`. -/
noncomputable def gShell (m : ℕ) : Finset GaussianInt :=
  (heckeShell m).image fun q => ⟨q.1, q.2⟩

/-- A class element has odd norm. -/
theorem inClass_norm_odd {z : ℤ[i]} (hz : inClass z) : z.norm % 2 = 1 := by
  obtain ⟨h1, h2⟩ := hz
  obtain ⟨t, ht⟩ : ∃ t, z.im = 2 * t := ⟨z.im / 2, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s, z.re = 2 * s + 1 := ⟨(z.re - 1) / 2, by omega⟩
  have hnorm : z.norm = 2 * (2 * s * s + 2 * s + 2 * t * t) + 1 := by
    rw [Zsqrtd.norm_def, hs, ht]
    ring
  omega

lemma mem_gShell {m : ℕ} {z : ℤ[i]} :
    z ∈ gShell m ↔ z.norm = (m : ℤ) ∧ inClass z := by
  rw [gShell, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hq, rfl⟩
    rw [heckeShell, Finset.mem_filter] at hq
    obtain ⟨-, h1, h2, h3⟩ := hq
    refine ⟨?_, h2, h3⟩
    rw [Zsqrtd.norm_def]
    show a * a - -1 * b * b = (m : ℤ)
    linear_combination h1
  · rintro ⟨hn, hc⟩
    obtain ⟨h1, h2⟩ := hc
    have hnorm : z.re ^ 2 + z.im ^ 2 = (m : ℤ) := by
      rw [Zsqrtd.norm_def] at hn
      linear_combination hn
    have hm1 : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
    have hbox : ∀ x y : ℤ, x ^ 2 + y ^ 2 = (m : ℤ) → x ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) := by
      intro x y hxy
      have hx2 : x ^ 2 ≤ (m : ℤ) := by nlinarith [sq_nonneg y]
      rw [Finset.mem_Icc]
      constructor <;> nlinarith [hx2, hm1, sq_nonneg (x + m), sq_nonneg (x - m)]
    refine ⟨(z.re, z.im), ?_, rfl⟩
    rw [heckeShell, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hbox z.re z.im hnorm, hbox z.im z.re (by linarith)⟩, hnorm, h1, h2⟩

private lemma isUnit_I : IsUnit (⟨0, 1⟩ : ℤ[i]) := by
  refine isUnit_iff_exists_inv.mpr ⟨⟨0, -1⟩, ?_⟩
  ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]

private lemma isUnit_negI : IsUnit (⟨0, -1⟩ : ℤ[i]) := by
  refine isUnit_iff_exists_inv.mpr ⟨⟨0, 1⟩, ?_⟩
  ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]

/-- Every odd-norm Gaussian integer has a class-normalized unit associate. -/
theorem exists_class_unit {z : ℤ[i]} (hodd : z.norm % 2 = 1) :
    ∃ u : ℤ[i], IsUnit u ∧ inClass (u * z) := by
  have hpar : (z.re % 2 = 1 ∧ z.im % 2 = 0) ∨ (z.re % 2 = 0 ∧ z.im % 2 = 1) := by
    rcases Int.even_or_odd z.re with ⟨s, hs⟩ | ⟨s, hs⟩ <;>
      rcases Int.even_or_odd z.im with ⟨t, ht⟩ | ⟨t, ht⟩
    · exfalso
      have hnorm : z.norm = 2 * (2 * s * s + 2 * t * t) := by
        rw [Zsqrtd.norm_def, hs, ht]
        ring
      omega
    · right
      omega
    · left
      omega
    · exfalso
      have hnorm : z.norm = 2 * (2 * s * s + 2 * s + 2 * t * t + 2 * t + 1) := by
        rw [Zsqrtd.norm_def, hs, ht]
        ring
      omega
  rcases hpar with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · by_cases hc : (z.re + z.im) % 4 = 1
    · exact ⟨1, isUnit_one, by rw [one_mul]; exact ⟨hc, h2⟩⟩
    · refine ⟨-1, isUnit_one.neg, ?_⟩
      have hre : ((-1 : ℤ[i]) * z).re = -z.re := by
        rw [Zsqrtd.re_mul]
        show (-1 : ℤ[i]).re * z.re + (-1) * (-1 : ℤ[i]).im * z.im = -z.re
        norm_num
      have him : ((-1 : ℤ[i]) * z).im = -z.im := by
        rw [Zsqrtd.im_mul]
        show (-1 : ℤ[i]).re * z.im + (-1 : ℤ[i]).im * z.re = -z.im
        norm_num
      rw [inClass, hre, him]
      constructor
      · omega
      · omega
  · have hreI : ((⟨0, 1⟩ : ℤ[i]) * z).re = -z.im := by
      rw [Zsqrtd.re_mul]
      norm_num
    have himI : ((⟨0, 1⟩ : ℤ[i]) * z).im = z.re := by
      rw [Zsqrtd.im_mul]
      norm_num
    have hreNI : ((⟨0, -1⟩ : ℤ[i]) * z).re = z.im := by
      rw [Zsqrtd.re_mul]
      norm_num
    have himNI : ((⟨0, -1⟩ : ℤ[i]) * z).im = -z.re := by
      rw [Zsqrtd.im_mul]
      norm_num
    by_cases hc : (-z.im + z.re) % 4 = 1
    · refine ⟨⟨0, 1⟩, isUnit_I, ?_⟩
      rw [inClass, hreI, himI]
      exact ⟨hc, by omega⟩
    · refine ⟨⟨0, -1⟩, isUnit_negI, ?_⟩
      rw [inClass, hreNI, himNI]
      exact ⟨by omega, by omega⟩

/-- Coprime norms force coprime elements, through Bézout. -/
private lemma isCoprime_of_norm_coprime {x y : ℤ[i]} {m n : ℕ}
    (hx : x.norm = (m : ℤ)) (hy : y.norm = (n : ℤ)) (hmn : Nat.Coprime m n) :
    IsCoprime x y := by
  set g := EuclideanDomain.gcd x y with hg
  have hnorm_dvd : ∀ {a b : ℤ[i]}, a ∣ b → a.norm ∣ b.norm := by
    rintro a b ⟨e, rfl⟩
    exact ⟨e.norm, Zsqrtd.norm_mul a e⟩
  have h1 : g.norm ∣ (m : ℤ) := hx ▸ hnorm_dvd (EuclideanDomain.gcd_dvd_left _ _)
  have h2 : g.norm ∣ (n : ℤ) := hy ▸ hnorm_dvd (EuclideanDomain.gcd_dvd_right _ _)
  have hnn : 0 ≤ g.norm := Zsqrtd.norm_nonneg (by norm_num) g
  have hg1 : g.norm = 1 := by
    obtain ⟨e, he⟩ : ∃ e : ℕ, g.norm = e := ⟨g.norm.toNat, by omega⟩
    rw [he] at h1 h2 ⊢
    have he1 : e ∣ m := by exact_mod_cast h1
    have he2 : e ∣ n := by exact_mod_cast h2
    have h3 : e ∣ Nat.gcd m n := Nat.dvd_gcd he1 he2
    rw [Nat.Coprime.gcd_eq_one hmn] at h3
    exact_mod_cast Nat.dvd_one.mp h3
  have hu : IsUnit g := (Zsqrtd.norm_eq_one_iff' (by norm_num) g).mp hg1
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
  have hbez := EuclideanDomain.gcd_eq_gcd_ab x y
  refine ⟨v * EuclideanDomain.gcdA x y, v * EuclideanDomain.gcdB x y, ?_⟩
  calc v * EuclideanDomain.gcdA x y * x + v * EuclideanDomain.gcdB x y * y
      = v * (x * EuclideanDomain.gcdA x y + y * EuclideanDomain.gcdB x y) := by ring
    _ = v * g := by rw [← hbez]
    _ = 1 := by rw [mul_comm]; exact hv

private lemma unit_norm_one {u : ℤ[i]} (hu : IsUnit u) : u.norm = 1 :=
  (Zsqrtd.norm_eq_one_iff' (by norm_num) u).mpr hu

/-- **The unique class factorization**: an element of the coprime-product shell splits
uniquely into class factors of the two norms. -/
theorem existsUnique_class_factor {m n : ℕ} (hmn : Nat.Coprime m n) {z : ℤ[i]}
    (hz : z ∈ gShell (m * n)) :
    ∃! q : GaussianInt × GaussianInt,
      q.1 ∈ gShell m ∧ q.2 ∈ gShell n ∧ q.1 * q.2 = z := by
  obtain ⟨hzn, hzc⟩ := mem_gShell.mp hz
  have hodd : z.norm % 2 = 1 := inClass_norm_odd hzc
  have hmn2 : (m * n) % 2 = 1 := by
    have h := hzn ▸ hodd
    exact_mod_cast h
  have hm2 : m % 2 = 1 := by
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · exfalso
      have : m * n = 2 * (k * n) := by rw [hk]; ring
      omega
    · omega
  have hn2 : n % 2 = 1 := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · exfalso
      have : m * n = 2 * (m * k) := by rw [hk]; ring
      omega
    · omega
  have hm0 : (m : ℤ) ≠ 0 := by
    have : m ≠ 0 := by omega
    exact_mod_cast this
  have hznorm : z.norm = (m : ℤ) * n := by rw [hzn]; push_cast; ring
  set d := EuclideanDomain.gcd z ((m : ℕ) : ℤ[i]) with hd_def
  have hdn : d.norm = (m : ℤ) := norm_gcd_eq hmn hznorm
  have hdodd : d.norm % 2 = 1 := by
    rw [hdn]
    omega
  obtain ⟨u, hu, huc⟩ := exists_class_unit hdodd
  set z1 := u * d with hz1_def
  have hz1n : z1.norm = (m : ℤ) := by
    rw [hz1_def, Zsqrtd.norm_mul, unit_norm_one hu, one_mul, hdn]
  have hz1shell : z1 ∈ gShell m := mem_gShell.mpr ⟨hz1n, huc⟩
  obtain ⟨e, he⟩ : d ∣ z := EuclideanDomain.gcd_dvd_left _ _
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
  set z2 := v * e with hz2_def
  have hfac : z1 * z2 = z := by
    rw [hz1_def, hz2_def]
    calc u * d * (v * e) = (u * v) * (d * e) := by ring
      _ = z := by rw [hv, one_mul, ← he]
  have hz2n : z2.norm = (n : ℤ) := by
    have h := congrArg Zsqrtd.norm hfac
    rw [Zsqrtd.norm_mul, hz1n, hznorm] at h
    exact mul_left_cancel₀ hm0 h
  have hz2c : inClass z2 := by
    have hz2odd : z2.norm % 2 = 1 := by
      rw [hz2n]
      omega
    obtain ⟨w, hw, hwc⟩ := exists_class_unit hz2odd
    have hclass : inClass (w * z) := by
      rw [← hfac, show w * (z1 * z2) = z1 * (w * z2) from by ring]
      exact inClass_mul (mem_gShell.mp hz1shell).2 hwc
    have hw1 : w = 1 := inClass_rigid hw hodd hzc hclass
    rwa [hw1, one_mul] at hwc
  have hz2shell : z2 ∈ gShell n := mem_gShell.mpr ⟨hz2n, hz2c⟩
  have hz1ne : z1 ≠ 0 := by
    intro h
    rw [h] at hz1n
    rw [Zsqrtd.norm_zero] at hz1n
    omega
  refine ⟨(z1, z2), ⟨hz1shell, hz2shell, hfac⟩, ?_⟩
  rintro ⟨w1, w2⟩ ⟨hw1s, hw2s, hwfac⟩
  dsimp only at hw1s hw2s hwfac
  obtain ⟨hw1n, hw1c⟩ := mem_gShell.mp hw1s
  obtain ⟨hw2n, hw2c⟩ := mem_gShell.mp hw2s
  have hcop : IsCoprime w1 z2 := isCoprime_of_norm_coprime hw1n hz2n hmn
  have hdvd : w1 ∣ z1 * z2 := by
    rw [hfac, ← hwfac]
    exact dvd_mul_right w1 w2
  have hw1z1 : w1 ∣ z1 := hcop.dvd_of_dvd_mul_right hdvd
  obtain ⟨c, hc⟩ := hw1z1
  have hcu : IsUnit c := by
    have h : (m : ℤ) = Zsqrtd.norm w1 * Zsqrtd.norm c := by
      rw [← hz1n, hc, Zsqrtd.norm_mul]
    rw [hw1n] at h
    have hc1 : c.norm = 1 := by
      have h2 := mul_left_cancel₀ hm0 (show (m : ℤ) * 1 = (m : ℤ) * c.norm from by
        rw [mul_one]
        exact h)
      exact h2.symm
    exact (Zsqrtd.norm_eq_one_iff' (by norm_num) c).mp hc1
  have hw1odd : w1.norm % 2 = 1 := by
    rw [hw1n]
    omega
  have hceq : c = 1 := by
    apply inClass_rigid hcu hw1odd hw1c
    rw [show c * w1 = z1 from by rw [hc]; ring]
    exact (mem_gShell.mp hz1shell).2
  have hz1w1 : z1 = w1 := by rw [hc, hceq, mul_one]
  have hmul : z1 * z2 = z1 * w2 := by rw [hfac, ← hwfac, hz1w1]
  exact Prod.ext_iff.mpr ⟨hz1w1.symm, (mul_left_cancel₀ hz1ne hmul).symm⟩

/-- The Gaussian shell sum. -/
noncomputable def gSum (m : ℕ) : GaussianInt := ∑ z ∈ gShell m, z

private lemma sum_components {α : Type*} (s : Finset α) (f : α → GaussianInt) :
    (∑ z ∈ s, f z) = ⟨∑ z ∈ s, (f z).re, ∑ z ∈ s, (f z).im⟩ := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, Finset.sum_cons, ih]
    rfl

/-- **The shell sum is the coefficient**: the imaginary parts cancel by conjugation. -/
theorem gSum_eq (m : ℕ) : gSum m = ⟨heckeCoeff m, 0⟩ := by
  rw [gSum, gShell, Finset.sum_image (by
    rintro ⟨a, b⟩ - ⟨c, e⟩ - h
    rw [Zsqrtd.ext_iff] at h
    exact Prod.ext_iff.mpr ⟨h.1, h.2⟩)]
  rw [sum_components]
  have hre : (∑ q ∈ heckeShell m, ((⟨q.1, q.2⟩ : GaussianInt)).re) = heckeCoeff m := by
    rw [heckeCoeff]
  have him : (∑ q ∈ heckeShell m, ((⟨q.1, q.2⟩ : GaussianInt)).im) = 0 := by
    have hpt : (∑ q ∈ heckeShell m, ((⟨q.1, q.2⟩ : GaussianInt)).im)
        = ∑ q ∈ heckeShell m, q.2 := Finset.sum_congr rfl fun q _ => rfl
    rw [hpt]
    refine Finset.sum_involution (fun q _ => (q.1, -q.2)) ?_ ?_ ?_ ?_
    · rintro ⟨a, b⟩ ha
      show b + -b = 0
      ring
    · rintro ⟨a, b⟩ ha hb
      intro hcon
      apply hb
      have := congrArg Prod.snd hcon
      dsimp at this
      show b = 0
      omega
    · rintro ⟨a, b⟩ ha
      show (a, -b) ∈ heckeShell m
      rw [heckeShell, Finset.mem_filter, Finset.mem_product] at ha ⊢
      obtain ⟨⟨hb1, hb2⟩, h1, h2, h3⟩ := ha
      refine ⟨⟨hb1, ?_⟩, ?_, ?_, ?_⟩
      · rw [Finset.mem_Icc] at hb2 ⊢
        omega
      · show a ^ 2 + (-b) ^ 2 = (m : ℤ)
        linear_combination h1
      · show (a + -b) % 4 = 1
        omega
      · show (-b) % 2 = 0
        omega
    · rintro ⟨a, b⟩ ha
      show (a, - -b) = (a, b)
      rw [neg_neg]
  rw [hre, him]

/-- **Multiplicativity of the shell sums** across coprime indices. -/
theorem gSum_mul {m n : ℕ} (hmn : Nat.Coprime m n) : gSum (m * n) = gSum m * gSum n := by
  rw [gSum, gSum, gSum, Finset.sum_mul_sum, ← Finset.sum_product']
  refine (Finset.sum_bij (i := fun (q : GaussianInt × GaussianInt)
      (_ : q ∈ gShell m ×ˢ gShell n) => q.1 * q.2) ?_ ?_ ?_ ?_).symm
  · rintro ⟨z1, z2⟩ hq
    rw [Finset.mem_product] at hq
    obtain ⟨h1, h2⟩ := hq
    obtain ⟨h1n, h1c⟩ := mem_gShell.mp h1
    obtain ⟨h2n, h2c⟩ := mem_gShell.mp h2
    refine mem_gShell.mpr ⟨?_, inClass_mul h1c h2c⟩
    rw [Zsqrtd.norm_mul, h1n, h2n]
    push_cast
    ring
  · rintro ⟨z1, z2⟩ hq ⟨w1, w2⟩ hw heq
    rw [Finset.mem_product] at hq hw
    dsimp at heq
    have hz : z1 * z2 ∈ gShell (m * n) := by
      obtain ⟨h1n, h1c⟩ := mem_gShell.mp hq.1
      obtain ⟨h2n, h2c⟩ := mem_gShell.mp hq.2
      refine mem_gShell.mpr ⟨?_, inClass_mul h1c h2c⟩
      rw [Zsqrtd.norm_mul, h1n, h2n]
      push_cast
      ring
    obtain ⟨q0, hq0, huniq⟩ := existsUnique_class_factor hmn hz
    have e1 := huniq (z1, z2) ⟨hq.1, hq.2, rfl⟩
    have e2 := huniq (w1, w2) ⟨hw.1, hw.2, heq.symm⟩
    rw [e1, ← e2]
  · intro z hzs
    obtain ⟨q0, hq0, -⟩ := existsUnique_class_factor hmn hzs
    exact ⟨q0, Finset.mem_product.mpr ⟨hq0.1, hq0.2.1⟩, hq0.2.2⟩
  · rintro ⟨z1, z2⟩ -
    rfl

/-- **The Hecke coefficients are multiplicative** across coprime indices. -/
theorem heckeCoeff_mul {a b : ℕ} (hab : Nat.Coprime a b) :
    heckeCoeff (a * b) = heckeCoeff a * heckeCoeff b := by
  have h := gSum_mul hab
  rw [gSum_eq, gSum_eq, gSum_eq] at h
  have hre := congrArg Zsqrtd.re h
  rw [Zsqrtd.re_mul] at hre
  show heckeCoeff (a * b) = heckeCoeff a * heckeCoeff b
  have : heckeCoeff (a * b) = heckeCoeff a * heckeCoeff b + -1 * 0 * 0 := hre
  linarith [this]

/-- The class representative of the inert prime square: for `p ≡ 3 (mod 4)`,
`⟨−p, 0⟩` is in the class. -/
private lemma inert_rep_inClass {p : ℕ} (hp3 : p % 4 = 3) :
    inClass (⟨-(p : ℤ), 0⟩ : GaussianInt) := by
  constructor
  · show (-(p : ℤ) + 0) % 4 = 1
    omega
  · show (0 : ℤ) % 2 = 0
    omega

/-- Inert descent: for `p ≡ 3 (mod 4)` prime, a Gaussian integer whose norm `p`
divides has both components divisible by `p`. -/
private lemma inert_descend {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3) {z : GaussianInt}
    (hdvd : (p : ℤ) ∣ z.norm) : (p : ℤ) ∣ z.re ∧ (p : ℤ) ∣ z.im := by
  have hns : ¬IsSquare (-1 : ZMod p) := by
    rw [ZMod.exists_sq_eq_neg_one_iff]
    omega
  have hnorm : (p : ℤ) ∣ z.re * z.re + z.im * z.im := by
    have h := hdvd
    rw [Zsqrtd.norm_def] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by linear_combination hc⟩
  have hcast : (z.re : ZMod p) ^ 2 + (z.im : ZMod p) ^ 2 = 0 := by
    have h : ((z.re * z.re + z.im * z.im : ℤ) : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hnorm
    push_cast at h
    linear_combination h
  have him : (z.im : ZMod p) = 0 := by
    by_contra hb
    apply hns
    refine ⟨(z.re : ZMod p) * (z.im : ZMod p)⁻¹, ?_⟩
    have hinv : (z.im : ZMod p) * (z.im : ZMod p)⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ (Ne.isUnit hb)
    have hsq : ((z.re : ZMod p) * (z.im : ZMod p)⁻¹) * ((z.re : ZMod p) * (z.im : ZMod p)⁻¹)
        = ((z.re : ZMod p) ^ 2) * ((z.im : ZMod p)⁻¹ * (z.im : ZMod p)⁻¹) := by
      ring
    rw [hsq]
    have hre2 : (z.re : ZMod p) ^ 2 = -(z.im : ZMod p) ^ 2 := by
      linear_combination hcast
    rw [hre2]
    have : -((z.im : ZMod p) ^ 2) * ((z.im : ZMod p)⁻¹ * (z.im : ZMod p)⁻¹)
        = -(((z.im : ZMod p) * (z.im : ZMod p)⁻¹) * ((z.im : ZMod p) * (z.im : ZMod p)⁻¹)) := by
      ring
    rw [this, hinv]
    ring
  have hre : (z.re : ZMod p) = 0 := by
    rw [him] at hcast
    have h : (z.re : ZMod p) ^ 2 = 0 := by linear_combination hcast
    exact pow_eq_zero_iff (by norm_num) |>.mp h
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd z.re p).mp hre,
    (ZMod.intCast_zmod_eq_zero_iff_dvd z.im p).mp him⟩

open scoped Classical in
/-- Multiplication by a fixed class element sums the divisible part of a shell. -/
private lemma sum_dvd_part {t : GaussianInt} {c k : ℕ} (htn : t.norm = (c : ℤ))
    (htc : inClass t) (ht0 : t ≠ 0) :
    ∑ z ∈ (gShell (c * k)).filter (fun z => t ∣ z), z = t * gSum k := by
  classical
  rw [gSum, Finset.mul_sum]
  refine (Finset.sum_bij (i := fun w (_ : w ∈ gShell k) => t * w) ?_ ?_ ?_ ?_).symm
  · intro w hw
    obtain ⟨hwn, hwc⟩ := mem_gShell.mp hw
    rw [Finset.mem_filter]
    refine ⟨mem_gShell.mpr ⟨?_, inClass_mul htc hwc⟩, Dvd.intro w rfl⟩
    rw [Zsqrtd.norm_mul, htn, hwn]
    push_cast
    ring
  · intro w1 h1 w2 h2 heq
    exact mul_left_cancel₀ ht0 heq
  · intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzs, w, hw⟩ := hz
    obtain ⟨hzn, hzc⟩ := mem_gShell.mp hzs
    have hcne : (c : ℤ) ≠ 0 := by
      intro h
      apply ht0
      rw [← Zsqrtd.norm_eq_zero_iff (by norm_num : (-1 : ℤ) < 0), htn, h]
    have hwn : w.norm = (k : ℤ) := by
      have h := congrArg Zsqrtd.norm hw
      rw [Zsqrtd.norm_mul, htn, hzn] at h
      have h2 : (c : ℤ) * (k : ℤ) = (c : ℤ) * w.norm := by
        rw [← h]
        push_cast
        ring
      exact (mul_left_cancel₀ hcne h2).symm
    have hzodd : z.norm % 2 = 1 := inClass_norm_odd hzc
    have hkodd : k % 2 = 1 := by
      have hck : (c * k) % 2 = 1 := by
        have h := hzn ▸ hzodd
        exact_mod_cast h
      rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · exfalso
        have : c * k = 2 * (c * j) := by rw [hj]; ring
        omega
      · omega
    have hwodd : w.norm % 2 = 1 := by
      rw [hwn]
      omega
    obtain ⟨u, hu, huc⟩ := exists_class_unit hwodd
    have hclass : inClass (u * z) := by
      rw [hw, show u * (t * w) = t * (u * w) from by ring]
      exact inClass_mul htc huc
    have hu1 : u = 1 := inClass_rigid hu hzodd hzc hclass
    exact ⟨w, mem_gShell.mpr ⟨hwn, by rwa [hu1, one_mul] at huc⟩, hw.symm⟩
  · intro w _
    rfl

open scoped Classical in
/-- **The inert recursion**: for `p ≡ 3 (mod 4)` prime,
`c(p^{k+2}) = −p · c(p^k)` — every element of the bigger shell descends through
`⟨−p, 0⟩`. -/
theorem heckeCoeff_prime_pow_inert {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3) (k : ℕ) :
    heckeCoeff (p ^ (k + 2)) = -((p : ℤ)) * heckeCoeff (p ^ k) := by
  classical
  set t : GaussianInt := ⟨-(p : ℤ), 0⟩ with ht_def
  have hp0 : (p : ℤ) ≠ 0 := by
    have := (Fact.out : p.Prime).pos
    positivity
  have htn : t.norm = ((p ^ 2 : ℕ) : ℤ) := by
    rw [ht_def, Zsqrtd.norm_def]
    push_cast
    ring
  have htc : inClass t := inert_rep_inClass hp3
  have ht0 : t ≠ 0 := by
    intro h
    have h2 := congrArg Zsqrtd.re h
    rw [ht_def] at h2
    have h3 : -(p : ℤ) = 0 := h2
    exact hp0 (by linarith)
  have htcast : t = -((p : ℤ) : GaussianInt) := by
    rw [ht_def]
    ext <;> simp
  have hfull : (gShell (p ^ 2 * p ^ k)).filter (fun z => t ∣ z) = gShell (p ^ 2 * p ^ k) := by
    apply Finset.filter_eq_self.mpr
    intro z hz
    obtain ⟨hzn, hzc⟩ := mem_gShell.mp hz
    have hpdvd : (p : ℤ) ∣ z.norm := by
      rw [hzn]
      refine ⟨((p ^ 1 * p ^ k : ℕ) : ℤ), ?_⟩
      push_cast
      ring
    obtain ⟨h1, h2⟩ := inert_descend hp3 hpdvd
    have hcoe : ((p : ℤ) : GaussianInt) ∣ z := (Zsqrtd.intCast_dvd _ _).mpr ⟨h1, h2⟩
    obtain ⟨w, hw⟩ := hcoe
    refine ⟨-w, ?_⟩
    rw [hw, htcast]
    ring
  have hsum := sum_dvd_part (t := t) (c := p ^ 2) (k := p ^ k) htn htc ht0
  rw [hfull] at hsum
  have hpow : p ^ 2 * p ^ k = p ^ (k + 2) := by ring
  rw [hpow] at hsum
  have hgs : gSum (p ^ (k + 2)) = t * gSum (p ^ k) := by
    rw [gSum]
    exact hsum
  rw [gSum_eq, gSum_eq, ht_def] at hgs
  have hre := congrArg Zsqrtd.re hgs
  rw [Zsqrtd.re_mul] at hre
  dsimp only at hre
  linear_combination hre

open scoped Classical in
/-- **The split recursion**: for `p ≡ 1 (mod 4)` prime,
`c(p^{k+2}) + p·c(p^k) = c(p)·c(p^{k+1})` — inclusion–exclusion over divisibility by
the two conjugate class primes above `p`. -/
theorem heckeCoeff_prime_pow_split {p : ℕ} [Fact p.Prime] (hp1 : p % 4 = 1) (k : ℕ) :
    heckeCoeff (p ^ (k + 2)) + (p : ℤ) * heckeCoeff (p ^ k)
      = heckeCoeff p * heckeCoeff (p ^ (k + 1)) := by
  have hp := (Fact.out : p.Prime)
  have hp2 : p ≠ 2 := by omega
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega : p % 4 ≠ 3)
  have hz0n : (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt).norm = (p : ℤ) := by
    rw [Zsqrtd.norm_def]
    have h : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (p : ℤ) := by exact_mod_cast hab
    linear_combination h
  have hz0odd : (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt).norm % 2 = 1 := by
    rw [hz0n]
    omega
  obtain ⟨u, hu, huc⟩ := exists_class_unit hz0odd
  set π : GaussianInt := u * ⟨(a : ℤ), (b : ℤ)⟩ with hπ_def
  have hπn : π.norm = (p : ℤ) := by
    rw [hπ_def, Zsqrtd.norm_mul, unit_norm_one hu, one_mul, hz0n]
  obtain ⟨hπ1, hπ2⟩ := huc
  have hπnorm2 : π.re * π.re + π.im * π.im = (p : ℤ) := by
    have h := hπn
    rw [Zsqrtd.norm_def] at h
    linarith [h]
  have hB0 : π.im ≠ 0 := by
    intro h
    rw [h] at hπnorm2
    have hnat : π.re.natAbs * π.re.natAbs = p := by
      have h2 : π.re * π.re = (p : ℤ) := by linarith
      have h3 := congrArg Int.natAbs h2
      rwa [Int.natAbs_mul, Int.natAbs_natCast] at h3
    have hdvd : π.re.natAbs ∣ p := ⟨π.re.natAbs, hnat.symm⟩
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · rw [h1, one_mul] at hnat
      exact hp.one_lt.ne hnat
    · rw [h1] at hnat
      nlinarith [hnat, hp.one_lt]
  have hstarc : inClass (star π) := by
    constructor
    · rw [Zsqrtd.re_star, Zsqrtd.im_star]
      omega
    · rw [Zsqrtd.im_star]
      omega
  have hstarn : (star π).norm = (p : ℤ) := by
    rw [Zsqrtd.norm_def, Zsqrtd.re_star, Zsqrtd.im_star]
    linear_combination hπnorm2
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, Zsqrtd.norm_zero] at hπn
    exact hp0 hπn.symm
  have hstar0 : star π ≠ 0 := by
    intro h
    rw [h, Zsqrtd.norm_zero] at hstarn
    exact hp0 hstarn.symm
  have hpp : π * star π = (((p : ℤ)) : GaussianInt) := by
    rw [← Zsqrtd.norm_eq_mul_conj, hπn]
  have hpc : inClass (((p : ℤ)) : GaussianInt) := by
    constructor
    · rw [Zsqrtd.re_intCast, Zsqrtd.im_intCast]
      omega
    · rw [Zsqrtd.im_intCast]
      omega
  have hpelt0 : (((p : ℤ)) : GaussianInt) ≠ 0 := by
    intro h
    have h2 := congrArg Zsqrtd.re h
    rw [Zsqrtd.re_intCast] at h2
    exact hp0 h2
  have hcp : heckeCoeff p = 2 * π.re := by
    refine shell_eq hp2 ?_ hπ1 hπ2 hB0
    linear_combination hπnorm2
  have hgsp : gSum p = π + star π := by
    rw [gSum_eq, hcp]
    ext
    · show 2 * π.re = π.re + (star π).re
      rw [Zsqrtd.re_star]
      ring
    · show (0 : ℤ) = π.im + (star π).im
      rw [Zsqrtd.im_star]
      ring
  have hprime_of_norm : ∀ w : GaussianInt, w.norm = (p : ℤ) → Prime w := by
    intro w hwn
    rw [← irreducible_iff_prime]
    constructor
    · intro hu'
      have h := unit_norm_one hu'
      rw [hwn] at h
      have h2 : p = 1 := by exact_mod_cast h
      exact hp.one_lt.ne' h2
    · intro x y hxy
      have hn := congrArg Zsqrtd.norm hxy
      rw [Zsqrtd.norm_mul, hwn] at hn
      have hxn : 0 ≤ x.norm := Zsqrtd.norm_nonneg (by norm_num) x
      have hyn : 0 ≤ y.norm := Zsqrtd.norm_nonneg (by norm_num) y
      obtain ⟨nx, hnx⟩ : ∃ nx : ℕ, x.norm = nx := ⟨x.norm.toNat, by omega⟩
      obtain ⟨ny, hny⟩ : ∃ ny : ℕ, y.norm = ny := ⟨y.norm.toNat, by omega⟩
      have hmulnat : nx * ny = p := by
        have h := hn
        rw [hnx, hny] at h
        exact_mod_cast h.symm
      have hdvd : nx ∣ p := ⟨ny, hmulnat.symm⟩
      rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
      · left
        rw [← Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0), hnx, h1]
        norm_num
      · right
        have hny1 : ny = 1 := by
          rw [h1] at hmulnat
          have := hp.pos
          nlinarith [hmulnat]
        rw [← Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0), hny, hny1]
        norm_num
  have hπprime := hprime_of_norm π hπn
  have hstarprime := hprime_of_norm (star π) hstarn
  have hstar_ndvd : ¬star π ∣ π := by
    rintro ⟨c, hc⟩
    have hn : (p : ℤ) = (p : ℤ) * c.norm := by
      have h0 : π.norm = (star π).norm * c.norm := by
        conv_lhs => rw [hc]
        rw [Zsqrtd.norm_mul]
      rwa [hπn, hstarn] at h0
    have hcu : IsUnit c := by
      rw [← Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0)]
      have hc1 : c.norm = 1 := by
        have h2 := mul_left_cancel₀ hp0 (show (p : ℤ) * 1 = (p : ℤ) * c.norm from by
          rw [mul_one]
          exact hn)
        exact h2.symm
      rw [hc1]
    have hceq : c = 1 := by
      apply inClass_rigid hcu (show (star π).norm % 2 = 1 from by rw [hstarn]; omega) hstarc
      have hcs : c * star π = π := by
        conv_rhs => rw [hc]
        ring
      rw [hcs]
      exact ⟨hπ1, hπ2⟩
    rw [hceq, mul_one] at hc
    have h := congrArg Zsqrtd.im hc
    rw [Zsqrtd.im_star] at h
    omega
  have hcover : ∀ z ∈ gShell (p ^ (k + 2)), π ∣ z ∨ star π ∣ z := by
    intro z hz
    obtain ⟨hzn, hzc⟩ := mem_gShell.mp hz
    have hπp : π ∣ (((p : ℤ)) : GaussianInt) := ⟨star π, hpp.symm⟩
    have hpz : (((p : ℤ)) : GaussianInt) ∣ ((z.norm : ℤ) : GaussianInt) := by
      rw [Zsqrtd.intCast_dvd_intCast, hzn]
      refine ⟨((p ^ (k + 1) : ℕ) : ℤ), ?_⟩
      push_cast
      ring
    have hzz : π ∣ z * star z := by
      have h := hπp.trans hpz
      rwa [Zsqrtd.norm_eq_mul_conj] at h
    rcases hπprime.2.2 _ _ hzz with h | h
    · exact Or.inl h
    · right
      obtain ⟨c, hc⟩ := h
      refine ⟨star c, ?_⟩
      have h2 := congrArg star hc
      rw [star_star, star_mul'] at h2
      exact h2
  have hinter_mem : ∀ z : GaussianInt, (π ∣ z ∧ star π ∣ z) →
      (((p : ℤ)) : GaussianInt) ∣ z := by
    rintro z ⟨⟨c, hc⟩, hstar⟩
    rcases hstarprime.2.2 π c (hc ▸ hstar) with h | h
    · exact absurd h hstar_ndvd
    · obtain ⟨e, he⟩ := h
      refine ⟨e, ?_⟩
      rw [hc, he, ← hpp]
      ring
  have hinter_mem' : ∀ z : GaussianInt, (((p : ℤ)) : GaussianInt) ∣ z →
      (π ∣ z ∧ star π ∣ z) := by
    rintro z ⟨c, hc⟩
    exact ⟨⟨star π * c, by rw [hc, ← hpp]; ring⟩, ⟨π * c, by rw [hc, ← hpp]; ring⟩⟩
  have hpow1 : p * p ^ (k + 1) = p ^ (k + 2) := by ring
  have hpow2 : p ^ 2 * p ^ k = p ^ (k + 2) := by ring
  have hsumA : ∑ z ∈ (gShell (p ^ (k + 2))).filter (fun z => π ∣ z), z
      = π * gSum (p ^ (k + 1)) := by
    have h := sum_dvd_part (t := π) (c := p) (k := p ^ (k + 1)) hπn ⟨hπ1, hπ2⟩ hπ0
    rwa [hpow1] at h
  have hsumB : ∑ z ∈ (gShell (p ^ (k + 2))).filter (fun z => star π ∣ z), z
      = star π * gSum (p ^ (k + 1)) := by
    have h := sum_dvd_part (t := star π) (c := p) (k := p ^ (k + 1)) hstarn hstarc hstar0
    rwa [hpow1] at h
  have hsumP : ∑ z ∈ (gShell (p ^ (k + 2))).filter
      (fun z => (((p : ℤ)) : GaussianInt) ∣ z), z
      = (((p : ℤ)) : GaussianInt) * gSum (p ^ k) := by
    have hn2 : ((((p : ℤ)) : GaussianInt)).norm = ((p ^ 2 : ℕ) : ℤ) := by
      rw [Zsqrtd.norm_intCast]
      push_cast
      ring
    have h := sum_dvd_part (t := (((p : ℤ)) : GaussianInt)) (c := p ^ 2) (k := p ^ k)
      hn2 hpc hpelt0
    rwa [hpow2] at h
  have hunion : (gShell (p ^ (k + 2))).filter (fun z => π ∣ z) ∪
      (gShell (p ^ (k + 2))).filter (fun z => star π ∣ z) = gShell (p ^ (k + 2)) := by
    apply Finset.Subset.antisymm
    · intro z hz
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hz
      rcases hz with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h
    · intro z hz
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases hcover z hz with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
  have hinter : (gShell (p ^ (k + 2))).filter (fun z => π ∣ z) ∩
      (gShell (p ^ (k + 2))).filter (fun z => star π ∣ z)
      = (gShell (p ^ (k + 2))).filter (fun z => (((p : ℤ)) : GaussianInt) ∣ z) := by
    ext z
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hzs, h1⟩, ⟨-, h2⟩⟩
      exact ⟨hzs, hinter_mem z ⟨h1, h2⟩⟩
    · rintro ⟨hzs, h⟩
      obtain ⟨h1, h2⟩ := hinter_mem' z h
      exact ⟨⟨hzs, h1⟩, ⟨hzs, h2⟩⟩
  have hkey := Finset.sum_union_inter
    (s₁ := (gShell (p ^ (k + 2))).filter (fun z => π ∣ z))
    (s₂ := (gShell (p ^ (k + 2))).filter (fun z => star π ∣ z))
    (f := fun z => z)
  rw [hunion, hinter, hsumA, hsumB, hsumP] at hkey
  have hfinal : gSum (p ^ (k + 2)) + (((p : ℤ)) : GaussianInt) * gSum (p ^ k)
      = gSum p * gSum (p ^ (k + 1)) := by
    rw [hgsp, gSum]
    linear_combination hkey
  rw [gSum_eq, gSum_eq, gSum_eq, gSum_eq] at hfinal
  have hre := congrArg Zsqrtd.re hfinal
  rw [Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]
    at hre
  dsimp only at hre
  linear_combination hre

/-- **The Euler recursion at every odd prime**, unified: on the blind frames the
coefficient vanishes and the inert descent carries the law; on the sighted frames the
split inclusion–exclusion carries it. -/
theorem heckeCoeff_prime_pow_recursion {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (k : ℕ) :
    heckeCoeff (p ^ (k + 2))
      = heckeCoeff p * heckeCoeff (p ^ (k + 1)) - (p : ℤ) * heckeCoeff (p ^ k) := by
  have hodd : p % 2 = 1 := (Fact.out : p.Prime).eq_two_or_odd.resolve_left hp2
  have h14 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases h14 with h | h
  · have := heckeCoeff_prime_pow_split h k
    linarith
  · rw [heckeCoeff_prime_pow_inert h k, heckeCoeff_three_mod_four h]
    ring

end Soma.Holonics.Millennium.HeckeEuler
