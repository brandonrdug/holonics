import Holonics.Compression.Landmark.Context.StoredDrift
import Holonics.Compression.Landmark.Context.Compaction

/-!
# Compression.Landmark.Context.StoredInstance: the arena's read is a `ConsistentTree`

[definition; agent-inferred] The instance map from the compacted executed tree to the full tree
(#62, "the instance map from the arena to `ConsistentTree`"; rebuild step 4, #73).
`Context/StoredDrift` proves its bounds for a `ConsistentTree`: the full tree, one node a depth,
with a stored discrepancy `K` at each node. The Rust stores the tree where paths part
(`Context/Compaction`) and carries, at each stored chain, one ratio `β̂`, so one split mass
`X̂ = (2^(S′) − 1) E/β̂` at its summed rung `S′`. At campaign 1's declared depth `D = 63` this is
the only tree the Rust runs, so every drift bound reaches the executed code through this owner.
The computational object is the helical pair interaction; this owner is the receiving parametron's
landmark tree, executed and stored where it is plural. Of the winding guide's six general objects it
touches the **tower thread** (a chain's implicit nodes are a unique gluing and carry no
discrepancy) and **faces and placement** (the executed weight at each stored level); the helix, the
pair, the cell holonomy and the tube stay attached, unchanged.

```text
routing     E = 1 and nothing reached below an unreached node; a unary node holds its child's counts
read        C(S, s) = E_s at D ;  C(S + j_d, s b) at an implicit node (one reached child b) ;
            (1 − 2^(−S′)) E_s + 2^(−S′) X̂_s at a kept node, S′ = S + j_d          (execFrom)
instance    Ŵ_s = 1 unreached ;  E_s at D ;  (1 − 2^(−j)) E_s + 2^(−j) ∏_b Ŵ(s b) implicit ;
            (1 − 2^(−j)) E_s + 2^(−j) X̂_s kept                                       (instW)
K           K_s = ln X̂_s − ln ∏_b Ŵ(s b) at a reached kept node above D, 0 elsewhere   (instK)
node law    Ŵ_s = (1 − 2^(−j)) E_s + 2^(−j) e^(K_s) ∏_b Ŵ(s b)                       (inst_node)
read = Ŵ    C(S, s) = (1 − 2^(−S)) E_s + 2^(−S) Ŵ_s ,  C(0, s) = Ŵ_s                  (exec_eq)
split       X̂_ℓ kept at β_ℓ ;  (2^(S_up) − 1) E/β_u = (1 − 2^(−S_low)) E + 2^(−S_low) X̂  (split_closed_form)
```

[proved-derived; formal-checked] What is proved.
- `inst_node`, `fullW_node`, `instTree`: the instance with `instK` obeys the executed node law and
  the ideal weight the ideal one, so together they are a `ConsistentTree` with own weight
  `ladder j · E`, split share `2^(−j)`, and the leaf read exactly at `D`.
- `exec_eq`, `instance_read`: the arena's read, entered at a reached node with the rung summed over
  the implicit nodes above it, is `(1 − 2^(−S)) E + 2^(−S) Ŵ`; with no rung above it is the
  instance's executed weight (`Compaction.massCompactFrom_eq`, executed: `chain_ratio` is an
  identity in the bottom's split mass).
- `instK_implicit`: `K = 0` at every implicit node, every unreached node and at `D`: a chain's
  discrepancy sits at its bottom, and a leaf chain reads exactly.
- `instK_exact`, `split_closed_form`: the Rust's two parts (`Law::part`, `Beta::split`) keep the
  lower part's `X̂` and form the upper part's carried split mass as the lower part's executed
  weight, which before the arrival's deposit is the new kept node's children's product (the new
  child weighs one), so the parting node's `K` is `0` before the two roundings; the roundings are
  the discrepancies `StoredDrift.split_charge` reads.

[agent-inferred] **The Rust side.** `execFrom` is `Law::reading`'s weight over the arena (each stored
chain one node at its summed rung `rung_sums`, read at its carried `β̂`); `X̂` is the carried
`β̂`'s split mass at the chain's KT mass (`kt_based`, under the declared base the same at every node
of a unary chain, its counts being its bottom's). A forced depth has rung `0`: a kept node there
reads `X̂` itself, and the Rust passes the face through. The faces and the steps are
`StoredDrift`'s (`level_read_drift`, `carried_step`, `split_effect`).

| Claim | Lean | Rust |
|---|---|---|
| the instance is a `ConsistentTree` | `instTree`, `inst_node`, `fullW_node` | `Landmarks` (its arena), `Law::reading` |
| the arena's read is the instance's weight | `exec_eq`, `instance_read` | `Law::reading`, `rung_sums` |
| the discrepancy at a chain's bottom, leaf chains exact | `instK_implicit` | `Law::leaf`, `Law::chain` |
| the split's closed forms | `split_closed_form`, `instK_exact` | `Law::part`, `Beta::split` |

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Compression.Landmark.Context.StoredInstance

open Finset
open Holonics.Compression.Landmark.Context.Compaction (kidsOf mem_kidsOf)
open Holonics.Compression.Landmark.Context.StoredDrift (ConsistentTree)

variable {Ltr : Type*} [Fintype Ltr]

/-- [definition] **Routing in `ℝ`** (`Compaction.MassRouted`'s weight part): an unreached node's KT
mass is `1` and it has no reached child above `D`; a node with one reached child holds its counts. -/
structure Routing (D : ℕ) (R : List Ltr → Bool) (E : List Ltr → ℝ) : Prop where
  pos : ∀ s, 0 < E s
  absent : ∀ s, R s = false → E s = 1
  closed : ∀ s : List Ltr, s.length < D → R s = false → ∀ b, R (s ++ [b]) = false
  unary : ∀ s : List Ltr, s.length < D → ∀ b0, (∀ b, R (s ++ [b]) = true → b = b0) →
    E (s ++ [b0]) = E s

/-- [definition] **The executed compacted read** (the Rust arena's weight): a chain entered at `s`
with the rung `S` summed above it; an implicit node (one reached child) adds its rung and continues;
a kept node reads its carried split mass `X̂ s` at the summed rung `S′`,
`(1 − 2^(−S′)) E + 2^(−S′) X̂` (the chain's weight `ladder S′ · E + (1 − ladder S′) X̂`, its
carried `β̂ = (2^(S′) − 1) E/X̂`). -/
def execFrom (j : ℕ → ℕ) (R : List Ltr → Bool) (E Xh : List Ltr → ℝ) :
    ℕ → ℕ → List Ltr → ℝ
  | 0, _, s => E s
  | m + 1, S, s =>
    if (kidsOf R s).card = 1 then
      ∑ b ∈ kidsOf R s, execFrom j R E Xh m (S + j s.length) (s ++ [b])
    else
      (1 - (1 / 2 : ℝ) ^ (S + j s.length)) * E s + (1 / 2 : ℝ) ^ (S + j s.length) * Xh s

/-- [definition] **The instance's executed weight on the full tree**: one node a depth, `1` at an
unreached node, the KT mass at `D`, an implicit node composed exactly from its children, a kept node
from its carried `X̂`. -/
def instW (j : ℕ → ℕ) (R : List Ltr → Bool) (E Xh : List Ltr → ℝ) : ℕ → List Ltr → ℝ
  | 0, s => E s
  | m + 1, s =>
    if R s = false then 1 else
      (1 - (1 / 2 : ℝ) ^ j s.length) * E s + (1 / 2 : ℝ) ^ j s.length *
        if (kidsOf R s).card = 1 then ∏ b, instW j R E Xh m (s ++ [b]) else Xh s

/-- [definition] **The ideal weight on the full tree**, one node a depth on the dyadic ladder. -/
def fullW (j : ℕ → ℕ) (R : List Ltr → Bool) (E : List Ltr → ℝ) : ℕ → List Ltr → ℝ
  | 0, s => E s
  | m + 1, s =>
    if R s = false then 1 else
      (1 - (1 / 2 : ℝ) ^ j s.length) * E s + (1 / 2 : ℝ) ^ j s.length *
        ∏ b, fullW j R E m (s ++ [b])

/-- [definition] **The instance's discrepancies**: `K = ln X̂ − ln ∏_b Ŵ(s b)` at a reached kept
node above `D` (the stored chain's bottom), `0` everywhere else. -/
def instK (j : ℕ → ℕ) (R : List Ltr → Bool) (E Xh : List Ltr → ℝ) (D : ℕ) (s : List Ltr) : ℝ :=
  if s.length < D ∧ R s = true ∧ (kidsOf R s).card ≠ 1 then
    Real.log (Xh s) - Real.log (∏ b, instW j R E Xh (D - s.length - 1) (s ++ [b]))
  else 0

variable {D : ℕ} {R : List Ltr → Bool} {E Xh : List Ltr → ℝ} (j : ℕ → ℕ)

theorem half_pow_pos (n : ℕ) : (0 : ℝ) < (1 / 2) ^ n := by positivity

theorem half_pow_le (n : ℕ) : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

/-- An unreached node weighs one, executed and ideal. -/
theorem instW_absent (hR : Routing D R E) :
    ∀ m (s : List Ltr), s.length + m = D → R s = false → instW j R E Xh m s = 1
  | 0, s, _, h => by simp only [instW]; exact hR.absent s h
  | m + 1, s, _, h => by simp only [instW, h, if_true]

theorem fullW_absent (hR : Routing D R E) :
    ∀ m (s : List Ltr), s.length + m = D → R s = false → fullW j R E m s = 1
  | 0, s, _, h => by simp only [fullW]; exact hR.absent s h
  | m + 1, s, _, h => by simp only [fullW, h, if_true]

theorem instW_pos (hR : Routing D R E) (hX : ∀ s, 0 < Xh s) :
    ∀ m (s : List Ltr), 0 < instW j R E Xh m s
  | 0, s => by simp only [instW]; exact hR.pos s
  | m + 1, s => by
    simp only [instW]
    split_ifs
    · norm_num
    · have := half_pow_le (j s.length); have := half_pow_pos (j s.length); have := hR.pos s
      have : 0 < ∏ b, instW j R E Xh m (s ++ [b]) := prod_pos fun b _ => instW_pos hR hX m _
      nlinarith
    · have := half_pow_le (j s.length); have := half_pow_pos (j s.length); have := hR.pos s
      have := hX s
      nlinarith

theorem fullW_pos (hR : Routing D R E) : ∀ m (s : List Ltr), 0 < fullW j R E m s
  | 0, s => by simp only [fullW]; exact hR.pos s
  | m + 1, s => by
    simp only [fullW]
    split_ifs
    · norm_num
    · have := half_pow_le (j s.length); have := half_pow_pos (j s.length); have := hR.pos s
      have : 0 < ∏ b, fullW j R E m (s ++ [b]) := prod_pos fun b _ => fullW_pos hR m _
      nlinarith

/-- [proved-derived] **`inst_node`: the instance obeys the executed node law** with `instK`:
`Ŵ_s = (1 − 2^(−j)) E_s + 2^(−j) e^(K_s) ∏_b Ŵ(s b)` above `D`. An unreached node and an implicit
node carry `K = 0`; a kept node's `e^K ∏_b Ŵ(s b)` is its carried `X̂`. -/
theorem inst_node (hR : Routing D R E) (hX : ∀ s, 0 < Xh s) (m : ℕ) (s : List Ltr)
    (hsm : s.length + m + 1 = D) :
    instW j R E Xh (m + 1) s = (1 - (1 / 2 : ℝ) ^ j s.length) * E s +
      (1 / 2 : ℝ) ^ j s.length *
        (Real.exp (instK j R E Xh D s) * ∏ b, instW j R E Xh m (s ++ [b])) := by
  have hs : s.length < D := by omega
  have hm : D - s.length - 1 = m := by omega
  by_cases hr : R s = false
  · have hK : instK j R E Xh D s = 0 := by
      unfold instK; rw [if_neg]; rintro ⟨-, h, -⟩; simp [hr] at h
    rw [hK, Real.exp_zero, one_mul, hR.absent s hr,
      prod_eq_one fun b _ => instW_absent j hR m (s ++ [b]) (by simp; omega) (hR.closed s hs hr b)]
    simp only [instW, hr, if_true]
    ring
  · have hr' : R s = true := by simpa using hr
    by_cases hc : (kidsOf R s).card = 1
    · have hK : instK j R E Xh D s = 0 := by
        unfold instK; rw [if_neg]; rintro ⟨-, -, h⟩; exact h hc
      rw [hK, Real.exp_zero, one_mul]
      simp only [instW, hr', hc, Bool.true_eq_false, if_true, if_false]
    · have hK : instK j R E Xh D s =
          Real.log (Xh s) - Real.log (∏ b, instW j R E Xh m (s ++ [b])) := by
        unfold instK; rw [if_pos ⟨hs, hr', hc⟩, hm]
      have hP : 0 < ∏ b, instW j R E Xh m (s ++ [b]) :=
        prod_pos fun b _ => instW_pos j hR hX m _
      rw [hK, Real.exp_sub, Real.exp_log (hX s), Real.exp_log hP, div_mul_cancel₀ _ hP.ne']
      simp only [instW, hr', hc, Bool.true_eq_false, if_false]

/-- [proved-derived] **`fullW_node`: the ideal weight obeys the ideal node law.** -/
theorem fullW_node (hR : Routing D R E) (m : ℕ) (s : List Ltr) (hsm : s.length + m + 1 = D) :
    fullW j R E (m + 1) s = (1 - (1 / 2 : ℝ) ^ j s.length) * E s +
      (1 / 2 : ℝ) ^ j s.length * ∏ b, fullW j R E m (s ++ [b]) := by
  have hs : s.length < D := by omega
  by_cases hr : R s = false
  · rw [hR.absent s hr,
      prod_eq_one fun b _ => fullW_absent j hR m (s ++ [b]) (by simp; omega) (hR.closed s hs hr b)]
    simp only [fullW, hr, if_true]
    ring
  · have hr' : R s = true := by simpa using hr
    simp only [fullW, hr', Bool.true_eq_false, if_false]

/-- [proved-derived] **`exec_eq`: the arena's read is the instance's weight.** Entered at a reached
node `s` with the rung `S` summed over the implicit nodes above it, the executed compacted read is
`(1 − 2^(−S)) E_s + 2^(−S) Ŵ_s`: an implicit node's rung joins the chain's sum, a kept node reads
its carried `X̂` (`Compaction.massCompactFrom_eq`, executed). At the root (`S = 0`) it is `Ŵ`. -/
theorem exec_eq (hR : Routing D R E) :
    ∀ m S (s : List Ltr), s.length + m = D → (m = 0 ∨ R s = true) →
      execFrom j R E Xh m S s =
        (1 - (1 / 2 : ℝ) ^ S) * E s + (1 / 2 : ℝ) ^ S * instW j R E Xh m s
  | 0, S, s, _, _ => by simp only [execFrom, instW]; ring
  | m + 1, S, s, hsm, hreach => by
    have hs : s.length < D := by omega
    have hr : R s = true := hreach.resolve_left (by omega)
    rw [execFrom]
    simp only [instW, hr, Bool.true_eq_false, if_false]
    split_ifs with hc
    · obtain ⟨b0, hb0⟩ := Finset.card_eq_one.mp hc
      have hU : ∀ b, R (s ++ [b]) = true → b = b0 := fun b hb => by
        have hmem : b ∈ kidsOf R s := mem_kidsOf.mpr hb
        rw [hb0] at hmem
        exact Finset.mem_singleton.mp hmem
      have hb0r : R (s ++ [b0]) = true := mem_kidsOf.mp (by rw [hb0]; exact mem_singleton_self _)
      rw [hb0, sum_singleton, exec_eq hR m _ (s ++ [b0]) (by simp; omega) (Or.inr hb0r),
        hR.unary s hs b0 hU, prod_eq_single b0]
      · rw [pow_add]; ring
      · intro b _ hb
        have hz : R (s ++ [b]) = false := by
          cases h : R (s ++ [b]) with
          | false => rfl
          | true => exact absurd (hU b h) hb
        exact instW_absent j hR m (s ++ [b]) (by simp; omega) hz
      · simp
    · rw [pow_add]; ring

/-- [definition] **The instance**: the compacted executed tree read as the full tree's
`ConsistentTree`, with the own weight `(1 − 2^(−j)) E` (`ladder j` times the KT mass), the split
share `κ = 2^(−j)`, the discrepancies `instK`, the ideal weight `fullW` and the executed `instW`. -/
def instTree (hR : Routing D R E) (hX : ∀ s, 0 < Xh s) : ConsistentTree Ltr D where
  E s := (1 - (1 / 2 : ℝ) ^ j s.length) * E s
  κ s := (1 / 2 : ℝ) ^ j s.length
  K := instK j R E Xh D
  W s := fullW j R E (D - s.length) s
  Wh s := instW j R E Xh (D - s.length) s
  E_nonneg s := mul_nonneg (by linarith [half_pow_le (j s.length)]) (hR.pos s).le
  κ_pos s := half_pow_pos _
  W_pos s := fullW_pos j hR _ s
  Wh_pos s := instW_pos j hR hX _ s
  W_node s hs := by
    obtain ⟨m, hm⟩ : ∃ m, D - s.length = m + 1 := ⟨D - s.length - 1, by omega⟩
    have hb : ∀ b : Ltr, D - (s ++ [b]).length = m := fun b => by simp; omega
    simp only [hm, hb]
    exact fullW_node j hR m s (by omega)
  Wh_node s hs := by
    obtain ⟨m, hm⟩ : ∃ m, D - s.length = m + 1 := ⟨D - s.length - 1, by omega⟩
    have hb : ∀ b : Ltr, D - (s ++ [b]).length = m := fun b => by simp; omega
    simp only [hm, hb]
    rw [inst_node j hR hX m s (by omega)]
    ring
  leaf s hs := by simp only [hs, Nat.sub_self, instW, fullW]

/-- [proved-derived] **`instK_implicit`: the discrepancy sits only at a stored chain's bottom.**
`K = 0` at every implicit node (one reached child), every unreached node and every node at the
declared depth, so a chain's implicit nodes read exactly and a leaf chain carries no discrepancy. -/
theorem instK_implicit (s : List Ltr)
    (h : D ≤ s.length ∨ R s = false ∨ (kidsOf R s).card = 1) : instK j R E Xh D s = 0 := by
  unfold instK
  rw [if_neg]
  rintro ⟨h1, h2, h3⟩
  rcases h with h | h | h
  · omega
  · simp [h] at h2
  · exact h3 h

/-- [proved-derived] **`instK_exact`: an exactly formed carried split mass has no discrepancy.**
If a kept node's `X̂` is its children's product exactly (a part formed in closed form before its
rounding, `split_closed_form`), `K = 0` there. -/
theorem instK_exact (s : List Ltr)
    (hexact : Xh s = ∏ b, instW j R E Xh (D - s.length - 1) (s ++ [b])) :
    instK j R E Xh D s = 0 := by
  unfold instK
  split_ifs
  · rw [hexact, sub_self]
  · rfl

/-- [proved-derived] **`instance_read`: the arena's read is the instance's executed weight.** At a
reached node, or at the declared depth, the compacted executed read entered with no rung above is
the instance's `Ŵ`; at the root it is the `ConsistentTree`'s executed root weight, so every bound of
`StoredDrift` (`drift_le_tot`, `stored_passage`, `level_read_drift`) applies to it. -/
theorem instance_read (hR : Routing D R E) (hX : ∀ s, 0 < Xh s) (s : List Ltr)
    (hs : s.length ≤ D) (hreach : D = s.length ∨ R s = true) :
    execFrom j R E Xh (D - s.length) 0 s = (instTree j hR hX).Wh s := by
  rw [exec_eq j hR (D - s.length) 0 s (by omega) (hreach.imp (fun h => by omega) id)]
  simp [instTree]

/-- [proved-derived] **`split_closed_form`: the Rust's two parts keep the chain exactly.** A chain
at the summed rung `S = S_up + S_low` with KT mass `E > 0` and carried `β > 0` (`X̂ = (2^S − 1) E/β`)
parts into a lower part at `β_ℓ = β (2^(S_low) − 1)/(2^S − 1)`, which keeps `X̂`, and an upper part
at `β_u = (2^(S_up) − 1) 2^(S_low) β_ℓ/((2^(S_low) − 1)(β_ℓ + 1))` (`Law::part`, `Beta::split`),
whose carried split mass `(2^(S_up) − 1) E/β_u` is the lower part's executed weight
`(1 − 2^(−S_low)) E + 2^(−S_low) X̂`: before either rounding the new kept node's `X̂` is its
children's product (the arrival's new child still weighs one), so `instK_exact` gives `K = 0` there,
and the parts' roundings are the discrepancies `split_charge` reads. -/
theorem split_closed_form {E β : ℝ} (hE : 0 < E) (hβ : 0 < β) {Su Sl : ℕ} (hu : 1 ≤ Su)
    (hl : 1 ≤ Sl) :
    (2 ^ Sl - 1) * E / (β * (2 ^ Sl - 1) / (2 ^ (Su + Sl) - 1)) =
        (2 ^ (Su + Sl) - 1) * E / β ∧
      (2 ^ Su - 1) * E /
          ((2 ^ Su - 1) * 2 ^ Sl * (β * (2 ^ Sl - 1) / (2 ^ (Su + Sl) - 1)) /
            ((2 ^ Sl - 1) * (β * (2 ^ Sl - 1) / (2 ^ (Su + Sl) - 1) + 1))) =
        (1 - (1 / 2 : ℝ) ^ Sl) * E + (1 / 2 : ℝ) ^ Sl * ((2 ^ (Su + Sl) - 1) * E / β) := by
  have hl2 : (1 : ℝ) < 2 ^ Sl := one_lt_pow₀ (by norm_num) (by omega)
  have hu2 : (1 : ℝ) < 2 ^ Su := one_lt_pow₀ (by norm_num) (by omega)
  have hS : (2 : ℝ) ^ (Su + Sl) = 2 ^ Su * 2 ^ Sl := pow_add 2 Su Sl
  have hh : (1 / 2 : ℝ) ^ Sl = 1 / 2 ^ Sl := by rw [one_div_pow]
  have hl0 : (2 : ℝ) ^ Sl - 1 ≠ 0 := by linarith
  have hu0 : (2 : ℝ) ^ Su - 1 ≠ 0 := by linarith
  have hS0 : (2 : ℝ) ^ Su * 2 ^ Sl - 1 ≠ 0 := by nlinarith
  have hp : (2 : ℝ) ^ Sl ≠ 0 := by positivity
  rw [hS, hh]
  have hden : β * (2 ^ Sl - 1) / (2 ^ Su * 2 ^ Sl - 1) + 1 ≠ 0 := by
    have : 0 < β * (2 ^ Sl - 1) / (2 ^ Su * 2 ^ Sl - 1) :=
      div_pos (mul_pos hβ (by linarith)) (by nlinarith)
    linarith
  refine ⟨?_, ?_⟩
  · field_simp
  · field_simp

/-! ### Audit -/

#print axioms inst_node
#print axioms fullW_node
#print axioms exec_eq
#print axioms instK_implicit
#print axioms instK_exact
#print axioms instance_read
#print axioms split_closed_form

end Holonics.Compression.Landmark.Context.StoredInstance
