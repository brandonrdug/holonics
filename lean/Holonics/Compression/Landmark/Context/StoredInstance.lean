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
the read    β̂ = (2^(S′) − 1) E/X = E_c/Q ,  E_c = (1 − 2^(−S′)) E ,  Q = 2^(−S′) X ,  C(S, s) = E_c + Q
            λ = β̂/(1 + β̂) = E_c/C(S, s) ;  λ k + (1 − λ) q = (E_c k + Q q)/C(S, s)        (read_level, read_face)
            X = X̂ at a kept node, C(0, s b) at a cut ;  C(S + T, s) = (1 − 2^(−S)) E + 2^(−S) C(T, s)  (exec_shift)
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

[proved-derived; formal-checked] **The arena's read** (`storedRead`, `Law::read`'s loop exact
before its roundings). The read walks only the stored levels: an implicit node the address follows
adds its rung and continues (`storedRead_levels`). At a stored level (a kept node, or a node the
address parts from, where `Law::part` cuts the chain) it mixes the node's KT face with the face below
at the stop weight of the chain's carried `β̂ = betaOf S′ E X`; `X` is the carried `X̂`, or at a cut
the lower part's executed weight (`rustX`). That stop weight is `execFrom`'s own share,
`E_c/C(S, s)` (`read_level`; at a cut through `exec_shift`), so the level's face is
`(E_c k + Q q)/C(S, s)` (`read_face`, `storedRead_stored`): `StoredDrift.level_read_drift`'s centre
with `E = E_c`, `E' = E_c k`, `Q = 2^(−S′) X`. A summed rung `0` passes its face through
(`stop_pass`), as the Rust skips a level whose bottom lies above the forced depths. The Rust's two
stop-weight numerators are `β/(1 + β)` before rounding (`stop_numerators`), and its β step
`β' = β u/(v x)` keeps `β̂ = betaOf S′ E X̂` through a deposit (`beta_step`). The roundings (the stop
weight's and the face's) are `Drift`'s `θ`.

[agent-inferred] **The Rust side.** `storedRead` is `Law::read` over the arena: its levels are the
walk's stored nodes (`Standing::walk`), each at its summed rung (`rung_sum`) and carried `β̂`; a
parting chain's level reads its upper part's chart (`parting.upper`); `bottoms[level] < forced` is
`S′ = 0`; `Stop::Node` is the leaf's face at `D`, `Stop::Prior` the base's split `k₀`. `X̂` is the
carried `β̂`'s split mass at the chain's KT mass (`kt_based`, under the declared base the same at
every node of a unary chain, its counts being its bottom's). The faces and the steps are
`StoredDrift`'s (`level_read_drift`, `carried_step`, `split_effect`).

| Claim | Lean | Rust |
|---|---|---|
| the instance is a `ConsistentTree` | `instTree`, `inst_node`, `fullW_node` | `Landmarks` (its arena), `Law::reading` |
| the arena's read is the instance's weight | `exec_eq`, `instance_read` | `Law::reading`, `rung_sums` |
| the discrepancy at a chain's bottom, leaf chains exact | `instK_implicit` | `Law::leaf`, `Law::chain` |
| the split's closed forms | `split_closed_form`, `instK_exact` | `Law::part`, `Beta::split` |
| the read's levels and stop weights | `storedRead`, `storedRead_levels`, `storedRead_stored`, `read_level`, `read_face`, `exec_shift`, `stop_beta`, `stop_pass` | `Law::read`, `Law::mix_stop`, `rung_sum` |
| the stop weight and the β step | `stop_numerators`, `beta_step` | `Beta::stop_weight`, `carried_step` |

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

/-! ### The arena's read: `Law::read` over the stored levels -/

/-- [definition] **A chain's carried `β`** at the summed rung `S`, KT mass `E` and carried split
mass `X̂`: `β̂ = (2^S − 1) E/X̂` (`Beta`; founded at `2^S − 1` over a leaf, `Law::chain`). -/
def betaOf (S : ℕ) (E X : ℝ) : ℝ := (2 ^ S - 1) * E / X

/-- [definition] **The stop weight** `λ = β/(1 + β)` (`Beta::stop_weight` before its rounding). -/
def stopOf (β : ℝ) : ℝ := β / (1 + β)

/-- [definition] **The split mass the Rust reads at a stored level**: a kept node's carried `X̂`;
at a node the address parts from (a cut chain, `Law::part`), the lower part's executed weight. -/
def rustX (j : ℕ → ℕ) (R : List Ltr → Bool) (E Xh : List Ltr → ℝ) (m : ℕ) (s : List Ltr) : ℝ :=
  if (kidsOf R s).card = 1 then ∑ b ∈ kidsOf R s, execFrom j R E Xh m 0 (s ++ [b]) else Xh s

/-- [definition] **The Rust's read** (`Law::read`, exact before its roundings) along the address
`a`, entered at depth `d` with `m` levels below and the rung `S` summed above: an implicit node the
address follows is no stored level (the chain continues, its rung joining the sum); at a stored
level the face mixes the node's KT face `k` with the face below at the stop weight of the chain's
carried `β̂`; the face below is the next stored chain's read, entered afresh, or the base's split
`k₀` past the last stored level (`Stop::Prior`); at `D` the leaf's face (`Stop::Node`). -/
def storedRead (j : ℕ → ℕ) (R : List Ltr → Bool) (E Xh k : List Ltr → ℝ) (k₀ : ℝ)
    (a : List Ltr) : ℕ → ℕ → ℕ → ℝ
  | 0, _, d => k (a.take d)
  | m + 1, S, d =>
    if (kidsOf R (a.take d)).card = 1 ∧ R (a.take (d + 1)) = true then
      storedRead j R E Xh k k₀ a m (S + j (a.take d).length) (d + 1)
    else
      stopOf (betaOf (S + j (a.take d).length) (E (a.take d)) (rustX j R E Xh m (a.take d))) *
          k (a.take d) +
        (1 - stopOf (betaOf (S + j (a.take d).length) (E (a.take d))
          (rustX j R E Xh m (a.take d)))) *
          if R (a.take (d + 1)) = true then storedRead j R E Xh k k₀ a m 0 (d + 1) else k₀

/-- [proved-derived] **`stop_numerators`: the Rust's two stop-weight forms are `β/(1 + β)`.** For
`β = a 2^e/b`, `e ≥ 0`: `1 − b/(a 2^e + b)`; for `β = a/(b 2^e)`: `a/(a + b 2^e)`
(`Beta::stop_weight`'s `2^M − 2^M b/g` and `2^M a/h`, before rounding). -/
theorem stop_numerators {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (ht : 0 < t) :
    1 - b / (a * t + b) = stopOf (a * t / b) ∧ a / (a + b * t) = stopOf (a / (b * t)) := by
  have h1 : 0 < a * t + b := by positivity
  have h2 : 0 < a + b * t := by positivity
  unfold stopOf
  constructor <;> field_simp <;> ring

/-- [proved-derived] **`stop_beta`: the stop weight of a chain's carried `β̂` is its own share.**
`β̂/(1 + β̂) = (1 − 2^(−S)) E/((1 − 2^(−S)) E + 2^(−S) X̂)`; `β̂ = E_c/Q` with the chain's own weight
`E_c = (1 − 2^(−S)) E` and split mass `Q = 2^(−S) X̂` (`Drift.face_weight_form`'s `β̂ = E/Q`). -/
theorem stop_beta {E X : ℝ} (hE : 0 < E) (hX : 0 < X) (S : ℕ) :
    betaOf S E X = (1 - (1 / 2 : ℝ) ^ S) * E / ((1 / 2 : ℝ) ^ S * X) ∧
      stopOf (betaOf S E X) =
        (1 - (1 / 2 : ℝ) ^ S) * E / ((1 - (1 / 2 : ℝ) ^ S) * E + (1 / 2 : ℝ) ^ S * X) := by
  have ht := half_pow_pos S
  have ht1 := half_pow_le S
  have h2 : (2 : ℝ) ^ S = 1 / (1 / 2) ^ S := by rw [one_div_pow, one_div_one_div]
  have hb : betaOf S E X = (1 - (1 / 2 : ℝ) ^ S) * E / ((1 / 2 : ℝ) ^ S * X) := by
    unfold betaOf; rw [h2]; field_simp
  refine ⟨hb, ?_⟩
  have hden : 0 < (1 - (1 / 2 : ℝ) ^ S) * E + (1 / 2 : ℝ) ^ S * X := by
    have : 0 ≤ (1 - (1 / 2 : ℝ) ^ S) * E := mul_nonneg (by linarith) hE.le
    have : 0 < (1 / 2 : ℝ) ^ S * X := mul_pos ht hX
    linarith
  have hQ : 0 < (1 / 2 : ℝ) ^ S * X := mul_pos ht hX
  rw [stopOf, hb]
  generalize (1 - (1 / 2 : ℝ) ^ S) * E = Ec at hden ⊢
  generalize (1 / 2 : ℝ) ^ S * X = Q at hden hQ ⊢
  have h1 : 1 + Ec / Q = (Ec + Q) / Q := by field_simp; ring
  rw [h1, div_div_div_cancel_right₀ hQ.ne']

/-- [proved-derived] **`stop_mix`: a stored level's face is the executed mixture.** At the stop
weight `λ = E_c/(E_c + Q)`, `λ k + (1 − λ) q = (E_c k + Q q)/(E_c + Q)`: the centre of
`StoredDrift.level_read_drift`'s `hround`, with `E' = E_c k`. -/
theorem stop_mix {Ec Q k q : ℝ} (h : 0 < Ec + Q) :
    Ec / (Ec + Q) * k + (1 - Ec / (Ec + Q)) * q = (Ec * k + Q * q) / (Ec + Q) := by
  field_simp
  ring

/-- [proved-derived] **`stop_pass`: at a summed rung `0` the level passes its face through.**
`β̂ = 0`, `λ = 0` (`Law::read` skips a level whose bottom lies above the forced depths). -/
theorem stop_pass (E X k q : ℝ) :
    stopOf (betaOf 0 E X) * k + (1 - stopOf (betaOf 0 E X)) * q = q := by
  simp [stopOf, betaOf]

/-- [proved-derived] **`beta_step`: the Rust's β step keeps the chain's correspondence.** With the
KT mass stepped by its face `k` and the split mass by the child's face `x`,
`β̂' = β̂ k/x` (`carried_step`'s `β' = β u/(v x)`, before its rebase). -/
theorem beta_step {E X k x : ℝ} (hX : X ≠ 0) (hx : x ≠ 0) (S : ℕ) :
    betaOf S (E * k) (X * x) = betaOf S E X * k / x := by
  unfold betaOf
  field_simp

theorem execFrom_pos (hR : Routing D R E) (hX : ∀ s, 0 < Xh s) :
    ∀ m S (s : List Ltr), 0 < execFrom j R E Xh m S s
  | 0, _, s => by simp only [execFrom]; exact hR.pos s
  | m + 1, S, s => by
    rw [execFrom]
    split_ifs with hc
    · obtain ⟨b0, hb0⟩ := Finset.card_eq_one.mp hc
      rw [hb0, sum_singleton]
      exact execFrom_pos hR hX m _ _
    · have := half_pow_le (S + j s.length); have := half_pow_pos (S + j s.length)
      have := hR.pos s; have := hX s
      nlinarith

/-- [proved-derived] **`exec_shift`: a rung summed above a chain is one node over it.**
`C(S + T, s) = (1 − 2^(−S)) E_s + 2^(−S) C(T, s)` (a unary chain's nodes hold its bottom's counts):
a chain cut anywhere is its upper part at its own rung over the lower part's weight. -/
theorem exec_shift (hR : Routing D R E) :
    ∀ m S T (s : List Ltr), s.length + m = D →
      execFrom j R E Xh m (S + T) s =
        (1 - (1 / 2 : ℝ) ^ S) * E s + (1 / 2 : ℝ) ^ S * execFrom j R E Xh m T s
  | 0, S, T, s, _ => by simp only [execFrom]; ring
  | m + 1, S, T, s, hsm => by
    have hs : s.length < D := by omega
    simp only [execFrom]
    split_ifs with hc
    · obtain ⟨b0, hb0⟩ := Finset.card_eq_one.mp hc
      have hU : ∀ b, R (s ++ [b]) = true → b = b0 := fun b hb => by
        have hmem : b ∈ kidsOf R s := mem_kidsOf.mpr hb
        rw [hb0] at hmem
        exact Finset.mem_singleton.mp hmem
      rw [hb0, sum_singleton, sum_singleton, add_assoc,
        exec_shift hR m S (T + j s.length) (s ++ [b0]) (by simp; omega), hR.unary s hs b0 hU]
    · rw [add_assoc, pow_add]; ring

/-- [proved-derived] **`read_level`: `Law::read`'s stop weight at a stored level is `execFrom`'s
own share.** At a stored level `s` (a kept node, or a node the address parts from) entered with the
rung `S`, `S′ = S + j_|s|`: the chain's executed weight is `E_c + 2^(−S′) X` with `E_c =
(1 − 2^(−S′)) E_s` and `X` the split mass the Rust reads (`rustX`: the carried `X̂`, or at a cut the
lower part's weight, `exec_shift`), and the stop weight of the carried `β̂ = betaOf S′ E_s X` is
`E_c/C(S, s)`. -/
theorem read_level (hR : Routing D R E) (hX : ∀ s, 0 < Xh s) (m S : ℕ) (s : List Ltr)
    (hsm : s.length + m + 1 = D) :
    execFrom j R E Xh (m + 1) S s =
        (1 - (1 / 2 : ℝ) ^ (S + j s.length)) * E s +
          (1 / 2 : ℝ) ^ (S + j s.length) * rustX j R E Xh m s ∧
      stopOf (betaOf (S + j s.length) (E s) (rustX j R E Xh m s)) =
        (1 - (1 / 2 : ℝ) ^ (S + j s.length)) * E s / execFrom j R E Xh (m + 1) S s := by
  have hs : s.length < D := by omega
  have hXpos : 0 < rustX j R E Xh m s := by
    unfold rustX
    split_ifs with hc
    · obtain ⟨b0, hb0⟩ := Finset.card_eq_one.mp hc
      rw [hb0, sum_singleton]; exact execFrom_pos j hR hX m 0 _
    · exact hX s
  have hC : execFrom j R E Xh (m + 1) S s =
      (1 - (1 / 2 : ℝ) ^ (S + j s.length)) * E s +
        (1 / 2 : ℝ) ^ (S + j s.length) * rustX j R E Xh m s := by
    unfold rustX
    simp only [execFrom]
    split_ifs with hc
    · obtain ⟨b0, hb0⟩ := Finset.card_eq_one.mp hc
      have hU : ∀ b, R (s ++ [b]) = true → b = b0 := fun b hb => by
        have hmem : b ∈ kidsOf R s := mem_kidsOf.mpr hb
        rw [hb0] at hmem
        exact Finset.mem_singleton.mp hmem
      rw [hb0, sum_singleton, sum_singleton,
        show S + j s.length = S + j s.length + 0 by rfl,
        exec_shift j hR m (S + j s.length) 0 (s ++ [b0]) (by simp; omega), hR.unary s hs b0 hU]
      simp only [add_zero]
    · rfl
  refine ⟨hC, ?_⟩
  rw [(stop_beta (hR.pos s) hXpos _).2, hC]

/-- [proved-derived] **`read_face`: a stored level of `Law::read` is the executed mixture over
`execFrom`.** Its face is `(E_c k + Q q)/(E_c + Q)` with `E_c + Q = C(S, s)` the chain's executed
weight (`read_level`), so `StoredDrift.level_read_drift` reads the Rust's levels with
`E = E_c`, `E' = E_c k`, `Q = 2^(−S′) X`; at `S′ = 0` the level passes its face through
(`stop_pass`). -/
theorem read_face (hR : Routing D R E) (hX : ∀ s, 0 < Xh s) (m S : ℕ) (s : List Ltr)
    (hsm : s.length + m + 1 = D) (k q : ℝ) :
    stopOf (betaOf (S + j s.length) (E s) (rustX j R E Xh m s)) * k +
        (1 - stopOf (betaOf (S + j s.length) (E s) (rustX j R E Xh m s))) * q =
      ((1 - (1 / 2 : ℝ) ^ (S + j s.length)) * E s * k +
          (1 / 2 : ℝ) ^ (S + j s.length) * rustX j R E Xh m s * q) /
        execFrom j R E Xh (m + 1) S s := by
  obtain ⟨hC, hlam⟩ := read_level j hR hX m S s hsm
  have hpos := execFrom_pos j hR hX (m + 1) S s
  rw [hlam, hC] at *
  rw [stop_mix hpos]

/-- [proved-derived] **`storedRead_levels`: the read walks only the stored levels.** An implicit
node the address follows contributes no level: the read continues into its child with the rung
summed, as `execFrom` does; every other node is a stored level (`read_face`). -/
theorem storedRead_levels (k : List Ltr → ℝ) (k₀ : ℝ) (a : List Ltr) (m S d : ℕ)
    (hc : (kidsOf R (a.take d)).card = 1) (hr : R (a.take (d + 1)) = true) :
    storedRead j R E Xh k k₀ a (m + 1) S d =
      storedRead j R E Xh k k₀ a m (S + j (a.take d).length) (d + 1) := by
  rw [storedRead, if_pos ⟨hc, hr⟩]

/-- [proved-derived] **`storedRead_stored`: at a stored level the read is the executed mixture over
`execFrom`.** Its face below is the next stored chain's read, or `k₀` past the last stored level. -/
theorem storedRead_stored (hR : Routing D R E) (hX : ∀ s, 0 < Xh s) (k : List Ltr → ℝ) (k₀ : ℝ)
    (a : List Ltr) (m S d : ℕ) (hsm : (a.take d).length + m + 1 = D)
    (hst : ¬((kidsOf R (a.take d)).card = 1 ∧ R (a.take (d + 1)) = true)) :
    storedRead j R E Xh k k₀ a (m + 1) S d =
      ((1 - (1 / 2 : ℝ) ^ (S + j (a.take d).length)) * E (a.take d) * k (a.take d) +
          (1 / 2 : ℝ) ^ (S + j (a.take d).length) * rustX j R E Xh m (a.take d) *
            (if R (a.take (d + 1)) = true then storedRead j R E Xh k k₀ a m 0 (d + 1) else k₀)) /
        execFrom j R E Xh (m + 1) S (a.take d) := by
  rw [storedRead, if_neg hst]
  exact read_face j hR hX m S (a.take d) hsm _ _

/-! ### Audit -/

#print axioms inst_node
#print axioms fullW_node
#print axioms exec_eq
#print axioms instK_implicit
#print axioms instK_exact
#print axioms instance_read
#print axioms split_closed_form
#print axioms stop_numerators
#print axioms stop_beta
#print axioms stop_mix
#print axioms stop_pass
#print axioms beta_step
#print axioms execFrom_pos
#print axioms exec_shift
#print axioms read_level
#print axioms read_face
#print axioms storedRead_levels
#print axioms storedRead_stored

end Holonics.Compression.Landmark.Context.StoredInstance
