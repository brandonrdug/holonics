import Mathlib

/-!
# The turn menu's fibre is read from its components: cycles of the turn's order, shorter paths, packed cosets

The record of October 5 on located keys
(`research/records/2026-10-05_LOCATED_KEYS_BECOME_THE_SOURCE_PORTS_PAIR_COMPONENT.md`, the turn machine and §8 item 1;
#410's box "The turn menu's fibre law", #359; atlas `hnn.turn-menu-fibre`) reads a ring's stationary transports as its
rotor's turns: a **turn menu** on `ℤ/d` reads each edge `u → v` as `S(v) = S(u) + c` for one unknown turn `c` and
images `S` injective on the menu's ports (the diagonal board). The October library's `TurnMenu::reading` decided which
turns survive from the menu relation's components, held to the brute-force fibre on 240 drawn menus. This file proves
the law, for any finite additive group and so for `ℤ/d`.

[proved-derived; formal-checked] What is proved.

1. **Any relation the turn fits** (`Fits`, `partialInj_of_fits`, `consequence_unique`, `walk_value`, `cycle_order_eq`,
   `path_length_lt`): with images injective on the ports, the relation is a partial injection (two consequences or two
   antecedents of one port would share an image); a port's consequence is the one port whose image is `S u + c`, so a
   survivor reads the relation itself; along a walk the images step by `c`; a cycle of `k` distinct ports has
   `ord(c) = k`; a path of `p` edges on distinct ports has `p < ord(c)`.
2. **A menu given by its components** (`TurnMenu`, `Edge`, `Survives`, `survives_iff_pos`): cycles and paths of given
   lengths on distinct ports; a turn survives when some images, injective on the ports, satisfy every edge.
3. **The fibre law** (`Packs`, `survives_iff`): a turn `c` survives exactly when every cycle has length `ord(c)`, every
   path has at most `ord(c)` ports (fewer than `ord(c)` edges), and the components fit disjoint cosets of `⟨c⟩`: the
   cycles take distinct cosets and the paths' runs, assigned to the other cosets, sum to at most `ord(c)` in each.
   Necessity reads the cosets from the images (`cycle_takes_coset`: a cycle's images are a whole coset); sufficiency
   places each cycle on its coset and each path's run after the runs before it in its coset (`place`, `place_fits`,
   `place_injective`). The count `#cycles · ord(c) + Σ path ports ≤ |G|` follows (`card_le_of_survives`).
4. **The cosets** (`card_coset`, `addOrderOf_zmod`, `card_cosets_zmod`, `zmod_survives_iff`): each coset of `⟨c⟩` has
   `ord(c)` elements; on `ℤ/d`, `ord(c) = d / gcd(d, c)` and there are `gcd(d, c)` cosets.
5. **The record's menu** (`ring60`, `ring60_survives_iff`): the cycle `(0 1 2 3)` on the ports of `ℤ/60` survives
   exactly the turns `15 = 3·5` and `45 = 3²·5`.

The computational object is the helical pair interaction on one ring: each edge is a pair contact whose stage is the
rotor's turn, and a cycle closes when its turns sum to zero, the cell holonomy of a `ℤ/d` connection on the menu. Of
the winding guide's six general objects this touches the helix (the rotor's turns and their order), the pair (the
edges), faces and placement (the images, placed coset by coset) and the cell holonomy (a cycle's turn sum); the tube
and the tower thread stay attached.

Consumers: the atlas row `hnn.turn-menu-fibre`, which `compression.located-transport` and `compression.transport-gauge`
use and specialize.

What stands beside it: the diagonal board's cycle fibre (`HNN/SurvivorsCycleFibre`), of which a turn menu's cycles are
the loops with the turn as their stage. The components are data here: that a finite partial injection splits into
cycles and paths is the standard decomposition and is not formalized, and the general lemmas of item 1 hold for any
read relation. Deciding the packing is a bin-packing search over the paths' runs, which the October library ran over
the few menu ports; the law states it and does not decide it. Publication, which reads only consequences that were
read, is `consequence_unique` on the read edges; a port whose consequence was not read stays plural.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.TurnMenuFibre

open AddSubgroup

section Relation

variable {P G : Type*} [AddCommGroup G]

/-- [definition] **A turn fits a relation** at images `S`: each edge `u → v` reads `S v = S u + c`. -/
def Fits (R : P → P → Prop) (S : P → G) (c : G) : Prop :=
  ∀ u v, R u v → S v = S u + c

variable {R : P → P → Prop} {D : Set P} {S : P → G} {c : G}

/-- [proved-derived; formal-checked] **The relation is a partial injection**: with images injective on the ports, two
consequences of one port, or two antecedents, would share an image. -/
theorem partialInj_of_fits (hS : Set.InjOn S D) (hD : ∀ u v, R u v → u ∈ D ∧ v ∈ D) (hfit : Fits R S c) :
    (∀ u v v', R u v → R u v' → v = v') ∧ ∀ u u' v, R u v → R u' v → u = u' :=
  ⟨fun u v v' h h' => hS (hD u v h).2 (hD u v' h').2 ((hfit u v h).trans (hfit u v' h').symm),
    fun u u' v h h' => hS (hD u v h).1 (hD u' v h').1 (add_right_cancel ((hfit u v h).symm.trans (hfit u' v h')))⟩

/-- [proved-derived; formal-checked] **A survivor reads the relation**: the one port whose image is `S u + c` is the
consequence `v` of `u` (publication reads it, and only where the edge was read). -/
theorem consequence_unique (hS : Set.InjOn S D) (hD : ∀ u v, R u v → u ∈ D ∧ v ∈ D) (hfit : Fits R S c)
    {u v w : P} (huv : R u v) (hw : w ∈ D) (hSw : S w = S u + c) : w = v :=
  hS hw (hD u v huv).2 (hSw.trans (hfit u v huv).symm)

/-- [proved-derived; formal-checked] **Along a walk the images step by the turn**: `S(x_i) = S(x_0) + i·c`. -/
theorem walk_value (hfit : Fits R S c) (x : ℕ → P) {m : ℕ} (hw : ∀ i < m, R (x i) (x (i + 1))) :
    ∀ i ≤ m, S (x i) = S (x 0) + i • c
  | 0, _ => by simp
  | i + 1, hi => by
      rw [hfit _ _ (hw i (by omega)), walk_value hfit x hw i (by omega), succ_nsmul, add_assoc]

/-- [proved-derived; formal-checked] **A cycle has the turn's order**: a cycle of `k` distinct ports closes exactly
when `k·c = 0`, and keeps its ports apart only if no shorter multiple vanishes, so `ord(c) = k`. -/
theorem cycle_order_eq (hS : Set.InjOn S D) (hfit : Fits R S c) (x : ℕ → P) {k : ℕ} (hk : 0 < k)
    (hw : ∀ i < k, R (x i) (x ((i + 1) % k))) (hD : ∀ i < k, x i ∈ D)
    (hdist : ∀ i < k, ∀ j < k, x i = x j → i = j) : addOrderOf c = k := by
  have hw' : ∀ i < k - 1, R (x i) (x (i + 1)) := fun i hi => by
    have := hw i (by omega)
    rwa [Nat.mod_eq_of_lt (by omega)] at this
  have hv := walk_value hfit x hw'
  have hclose := hfit _ _ (hw (k - 1) (by omega))
  rw [Nat.sub_add_cancel hk, Nat.mod_self, hv (k - 1) le_rfl, add_assoc, ← succ_nsmul,
    Nat.sub_add_cancel hk] at hclose
  rw [addOrderOf_eq_iff hk]
  refine ⟨add_eq_left.mp hclose.symm, fun m hm hm0 hmc => ?_⟩
  have h1 := hv m (by omega)
  rw [hmc, add_zero] at h1
  have := hdist m hm 0 hk (hS (hD m hm) (hD 0 hk) h1)
  omega

/-- [proved-derived; formal-checked] **A path is shorter than the turn's order**: a path of `p` edges on distinct
ports has `p < ord(c)`, since `ord(c)` steps return its first image. -/
theorem path_length_lt [Finite G] (hS : Set.InjOn S D) (hfit : Fits R S c) (x : ℕ → P) {p : ℕ}
    (hw : ∀ i < p, R (x i) (x (i + 1))) (hD : ∀ i ≤ p, x i ∈ D)
    (hdist : ∀ i ≤ p, ∀ j ≤ p, x i = x j → i = j) : p < addOrderOf c := by
  refine lt_of_not_ge fun h => ?_
  have hpos := addOrderOf_pos c
  have h1 := walk_value hfit x hw (addOrderOf c) h
  rw [addOrderOf_nsmul_eq_zero, add_zero] at h1
  have := hdist _ h 0 (Nat.zero_le _) (hS (hD _ h) (hD 0 (Nat.zero_le _)) h1)
  omega

end Relation

section Cosets

variable {G : Type*} [AddCommGroup G]

/-- [proved-derived; formal-checked] A step by a multiple of the turn stays in its coset. -/
theorem mk_add_nsmul (a c : G) (n : ℕ) : ((a + n • c : G) : G ⧸ zmultiples c) = a := by
  rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff (n • c)).mpr (nsmul_mem_zmultiples c n), add_zero]

/-- [proved-derived; formal-checked] Two elements of one coset differ by a multiple of the turn below its order. -/
theorem exists_nsmul_of_mk_eq [Finite G] {a b c : G} (h : (a : G ⧸ zmultiples c) = b) :
    ∃ n < addOrderOf c, b = a + n • c := by
  classical
  have hm : -a + b ∈ zmultiples c := QuotientAddGroup.eq.mp h
  rw [mem_zmultiples_iff_mem_range_addOrderOf] at hm
  obtain ⟨n, hn, hn'⟩ := Finset.mem_image.mp hm
  exact ⟨n, Finset.mem_range.mp hn, by rw [hn']; abel⟩

/-- [proved-derived; formal-checked] **Each coset of `⟨c⟩` has `ord(c)` elements.** -/
theorem card_coset [Finite G] (c : G) (q : G ⧸ zmultiples c) :
    Nat.card {g : G // (g : G ⧸ zmultiples c) = q} = addOrderOf c := by
  let f : Fin (addOrderOf c) → {g : G // (g : G ⧸ zmultiples c) = q} :=
    fun n => ⟨Quotient.out q + (n : ℕ) • c, by rw [mk_add_nsmul, QuotientAddGroup.out_eq']⟩
  have hf : Function.Bijective f := by
    refine ⟨fun n m h => Fin.ext ?_, fun ⟨g, hg⟩ => ?_⟩
    · have h' : Quotient.out q + (n : ℕ) • c = Quotient.out q + (m : ℕ) • c := congrArg Subtype.val h
      exact nsmul_injOn_Iio_addOrderOf n.2 m.2 (add_left_cancel h')
    · obtain ⟨n, hn, rfl⟩ := exists_nsmul_of_mk_eq ((QuotientAddGroup.out_eq' q).trans hg.symm)
      exact ⟨⟨n, hn⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- [proved-derived; formal-checked] **On `ℤ/d` the turn's order is `d / gcd(d, c)`.** -/
theorem addOrderOf_zmod {d : ℕ} [NeZero d] (c : ZMod d) : addOrderOf c = d / d.gcd c.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  exact ZMod.addOrderOf_coe c.val (NeZero.ne d)

/-- [proved-derived; formal-checked] **On `ℤ/d` there are `gcd(d, c)` cosets of `⟨c⟩`.** -/
theorem card_cosets_zmod {d : ℕ} [NeZero d] (c : ZMod d) :
    Nat.card (ZMod d ⧸ zmultiples c) = d.gcd c.val := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (zmultiples c)
  rw [Nat.card_zmultiples, addOrderOf_zmod, Nat.card_zmod] at h
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hg : d.gcd c.val ∣ d := Nat.gcd_dvd_left _ _
  have hpos : 0 < d / d.gcd c.val := Nat.div_pos (Nat.le_of_dvd hd hg) (Nat.gcd_pos_of_pos_left _ hd)
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [← h]
  exact (Nat.mul_div_cancel' hg).symm

end Cosets

/-! ## A menu given by its components -/

/-- [definition] **A turn menu given by its components**: cycles indexed by `ι` with their lengths, paths indexed by
`κ` with their port counts (a path of `p` edges has `p + 1` ports), and an injective map of their positions to the
ports. Cycle `j` reads `i → i + 1 (mod clen j)`, path `π` reads `i → i + 1`. -/
structure TurnMenu (P ι κ : Type*) where
  clen : ι → ℕ
  plen : κ → ℕ
  clen_pos : ∀ j, 0 < clen j
  plen_pos : ∀ π, 0 < plen π
  port : (Σ j, Fin (clen j)) ⊕ (Σ π, Fin (plen π)) → P
  port_injective : Function.Injective port

namespace TurnMenu

variable {P ι κ G : Type*} [AddCommGroup G]

/-- [definition] The positions of a menu's components. -/
abbrev Pos (M : TurnMenu P ι κ) : Type _ := (Σ j, Fin (M.clen j)) ⊕ (Σ π, Fin (M.plen π))

/-- [definition] The next position around cycle `j`. -/
def cnext (M : TurnMenu P ι κ) (j : ι) (i : Fin (M.clen j)) : Fin (M.clen j) :=
  ⟨(i.1 + 1) % M.clen j, Nat.mod_lt _ (M.clen_pos j)⟩

/-- [definition] **The edges between positions**: around each cycle, and along each path. -/
inductive PosEdge (M : TurnMenu P ι κ) : M.Pos → M.Pos → Prop
  | cyc (j : ι) (i : Fin (M.clen j)) : PosEdge M (.inl ⟨j, i⟩) (.inl ⟨j, M.cnext j i⟩)
  | path (π : κ) (i : ℕ) (h : i + 1 < M.plen π) :
      PosEdge M (.inr ⟨π, ⟨i, Nat.lt_of_succ_lt h⟩⟩) (.inr ⟨π, ⟨i + 1, h⟩⟩)

/-- [definition] **The menu relation** `R` on the ports. -/
def Edge (M : TurnMenu P ι κ) (u v : P) : Prop :=
  ∃ a b, M.PosEdge a b ∧ u = M.port a ∧ v = M.port b

/-- [definition] The menu's ports. -/
def Ports (M : TurnMenu P ι κ) : Set P := Set.range M.port

/-- [definition] **A turn survives the menu**: some images, injective on the ports, satisfy every edge. -/
def Survives (M : TurnMenu P ι κ) (c : G) : Prop :=
  ∃ S : P → G, Set.InjOn S M.Ports ∧ Fits M.Edge S c

open Classical in
/-- [definition] The ports the paths assigned to coset `q` take: the sum of their runs. -/
noncomputable def binSum [Fintype κ] (M : TurnMenu P ι κ) {Q : Type*} (β : κ → Q) (q : Q) : ℕ :=
  ∑ π ∈ Finset.univ.filter (fun π => β π = q), M.plen π

open Classical in
/-- [definition] A path's offset in its coset: the runs of the paths before it assigned to the same coset. -/
noncomputable def off [Fintype κ] [LinearOrder κ] (M : TurnMenu P ι κ) {Q : Type*} (β : κ → Q) (π : κ) : ℕ :=
  ∑ π' ∈ Finset.univ.filter (fun π' => π' < π ∧ β π' = β π), M.plen π'

/-- [definition] **The components fit disjoint cosets of `⟨c⟩`**: the cycles take distinct cosets, and the paths,
assigned to the other cosets, sum to at most `ord(c)` ports in each. -/
def Packs [Fintype κ] (M : TurnMenu P ι κ) (c : G) : Prop :=
  ∃ (γ : ι → G ⧸ zmultiples c) (β : κ → G ⧸ zmultiples c), Function.Injective γ ∧ (∀ j π, γ j ≠ β π) ∧
    ∀ q, M.binSum β q ≤ addOrderOf c

/-- [definition] **The placement**: cycle `j` on its coset from the coset's representative, path `π` on its coset
after the offset `o π`. -/
noncomputable def place (M : TurnMenu P ι κ) (c : G) (γ : ι → G ⧸ zmultiples c) (β : κ → G ⧸ zmultiples c)
    (o : κ → ℕ) : M.Pos → G
  | .inl ⟨j, i⟩ => Quotient.out (γ j) + (i : ℕ) • c
  | .inr ⟨π, i⟩ => Quotient.out (β π) + (o π + i) • c

/-- [proved-derived; formal-checked] **Survival read on the positions**: a turn survives exactly when an injective
assignment of the positions satisfies every edge between them. -/
theorem survives_iff_pos (M : TurnMenu P ι κ) (c : G) :
    M.Survives c ↔ ∃ V : M.Pos → G, Function.Injective V ∧ Fits M.PosEdge V c := by
  constructor
  · rintro ⟨S, hS, hfit⟩
    exact ⟨S ∘ M.port, fun a b h => M.port_injective (hS ⟨a, rfl⟩ ⟨b, rfl⟩ h),
      fun a b h => hfit _ _ ⟨a, b, h, rfl, rfl⟩⟩
  · rintro ⟨V, hV, hfit⟩
    refine ⟨Function.extend M.port V 0, ?_, ?_⟩
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
      rw [M.port_injective.extend_apply, M.port_injective.extend_apply] at h
      rw [hV h]
    · rintro u v ⟨a, b, h, rfl, rfl⟩
      rw [M.port_injective.extend_apply, M.port_injective.extend_apply]
      exact hfit a b h

variable {M : TurnMenu P ι κ} {V : M.Pos → G} {c : G}

/-- [proved-derived; formal-checked] Around a cycle the positions' images step by the turn. -/
theorem pos_cycle_val (hV : Fits M.PosEdge V c) (j : ι) :
    ∀ (i : ℕ) (hi : i < M.clen j), V (.inl ⟨j, ⟨i, hi⟩⟩) = V (.inl ⟨j, ⟨0, M.clen_pos j⟩⟩) + i • c
  | 0, _ => by simp
  | i + 1, hi => by
      have hE := hV _ _ (PosEdge.cyc j ⟨i, by omega⟩)
      have hn : M.cnext j ⟨i, by omega⟩ = ⟨i + 1, hi⟩ := Fin.ext (Nat.mod_eq_of_lt hi)
      rw [hn] at hE
      rw [hE, pos_cycle_val hV j i (by omega), succ_nsmul, add_assoc]

/-- [proved-derived; formal-checked] Along a path the positions' images step by the turn. -/
theorem pos_path_val (hV : Fits M.PosEdge V c) (π : κ) :
    ∀ (i : ℕ) (hi : i < M.plen π), V (.inr ⟨π, ⟨i, hi⟩⟩) = V (.inr ⟨π, ⟨0, M.plen_pos π⟩⟩) + i • c
  | 0, _ => by simp
  | i + 1, hi => by
      rw [hV _ _ (PosEdge.path π i hi), pos_path_val hV π i (by omega), succ_nsmul, add_assoc]

/-- [proved-derived; formal-checked] Equal cycle positions lie on one cycle. -/
theorem inl_fst {j j' : ι} {i : Fin (M.clen j)} {i' : Fin (M.clen j')}
    (h : (.inl ⟨j, i⟩ : M.Pos) = .inl ⟨j', i'⟩) : j = j' :=
  congrArg Sigma.fst (Sum.inl.inj h)

/-- [proved-derived; formal-checked] **Every cycle has the turn's order**, at an injective assignment. -/
theorem pos_cycle_order (hinj : Function.Injective V) (hV : Fits M.PosEdge V c) (j : ι) :
    addOrderOf c = M.clen j := by
  have hk := M.clen_pos j
  have hE := hV _ _ (PosEdge.cyc j ⟨M.clen j - 1, by omega⟩)
  have hn : M.cnext j ⟨M.clen j - 1, by omega⟩ = ⟨0, hk⟩ :=
    Fin.ext (by simp [cnext, Nat.sub_add_cancel hk])
  rw [hn, pos_cycle_val hV j (M.clen j - 1) (by omega), add_assoc, ← succ_nsmul,
    Nat.sub_add_cancel hk] at hE
  rw [addOrderOf_eq_iff hk]
  refine ⟨add_eq_left.mp hE.symm, fun m hm hm0 hmc => ?_⟩
  have h1 := pos_cycle_val hV j m hm
  rw [hmc, add_zero] at h1
  have h2 := hinj h1
  simp only [Sum.inl.injEq, Sigma.mk.injEq, heq_eq_eq, Fin.mk.injEq, true_and] at h2
  omega

/-- [proved-derived; formal-checked] **Every path is shorter than the turn's order**, at an injective assignment. -/
theorem pos_path_le [Finite G] (hinj : Function.Injective V) (hV : Fits M.PosEdge V c) (π : κ) :
    M.plen π ≤ addOrderOf c := by
  refine le_of_not_gt fun h => ?_
  have hpos := addOrderOf_pos c
  have h1 := pos_path_val hV π (addOrderOf c) h
  rw [addOrderOf_nsmul_eq_zero, add_zero] at h1
  have h2 := hinj h1
  simp only [Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, Fin.mk.injEq, true_and] at h2
  omega

/-- [proved-derived; formal-checked] **The components fit disjoint cosets**, at an injective assignment: the cosets of
the components' first images pack them. -/
theorem pos_packs [Fintype κ] [Finite G] (hinj : Function.Injective V) (hV : Fits M.PosEdge V c) : M.Packs c := by
  classical
  refine ⟨fun j => (V (.inl ⟨j, ⟨0, M.clen_pos j⟩⟩) : G ⧸ zmultiples c),
    fun π => (V (.inr ⟨π, ⟨0, M.plen_pos π⟩⟩) : G ⧸ zmultiples c), ?_, ?_, ?_⟩
  · intro j j' h
    obtain ⟨n, hn, hb⟩ := exists_nsmul_of_mk_eq h
    rw [pos_cycle_order hinj hV j] at hn
    rw [← pos_cycle_val hV j n hn] at hb
    exact (inl_fst (hinj hb)).symm
  · intro j π h
    obtain ⟨n, hn, hb⟩ := exists_nsmul_of_mk_eq h
    rw [pos_cycle_order hinj hV j] at hn
    rw [← pos_cycle_val hV j n hn] at hb
    exact absurd (hinj hb) (by simp)
  · intro q
    obtain ⟨s, hs, hmem⟩ : ∃ s : Finset κ, M.binSum (fun π => (V (.inr ⟨π, ⟨0, M.plen_pos π⟩⟩) :
        G ⧸ zmultiples c)) q = ∑ π ∈ s, M.plen π ∧
        ∀ π, π ∈ s ↔ (V (.inr ⟨π, ⟨0, M.plen_pos π⟩⟩) : G ⧸ zmultiples c) = q :=
      ⟨_, rfl, fun π => by simp⟩
    rw [hs]
    have hcard : ∑ π ∈ s, M.plen π =
        (s.sigma fun π => (Finset.univ : Finset (Fin (M.plen π)))).card := by
      rw [Finset.card_sigma]; simp
    rw [hcard]
    calc _ ≤ ((Finset.range (addOrderOf c)).image fun n => Quotient.out q + n • c).card := by
          refine Finset.card_le_card_of_injOn (fun x : (Σ π, Fin (M.plen π)) => V (.inr x)) ?_ ?_
          · rintro ⟨π, i⟩ hx
            rw [Finset.mem_coe, Finset.mem_sigma] at hx
            have hq := (hmem π).mp hx.1
            have hv := pos_path_val hV π i.1 i.2
            simp only [Fin.eta] at hv
            have hq' : ((V (.inr ⟨π, i⟩) : G) : G ⧸ zmultiples c) = q := by rw [hv, mk_add_nsmul, hq]
            obtain ⟨n, hn, hb⟩ := exists_nsmul_of_mk_eq ((QuotientAddGroup.out_eq' q).trans hq'.symm)
            rw [Finset.mem_coe, Finset.mem_image]
            exact ⟨n, Finset.mem_range.mpr hn, hb.symm⟩
          · intro x _ y _ hxy
            exact Sum.inr.inj (hinj hxy)
      _ ≤ (Finset.range (addOrderOf c)).card := Finset.card_image_le
      _ = addOrderOf c := Finset.card_range _

/-- [proved-derived; formal-checked] A path's offset is the sum of the runs before it in its coset. -/
theorem off_eq [Fintype κ] [LinearOrder κ] (M : TurnMenu P ι κ) {Q : Type*} (β : κ → Q) (π : κ) :
    ∃ s : Finset κ, M.off β π = ∑ x ∈ s, M.plen x ∧ ∀ x, x ∈ s ↔ x < π ∧ β x = β π :=
  ⟨_, rfl, fun x => by simp⟩

/-- [proved-derived; formal-checked] A coset's run sum is the sum over the paths assigned to it. -/
theorem binSum_eq [Fintype κ] (M : TurnMenu P ι κ) {Q : Type*} (β : κ → Q) (q : Q) :
    ∃ s : Finset κ, M.binSum β q = ∑ x ∈ s, M.plen x ∧ ∀ x, x ∈ s ↔ β x = q :=
  ⟨_, rfl, fun x => by simp⟩

/-- [proved-derived; formal-checked] A path's run ends before the next path of its coset begins. -/
theorem off_add_le_off [Fintype κ] [LinearOrder κ] (M : TurnMenu P ι κ) {Q : Type*} (β : κ → Q) {π π' : κ}
    (hlt : π < π') (hβ : β π = β π') : M.off β π + M.plen π ≤ M.off β π' := by
  obtain ⟨s, hs, hmem⟩ := M.off_eq β π
  obtain ⟨s', hs', hmem'⟩ := M.off_eq β π'
  have hnot : π ∉ s := fun h => lt_irrefl π ((hmem π).mp h).1
  have hsub : insert π s ⊆ s' := by
    intro x hx
    rw [hmem']
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨hlt, hβ⟩
    · obtain ⟨h1, h2⟩ := (hmem x).mp hx
      exact ⟨h1.trans hlt, h2.trans hβ⟩
  rw [hs, hs', add_comm, ← Finset.sum_insert hnot]
  exact Finset.sum_le_sum_of_subset hsub

/-- [proved-derived; formal-checked] A path's run ends within its coset's runs. -/
theorem off_add_le_bin [Fintype κ] [LinearOrder κ] (M : TurnMenu P ι κ) {Q : Type*} (β : κ → Q) (π : κ) :
    M.off β π + M.plen π ≤ M.binSum β (β π) := by
  obtain ⟨s, hs, hmem⟩ := M.off_eq β π
  obtain ⟨t, ht, hmem'⟩ := M.binSum_eq β (β π)
  have hnot : π ∉ s := fun h => lt_irrefl π ((hmem π).mp h).1
  have hsub : insert π s ⊆ t := by
    intro x hx
    rw [hmem']
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rfl
    · exact ((hmem x).mp hx).2
  rw [hs, ht, add_comm, ← Finset.sum_insert hnot]
  exact Finset.sum_le_sum_of_subset hsub

/-- [proved-derived; formal-checked] **The placement satisfies every edge** when every cycle has the turn's order. -/
theorem place_fits (hc : ∀ j, M.clen j = addOrderOf c) (γ : ι → G ⧸ zmultiples c) (β : κ → G ⧸ zmultiples c)
    (o : κ → ℕ) : Fits M.PosEdge (M.place c γ β o) c := by
  intro a b h
  cases h with
  | cyc j i =>
      have key : ∀ n : ℕ, ((n + 1) % M.clen j) • c = (n + 1) • c := fun n => by
        rw [hc j, mod_addOrderOf_nsmul]
      simp only [place, cnext]
      rw [key, succ_nsmul, add_assoc]
  | path π i h =>
      simp only [place]
      rw [show o π + (i + 1) = (o π + i) + 1 by omega, succ_nsmul, add_assoc]

/-- [proved-derived; formal-checked] **The placement is injective** when the components pack: distinct cosets hold
distinct components, a cycle's images are distinct multiples below the order, and a coset's paths take disjoint runs
below the order. -/
theorem place_injective [Fintype κ] [LinearOrder κ] (hc : ∀ j, M.clen j = addOrderOf c)
    {γ : ι → G ⧸ zmultiples c} {β : κ → G ⧸ zmultiples c} (hγ : Function.Injective γ) (hγβ : ∀ j π, γ j ≠ β π)
    (hbin : ∀ q, M.binSum β q ≤ addOrderOf c) : Function.Injective (M.place c γ β (M.off β)) := by
  have hcl : ∀ j i, ((M.place c γ β (M.off β) (.inl ⟨j, i⟩) : G) : G ⧸ zmultiples c) = γ j := fun j i => by
    simp only [place]; rw [mk_add_nsmul, QuotientAddGroup.out_eq']
  have hpl : ∀ π i, ((M.place c γ β (M.off β) (.inr ⟨π, i⟩) : G) : G ⧸ zmultiples c) = β π := fun π i => by
    simp only [place]; rw [mk_add_nsmul, QuotientAddGroup.out_eq']
  rintro (⟨j, i⟩ | ⟨π, i⟩) (⟨j', i'⟩ | ⟨π', i'⟩) h
  · obtain rfl : j = j' := hγ ((hcl j i).symm.trans ((congrArg _ h).trans (hcl j' i')))
    simp only [place] at h
    have hi : (i : ℕ) = i' := nsmul_injOn_Iio_addOrderOf (show (i : ℕ) < addOrderOf c from hc j ▸ i.2)
      (show (i' : ℕ) < addOrderOf c from hc j ▸ i'.2) (add_left_cancel h)
    obtain rfl := Fin.ext hi
    rfl
  · exact absurd ((hcl j i).symm.trans ((congrArg _ h).trans (hpl π' i'))) (hγβ j π')
  · exact absurd ((hcl j' i').symm.trans ((congrArg _ h).symm.trans (hpl π i))) (hγβ j' π)
  · have hβ : β π = β π' := (hpl π i).symm.trans ((congrArg _ h).trans (hpl π' i'))
    simp only [place] at h
    rw [hβ] at h
    have hi := i.2
    have hi' := i'.2
    have b1 : M.off β π + i < addOrderOf c :=
      lt_of_lt_of_le (by omega) ((M.off_add_le_bin β π).trans (hbin _))
    have b2 : M.off β π' + i' < addOrderOf c :=
      lt_of_lt_of_le (by omega) ((M.off_add_le_bin β π').trans (hbin _))
    have heq : M.off β π + i = M.off β π' + i' := nsmul_injOn_Iio_addOrderOf b1 b2 (add_left_cancel h)
    rcases lt_trichotomy π π' with hlt | rfl | hlt
    · have := M.off_add_le_off β hlt hβ
      omega
    · have : (i : ℕ) = i' := by omega
      obtain rfl := Fin.ext this
      rfl
    · have := M.off_add_le_off β hlt hβ.symm
      omega

/-- [proved-derived; formal-checked] **The turn menu's fibre law** (#359). A turn `c` survives a menu given by its
components exactly when every cycle has length `ord(c)`, every path has at most `ord(c)` ports (fewer than `ord(c)`
edges), and the components fit disjoint cosets of `⟨c⟩` (`Packs`). -/
theorem survives_iff [Fintype κ] [LinearOrder κ] [Finite G] (M : TurnMenu P ι κ) (c : G) :
    M.Survives c ↔ (∀ j, M.clen j = addOrderOf c) ∧ (∀ π, M.plen π ≤ addOrderOf c) ∧ M.Packs c := by
  rw [survives_iff_pos]
  constructor
  · rintro ⟨V, hinj, hV⟩
    exact ⟨fun j => (pos_cycle_order hinj hV j).symm, pos_path_le hinj hV, pos_packs hinj hV⟩
  · rintro ⟨hc, -, γ, β, hγ, hγβ, hbin⟩
    exact ⟨M.place c γ β (M.off β), place_injective hc hγ hγβ hbin, place_fits hc γ β (M.off β)⟩

/-- [proved-derived; formal-checked] **A cycle's images are a whole coset**: at a survivor, an element lies in the
coset of the cycle's first image exactly when some position of the cycle reads it. -/
theorem cycle_takes_coset [Finite G] {S : P → G} (hS : Set.InjOn S M.Ports) (hfit : Fits M.Edge S c) (j : ι)
    (g : G) :
    (g : G ⧸ zmultiples c) = (S (M.port (.inl ⟨j, ⟨0, M.clen_pos j⟩⟩)) : G ⧸ zmultiples c) ↔
      ∃ i, S (M.port (.inl ⟨j, i⟩)) = g := by
  have hV : Fits M.PosEdge (S ∘ M.port) c := fun a b h => hfit _ _ ⟨a, b, h, rfl, rfl⟩
  have hinj : Function.Injective (S ∘ M.port) := fun a b h => M.port_injective (hS ⟨a, rfl⟩ ⟨b, rfl⟩ h)
  constructor
  · intro h
    obtain ⟨n, hn, hb⟩ := exists_nsmul_of_mk_eq h.symm
    rw [pos_cycle_order hinj hV j] at hn
    exact ⟨⟨n, hn⟩, (pos_cycle_val hV j n hn).trans hb.symm⟩
  · rintro ⟨i, rfl⟩
    have := pos_cycle_val hV j i.1 i.2
    simp only [Fin.eta, Function.comp_apply] at this
    rw [this, mk_add_nsmul]

/-- [proved-derived; formal-checked] **The count**: at a surviving turn, `#cycles · ord(c) + Σ path ports ≤ |G|`. -/
theorem card_le_of_survives [Fintype ι] [Fintype κ] [Fintype G] (h : M.Survives c) :
    Fintype.card ι * addOrderOf c + ∑ π, M.plen π ≤ Fintype.card G := by
  obtain ⟨V, hinj, hV⟩ := (survives_iff_pos M c).mp h
  have hle := Fintype.card_le_of_injective V hinj
  rw [Fintype.card_sum, Fintype.card_sigma, Fintype.card_sigma] at hle
  simp only [Fintype.card_fin] at hle
  rwa [Finset.sum_congr rfl fun j _ => (pos_cycle_order hinj hV j).symm, Finset.sum_const, smul_eq_mul,
    Finset.card_univ] at hle

/-- [proved-derived; formal-checked] **The fibre law on `ℤ/d`**: the order is `d / gcd(d, c)`, over `gcd(d, c)` cosets
(`card_cosets_zmod`) of `d / gcd(d, c)` elements each (`card_coset`). -/
theorem zmod_survives_iff [Fintype κ] [LinearOrder κ] {d : ℕ} [NeZero d] (M : TurnMenu P ι κ) (c : ZMod d) :
    M.Survives c ↔ (∀ j, M.clen j = d / d.gcd c.val) ∧ (∀ π, M.plen π ≤ d / d.gcd c.val) ∧ M.Packs c := by
  rw [survives_iff, addOrderOf_zmod]

end TurnMenu

/-! ## The record's menu: one cycle on `ℤ/60` -/

/-- [definition] **The record's menu**: the cycle `(0 1 2 3)` on the ports of `ℤ/60`, no path. -/
def ring60 : TurnMenu (ZMod 60) (Fin 1) (Fin 0) where
  clen _ := 4
  plen π := π.elim0
  clen_pos _ := by decide
  plen_pos π := π.elim0
  port
    | .inl ⟨_, i⟩ => (i.1 : ZMod 60)
    | .inr ⟨π, _⟩ => π.elim0
  port_injective := by
    rintro (⟨j, i⟩ | ⟨π, _⟩) (⟨j', i'⟩ | ⟨π', _⟩) h
    · obtain rfl : j = j' := Subsingleton.elim j j'
      have key : ∀ a b : Fin 4, ((a.1 : ZMod 60) = b.1) → a = b := by decide
      obtain rfl := key i i' h
      rfl
    · exact π'.elim0
    · exact π.elim0
    · exact π.elim0

/-- [proved-derived; formal-checked] **The record's example**: the cycle `(0 1 2 3)` on `ℤ/60` survives exactly the
turns `15 = 3·5` and `45 = 3²·5`, the elements of order four. -/
theorem ring60_survives_iff (c : ZMod 60) : ring60.Survives c ↔ c = 15 ∨ c = 45 := by
  have key : ∀ c : ZMod 60, (4 • c = 0 ∧ ∀ m < 4, 0 < m → m • c ≠ 0) ↔ (c = 15 ∨ c = 45) := by decide
  have hpacks : ring60.Packs c :=
    ⟨fun _ => 0, fun π => π.elim0, fun a b _ => Subsingleton.elim a b, fun _ π => π.elim0,
      fun q => by simp [TurnMenu.binSum]⟩
  rw [TurnMenu.survives_iff]
  constructor
  · rintro ⟨h, -, -⟩
    exact (key c).mp ((addOrderOf_eq_iff (by norm_num)).mp (h 0).symm)
  · intro h
    exact ⟨fun _ => ((addOrderOf_eq_iff (by norm_num)).mpr ((key c).mpr h)).symm, fun π => π.elim0, hpacks⟩

end Holonics.HNN.TurnMenuFibre
