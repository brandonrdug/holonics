# Hard Lefschetz holds on a flat torus letter by letter, a cover's closed walks fall into their holonomy classes at the half, and the covering tree's returns set the floor at the half

November 18, 2026, 23:44 UTC, to November 19, 00:16 UTC. Derivations with their Lean proofs and a host ruler, the
fourth set of the evening. Nothing ran on a learner or on the card, and no line was touched. Each paragraph carries
its grade: `tree` (read in this repository), `from training` (a result of the literature, named) or `agent-inferred`
(this record's join). A statement cited as Lean names its module and theorem; every such module builds with no
`sorry`, no added axiom and no `native_decide` (§7). Refs #410.

This record continues [the third set](2026-11-18_AN_ABELIAN_COVER_FACTORS_THROUGH_ITS_CHARACTERS_A_TEMPERED_COMPLEX_MIXES_AT_ITS_HALF_THE_FLUIDS_TRIADS_DO_NO_WORK_SO_EVERY_TRUNCATION_FLOWS_FOR_ALL_TIME_AND_HARD_LEFSCHETZ_IS_A_POSITIVE_COMMUTATOR.md)
("the third record"). The third record named, as the constructions its statements reach for, a triple with a
positive pairing on a cohomology (§8.3 there) and the floor at `2√q` from the covering tree (§4.2 there), and its
abelian cover left the closed walks unsorted by their holonomy. This record builds the three.

Owners touched: `hodge.hard-lefschetz-positivity`, `trace.abelian-cover-artin`, `trace.prime-cycle-theorem-half`,
`trace.tempered-density-law`, `trace.regular-zeros-on-circle`, `prime.frobenius-colour-chebotarev`. Three atlas rows
enter and three change (§7).

Receipts: [`fourth_ruler.py`](2026-11-18_HARD_LEFSCHETZ_HOLDS_ON_A_FLAT_TORUS_LETTER_BY_LETTER_A_COVERS_CLOSED_WALKS_FALL_INTO_THEIR_HOLONOMY_CLASSES_AT_THE_HALF_AND_THE_COVERING_TREES_RETURNS_SET_THE_FLOOR_AT_THE_HALF_receipts/fourth_ruler.py),
three sections, every check an assert, all pass, 0.2 seconds in one process on the cloud container's host (numpy's
default threads; integers for the triple and the counts, double floats for spectra and norms, printed as the ruler's
readings); its output
[`fourth_ruler_output.txt`](2026-11-18_HARD_LEFSCHETZ_HOLDS_ON_A_FLAT_TORUS_LETTER_BY_LETTER_A_COVERS_CLOSED_WALKS_FALL_INTO_THEIR_HOLONOMY_CLASSES_AT_THE_HALF_AND_THE_COVERING_TREES_RETURNS_SET_THE_FLOOR_AT_THE_HALF_receipts/fourth_ruler_output.txt)
and the guesses fixed in its source before its first run,
[`guesses.txt`](2026-11-18_HARD_LEFSCHETZ_HOLDS_ON_A_FLAT_TORUS_LETTER_BY_LETTER_A_COVERS_CLOSED_WALKS_FALL_INTO_THEIR_HOLONOMY_CLASSES_AT_THE_HALF_AND_THE_COVERING_TREES_RETURNS_SET_THE_FLOOR_AT_THE_HALF_receipts/guesses.txt)
(the first run started 23:47:18 UTC and the passing run 23:47:29 UTC by `date -u`).

## 1. The frame

The three earlier sets of the evening held one mechanism in many charts: a move with a reversal builds a form the move
scales, and where the form is positive every mode sits at the half. The third record proved hard Lefschetz from one
such form, the commutator of a move with its reversal, and left the triple as a hypothesis. Here the triple is built on
the exterior algebra of a flat torus, letter by letter, so hard Lefschetz holds there with its constant (§3).

On the complexes, the third record factored an abelian cover's zeta through its characters. Here the same characters
sort the base's closed walks by the carry they add around themselves, their holonomy, and where every twisted count
stays at the half's size the walks fall into the classes in equal shares (§4): the finite form of Chebotarev's density
theorem with the Riemann hypothesis's error. Finally the half is shown to be a floor and not only a ceiling: every
complex with `q + 1` darts at every cell holds the covering tree's returns at every cell, and the trace spends them over
the modes, so a large enough complex has a mode other than the count beyond any `μ < 2√q` (§5). The tempered complexes
of the first three records are the ones that meet this floor.

## 2. What the tree held

`tree`, read before each statement was written.

- `Hodge/LefschetzFromPositivity` (the third record): the `Triple` structure (`U`, its adjoint `D`, `H = DU − UD` with
  `HU − UH = −2U`), `Triple.hard_lefschetz` (`m!‖x‖ ≤ ‖Uᵐx‖` on weight `m`), `Triple.lefschetzEquiv` and
  `Triple.inner_iterate_primitive_nat`; atlas `hodge.hard-lefschetz-positivity`, whose scope said the triple is given
  and no cohomology carries one in the tree. `Hodge/HodgeEllipticPower` (the (1,1) classes of `n` tori) and atlas
  `hodge.torus-power-narayana` (the count of Hodge classes on `Eⁿ` by a ruler) read the torus without a triple.
- `Landmarks/IharaAbelianCover` (the third record): the cover's dart operator, its frame change to the twists
  (then `cover_mul_fourier`, renamed here, §7.1) and `artin_abelian_cover`; atlas `trace.abelian-cover-artin`, whose
  scope named "the splitting of a prime cycle by the order of its holonomy" as not stated. `Landmarks/IharaEulerProduct`
  (`ClosedWalk`, closed walks without backtracking with the wrap) and `Compression/Landmark/NecklaceIntegrality` (the
  expansion of a matrix power's trace over cyclic words). Atlas `prime.frobenius-colour-chebotarev` holds Chebotarev's
  density for number fields read on two cubics by a census, with the error `√x` under the generalized Riemann
  hypothesis; no row held it for a complex.
- `Landmarks/RegularComplexDensityLaw` (the third record): `Balanced.floor` and `floor_of_modes`, a floor from the
  trace of `A²` alone, and atlas `trace.tempered-density-law`, whose scope said "the Alon–Boppana limit 2√q − o(1) …
  not stated, and the trace floor tends to √(q + 1), below 2√q". `Landmarks/IharaBass` (`src`, `tgt`, the incidences,
  `J`, `hashimoto`) and `Landmarks/RegularComplexZeros` (`eigen`, `trace_pow_eq_sum_roots_charpoly`). Mathlib holds
  `catalan` and its recursion; no ballot theorem and no walk count on a tree.

## 3. Hard Lefschetz on a flat torus, letter by letter

`Hodge/TorusLefschetzTriple`. [definition] `agent-inferred`. The exterior algebra of `ℝ^(2n)` with plane pairs
`(e_i, f_i)` has the orthonormal basis of words `w : Fin n → Fin 4`: at place `i`, the letter `0` is `1`, `1` is `e_i`,
`2` is `f_i` and `3` is `e_i ∧ f_i`. The flat Kähler form `ω = Σ_i e_i ∧ f_i` is a sum of even forms, so `ω ∧ ·` acts
letter by letter with no sign: `L_i` turns the letter `0` at `i` into `3`, `Λ_i` turns `3` back into `0`, and `H_i`
weighs a word by `+1`, `0`, `0`, `−1` for its letter at `i`. Each move is read through the involution `flip i` that
exchanges `0` and `3` at `i`, gated on the letter it acts on.

[proved-derived; formal-checked]

1. The letterwise laws (`inner_lowerAt`, `raiseAt_lowerAt_of_ne`, `raiseAt_lowerAt_self`, `weightAt_lowerAt_of_ne`,
   `weightAt_lowerAt_self`): `L_i` and `Λ_i` are adjoint; letters at different places commute;
   `Λ_i L_i − L_i Λ_i = H_i` and `H_i L_i − L_i H_i = −2L_i`.
2. The triple (`torusTriple`): `(L, Λ, H)` with `L = Σ L_i` is a `Triple` of `Hodge/LefschetzFromPositivity` on the
   forms, the forms' inner product its positive pairing.
3. The weight is the codegree (`weight_apply`, `weightSpace_eq_formsOfDegree`, `weightSpace_neg_eq_formsOfDegree`):
   `H` multiplies a word of degree `deg w` by `n − deg w`, so the weight spaces `±m` are the forms of degrees `n ∓ m`.
4. Hard Lefschetz (`hard_lefschetz_degree`, `inner_iterate_primitive_degree`, `lefschetzDegreeEquiv`,
   `finrank_formsOfDegree_symm`): for `m ≤ n` and `x` of degree `n − m`, `m!‖x‖ ≤ ‖Lᵐx‖`; on a primitive `x`,
   `⟪Lʲx, Lʲy⟫ = j!·m!/(m − j)!·⟪x, y⟫`; `Lᵐ` is a linear equivalence from degree `n − m` onto degree `n + m`, so the
   two degrees have one dimension.

[interpretation] `agent-inferred`. Each plane pair is one copy of the smallest triple: a doublet `1, e_i ∧ f_i` of
weights `±1` and two singlets `e_i`, `f_i`. The torus's triple is their sum, the weight is the contacts a form
leaves open less those it closes, and `Lᵐ` places a face onto its mirror. The pairing is positive from the start, so the theorem holds with
no harmonic theory beyond the flat one: the third record's statement now has a first space that carries its triple.
The identification of the torus's de Rham cohomology with these forms (by the invariant forms) and of its cup product
with `∧` is the standard one (`from training`) and is not formalized; the count of words `C(2n, n − m)` is not computed.

## 4. A cover's closed walks fall into their holonomy classes at the half

`Landmarks/IharaCoverChebotarev`. [definition] A closed walk of the base (`n` darts, no step back, the wrap included)
carries a holonomy, the sum of the voltages it crosses, in the finite commutative group `G` of the cover; `W_n(g)`
counts the closed walks of `n` darts of holonomy `g`.

[proved-derived; formal-checked]

1. A weighted power's trace is a sum over closed walks (`trace_pow_weighted`, `trace_pow_hashimotoC`,
   `trace_pow_diagonal_mul_hashimoto`), read through `NecklaceIntegrality`'s cyclic-word expansion; the twist that
   weighs the dart entered and the twist that weighs the dart left give one sum.
2. A twist reads the holonomy (`trace_pow_twist`): `tr(B_k)ⁿ = Σ_c ψ(k·hol c)`.
3. Orthogonality sorts the walks (`sum_char_mul_trace`): for a primitive `ψ` into a domain,
   `Σ_k ψ(−kg)·tr(B_k)ⁿ = #G·W_n(g)`; the classes add to all the closed walks (`sum_holonomyCount`), and the trivial
   twist is the base (`trace_pow_twist_zero`).
4. The cover counts the walks of holonomy zero (`trace_cover_pow_eq`): `tr B_Yⁿ = #G·W_n(0)`, through
   `IharaAbelianCover`'s frame change and its two-sided inverse (`charFrameInv_mul_charFrame`,
   `charFrame_mul_charFrameInv`): a closed walk of the cover is a closed walk of the base of holonomy zero with a
   starting sheet.
5. Chebotarev at the half (`holonomyCount_sub_le`, `holonomyCount_tempered`): over `ℂ`, if every nontrivial twist has
   `‖tr(B_k)ⁿ‖ ≤ M`, then `|W_n(g) − tr Bⁿ/#G| ≤ (#G − 1)/#G·M` for every class; with the base tempered and the twists'
   traces at most `C·√qⁿ`, `|W_n(g) − qⁿ/#G| ≤ ((#G − 1)·C·√qⁿ + 1 + 2|c| + 2(|V| − 1)·√qⁿ)/#G`, `c = |E| − |V|`.

[interpretation] `agent-inferred`. The holonomy of a closed walk is what a contact's carry adds up to around a closed
strand, and the characters are the cover's own frames reading it. The base's count is the trivial frame; every other
frame reads a twisted count, and where each stays at the half's size the walks split into the classes in equal shares
up to the half. For an abelian cover the holonomy of a prime cycle is its Frobenius (Stark and Terras, `from
training`), so this is `prime.frobenius-colour-chebotarev` on a complex, for closed walks, with the error the
generalized Riemann hypothesis gives a number field. The bound on the twisted traces stays a hypothesis: placing a
twisted operator's modes in the band is the twisted complex's own half.

## 5. The covering tree's returns set the floor at the half

`Landmarks/TreeWalkFloor`. On a complex with `q + 1` darts at every cell, write `N_j` for the cell-to-cell counts of
walks of `j` darts without a step back, `n` for the count of cells and `C_k` for Catalan's number.

[proved-standard; formal-checked]

1. The three-term recursion (`adjacency_mul_nbWalk`): `A·N_j = N_(j+1) + w_j·N_(j−1)`, with `w_0 = 0`, `w_1 = q + 1`
   and `w_j = q` beyond. It rests on `B = TᵀS − J` (`hashimoto_eq`), `TTᵀ = q + 1` and `TB = qS`.
2. The tree counts (`adjacency_pow_eq_sum`, `treeCount_le_adjacency_pow_diag`): `Aᵐ = Σ_(j≤m) treeCount q m j·N_j`,
   where `treeCount q m j` counts the walks of `m` steps from the covering tree's root that end at depth `j`, each step
   back weighed by its `w`. Every `N_j` is entrywise nonnegative and `N_0 = 1`, so `(Aᵐ)_vv ≥ treeCount q m 0`.
3. Catalan's count (`pow_mul_ballot_le_treeCount`, `ballot_eq_form`, `ballot_zero_right`, `four_pow_le_catalan`): the
   ballot numbers count the paths that stay at or above the root; each step back weighs at least `q`, the ballot theorem
   `ballot i j = C(2i + j, i) − C(2i + j, i − 1)` holds in `ℤ`, so `(A^(2k))_vv ≥ C_k·qᵏ`; and
   `4ᵏ ≤ (2k + 1)(k + 1)·C_k`.
4. The floor (`card_mul_catalan_le_trace`, `floor`, `floor_div`, `floor_half`): `tr A^(2k) = Σ_i λ_i^(2k) ≥ n·C_k·qᵏ`;
   if the count `q + 1` is the mode at `i₀` and every other mode has `|λ_i| ≤ μ`, then
   `n·C_k·qᵏ ≤ (q + 1)^(2k) + (n − 1)·μ^(2k)`.
5. Alon–Boppana in finite form (`alon_boppana`): for every `μ` with `μ² < 4q` there is a size `N = 2(q + 1)^(2k)`
   (the `k` at which `k²·(μ²/4q)ᵏ < 1/12`) such that every complex with `q + 1` darts at every cell and at least `N`
   cells has a mode other than the count with `|λ_i| > μ`.

The reading. The covering tree is the complex unwound, and its closed walks are words of steps out and back, `C_k` of
them for `2k` steps with at least `q` ways for each step back. Every cell of the finite complex holds all of them,
because the walks without backtracking are counts and the first of them is the identity. The trace spends those returns
over the modes: the count takes a fixed `(q + 1)^(2k)`, and the rest must be spread over the other `n − 1`, which then
cannot all stay below `(C_k·qᵏ/2)^(1/2k)`, a number that reaches `2√q` as `k` grows. The half `2√q` is the spectral
radius of the tree's own walk: `trace.regular-zeros-on-circle` places a complex's zeros on the circle when its modes are
inside the band, and this floor says that, in the large, the band cannot be narrowed. The route is algebraic: the
expansion of `Aᵐ` in the `N_j` stands where the textbook proof injects the tree's words into the complex's walks (Alon,
1986; Nilli, 1991, `from training`), so no list of walks is built.

Three forms are not written: the diameter form `λ₂ ≥ 2√q − (2√q − 1)/⌊D/2⌋`; the signed second mode (on a complex with
two sides the mode `−(q + 1)` is among the others, and the statement is spent on it; erasing it too is the same
argument); and the root form `μ ≥ (C_k·qᵏ/2)^(1/2k)` with its limit.

## 6. Guesses and scores, and what follows for the machine

**6.1 Guesses** (fixed in the ruler's source before its first run, scored from its output).

- A: the letterwise triple's laws in integers for `n = 1` to `4`, a word's weight `n − deg`, `Lᵏ` of full rank with
  least singular value `k!`, and the planted sign `H = deg` breaks `[H, U] = −2U`: hit (every ratio 1.000000 on 4 to
  256 words; the planted sign gives `+2U`).
- B: on cyclic covers the orthogonality identity to `1e-9`, the classes adding to `tr Bⁿ`, the deviation within
  `(m − 1)/m` of the largest twisted trace, and a wrong character set misses: hit, with one note. On three bases at
  `m = 2, 3, 5` and lengths 3 to 6 every law held. The first run's planted instance, the characters shifted by a fixed
  residue, multiplies each term by one phase and is not a wrong set, so it did not miss and the run stopped on its
  assert; the planting was replaced before the passing run by characters of order `m + 1`, which miss by 425.469. The
  guess stands as written; the first planting was the ruler's defect.
- C: `(A^(2k))_vv ≥ C_k·qᵏ` at every cell for `k ≤ 8` on random regular multigraphs, the floor holds, the Petersen graph
  has 15 closed walks of length 4 at each cell, and the bound with `(q + 1)ᵏ` fails there: hit (least ratios 1.333,
  1.200, 1.333; Petersen 15 against `C_2·q² = 8`, the planted 18 fails). A reading beside it: two of the three random
  specimens were not tempered (second modes 4.526 against `2√5 = 4.472` and 3.476 against `2√3 = 3.464`), which the
  floor does not need; the Petersen graph, of girth 5, holds the tree's count exactly at length 4.

**6.2 Tests offered** (`agent-inferred`; none run on a learner).

- A carry census of closed strands (§4). In a bank of rings whose contacts carry residues in `ℤ/m`, the closed strands
  sort by their total carry, and one twisted trace per character reads the whole census. A class whose share stands
  above `(m − 1)/m` of the largest twisted trace off `tr Bⁿ/m` is a misread census; a class whose share leaves the
  half's size names the character whose twisted modes left the band.
- The fastest forgetting a large regular contact region can show (§5). A walk on a region with `q + 1` contacts a site
  forgets its start at best at `2√q/(q + 1)` a tick once the region is large (the third record's relaxation reaches it
  only when tempered, and this floor says nothing does better). A reader that reports a large regular region forgetting
  faster has read the region wrong or the region is not regular.
- A face and its mirror are one dimension (§3). Wherever a receiver's states are read by the paired contacts they leave open less
  those they close, a move that closes one pair at a time, with a reversal and a positive pairing, maps the states `m`
  above the balance one-to-one onto those `m` below it, with the constant `m!`; a reading that finds the two sides of
  unequal size has a move without that triple.

**6.3 What does not transfer.** No statement here is about an unending family or a curved space. Each is a construction,
named where its section stands: the Kähler identities on a curved Kähler manifold's harmonic forms, which give a variety
its triple, and the Hodge–Riemann signs against the intersection pairing (§3); the twisted complex's own half, which
would close §4's hypothesis, and the Möbius inversion by holonomy class that carries the density to prime cycles (§4);
the root form of the floor and its diameter form (§5); non-abelian covers.

## 7. Lean, atlas and receipts

**7.1 Lean.** Three modules under `lean/HolonicsResearch/`, each importing Mathlib and earlier modules of the tree.
Each builds with no `sorry`, no added axiom and no `native_decide`, and every audited theorem depends on `propext`,
`Classical.choice` and `Quot.sound` alone.

| Module | Lines | Theorems | Holds |
|---|---|---|---|
| `Hodge/TorusLefschetzTriple` | 464 | 33 | §3: the flat torus's triple and hard Lefschetz by degree |
| `Landmarks/IharaCoverChebotarev` | 373 | 17 | §4: closed walks by holonomy class, Chebotarev at the half |
| `Landmarks/TreeWalkFloor` | 635 | 28 | §5: the covering tree's returns, the floor, Alon–Boppana |

Changed beside them: `Landmarks/IharaAbelianCover` renames its frame change from `fourier` to `charFrame` (with
`charFrame_det_ne_zero`, `coverHashimoto_mul_charFrame` and `cover_mul_charFrame`), because under `open` the name met
Mathlib's `fourier` on the additive circle, and it now holds the second side of the orthogonality (`charFrameInv`,
`charTable_mul_charTableInv`, `charFrameInv_mul_charFrame`, `charFrame_mul_charFrameInv`), which §4 consumes; its header,
`Landmarks/RegularComplexDensityLaw` (the Alon–Boppana limit now points to `TreeWalkFloor.alon_boppana`) and
`Hodge/LefschetzFromPositivity` (its first instance now points to `TorusLefschetzTriple.torusTriple`) gain pointers.
Where it was checked: in this thread's cloud container with the project's pinned toolchain and Mathlib's cached build,
each file by `lake env lean`, and the three with the four changed modules by `bash tools/lean_check.sh` on their module
names (gate 4: 8,740 jobs, exit 0, 00:12:40 to 00:13:11 UTC on November 19, after a merge of `main`). The census
(`tools/lean_census.py`) reads no unbuilt and no unrooted module. The root `HolonicsResearch.lean` gains the three imports.

**7.2 Atlas.** Three rows enter: `hodge.torus-kahler-triple` (targets; an instance of
`hodge.hard-lefschetz-positivity`), `trace.cover-holonomy-equidistribution` and `trace.tree-walk-floor` (geometry).
`trace.abelian-cover-artin` takes the renamed owner and points its unstated splitting to the new row;
`trace.tempered-density-law` points its Alon–Boppana limit to `trace.tree-walk-floor`; `hodge.hard-lefschetz-positivity`
names its first instance.

**7.3 #410.** No open box of #410 names these statements; the set adds to its rows and leaves its boxes as they stand.

**7.4 Receipts.** The ruler, its output and the guesses, named at the head of this record. Its three sections: A the
letterwise triple on `n = 1` to `4` in integers, with singular values of `Lᵏ` between the mirrored degrees; B the
orthogonality identity, the classes' total and the deviation bound on three bases at `m = 2, 3, 5`, lengths 3 to 6; C
the diagonal walk counts and the floor on three random regular multigraphs (30 cells of degree 4, 50 of degree 6, 64 of
degree 4) and the Petersen graph. Each null is held to a planted instance in the same run (the sign `H = deg` in A,
characters of order `m + 1` in B, the bound with `(q + 1)ᵏ` on Petersen in C).
