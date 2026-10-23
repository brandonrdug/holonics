# The contacts are a sheaf, weight tying represents the words, and the square law is the scattering read

October 23. Refs #410, #73.

Brandon offered three papers and a list of disciplines to seed intuition:
- categorical deep learning as monad algebras on parametric maps (Gavranović et al., arXiv
  2402.15332);
- sheaf-theoretic multimodal alignment (Ghalkha et al., arXiv 2510.20540);
- homotopy invariants of learning dynamics (Tamim, arXiv 2510.04376);
- a list ranging from cellular sheaves and Fisher geometry to Mallat's scattering transform.

This record derives the lens and joins it to the owners it touches. It changes no plan item's law
or acceptance. Only the abstracts were read. Grades follow
[the epistemic grades](../../docs/canon/EPISTEMIC_GRADES.md).

## 1. The contacts are a cellular sheaf

[derived] The cellular sheaf is assembled from objects that already exist:

| sheaf | Holonics |
|---|---|
| stalks on the vertices | the participating Holons' states |
| stalk on an edge | a contact's comparison space |
| restriction maps | the contact charts (`v₋ = v₊ ∘ σ` in the helical code) |
| coboundary `δ` | the slip, `(δx)_e = F_(u⊴e) x_u − F_(v⊴e) x_v` |
| sheaf Laplacian `δᵀ W δ` | the contact material `M_contact = Σ w J*DJ`, summed over the contacts |
| Dirichlet energy | `Σ_e w_e Q_e`, the summed quadrance of the slips |

The cohomology reads as follows:
- `H⁰ = ker δ` holds the global sections: the states on which every contact agrees, which is
  where the contacts lock.
- `H¹ = coker δ` holds what cannot glue. The tower's three returns (unique, plural, obstructed;
  `Foundation/ContinuingTower`, `Foundation/GluingPassage`) are a section that is unique, a
  section with a nontrivial kernel, and a nonzero obstruction class.
- With invertible restriction maps (a connection sheaf), a global section exists exactly when
  the holonomy around each cycle fixes it. That is the Bombe's loop closure, and its gauge
  freedom is `cell_flux_is_gauge_free` (`Transport/CellHolonomy`).

Mutual loss is this Dirichlet energy. Its gradient moves both ends of every contact
(`DQ = 2J*Δ`). When the contacts carry declared offsets `b` (lock addresses), the energy is
`‖δx − b‖²_W`. Its minimum leaves the residual `b − δx*`, the projection of `b` off the image of
`δ`, which represents an `H¹` class: what each side keeps unresolved. SheafAlign's case against one shared embedding space, with a comparison space for
each pair instead, is the framework's refusal of a global frame or a global gradient.

## 2. Weight tying represents the words

[derived] A field whose cell `t` applies the move chosen by its symbol is an action of the free
monoid of words `Σ*` on its state. The encoding law `E T_a = U_a E` is a morphism of such actions:
equivariance, which is the paper's monad-algebra morphism. A field can read only what the image of
`Σ*` under its linear part keeps:

| linear part | image of the words | what a readout sees | owner |
|---|---|---|---|
| one `M` for every symbol | the length, `ℕ` | (symbol, lag residue) counts | `laggedRun_lag_residue` |
| commuting, chosen by the symbol | the symbol counts, `ℕ^Σ` | each entry transported by the counts of what followed it | owed (§5) |
| reflections in one plane | the dihedral group | parity and a signed phase sum | `plane_turns_commute` |
| non-commuting | the free monoid | order | the minimal realization, `E T_a = U_a E` |

The paper's "tensor product state preparation" is a matrix product state: the selected matrices
`A_(s_1) ⋯ A_(s_n)`, whose bond dimension is the Hankel rank of the amplitude. The repository
already owns that object read through `|·|²`: the Born face (`HNN/BornFace`), whose density is the
future-sufficient retained quotient (`born_state_future_sufficient`).

The Born face was measured negative on September 26
([record](2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) §2):
- its best register coded 4 + 3/16 bits a cell, against the tree's 3 + 10/16;
- its operators were deposited one cell at a time, by `G = 2(δ/T − 1/Z) A ρ` at the state as it
  stood.

[inferred] That covector does not locate an operator through what it did to the state over the
passage. The forward jet does, but for `χ × χ` operators it costs `χ⁴` per cell, against `K|Σ|`
for `K` scalar modes. Selective state-space models keep their transports diagonal for this reason
and take conjunction from a nonlinear read between levels. In the objects, that read is the tower
with a face between its levels (§4).

## 3. The homotopy of a learning path

[derived] The usable content is already a law. The loss `log R` keeps its winding branch, and the
winding of the ratio around zero is a homotopy invariant of the learning path. Two runs whose
ratios wind differently are not deformable into one another through ratios that do not vanish.
Persistence of minima reads as `tower.filtration-persistence`. The paper is single-author with
large empirical claims, so it is read as a lens only.

## 4. The square law is the scattering read

[derived] Each scalar mode `z' = λ_s z + β_s`, with `λ = r e^(iθ)`, is a causal damped resonator: a
complex wavelet at frequency `θ` and scale `1/(1 − r)`. A bank of such modes is a bank of
parametron rings.

- Reading a mode's face `|z|²` demodulates it, and passing the face on to a slower bank is Mallat's
  scattering cascade.
- The modulus is non-expansive and keeps the energy while moving it toward low frequency. The
  phase it drops is carried into the receiver's kernel, not annihilated (the dissolution account,
  record 2026-10-22 §5).
- A quadratic face reads `z_j z̄_k`, the relative phase between modes, and so pairs of past
  symbols.
- The elementary objects already place this read at the pump. No linear reading followed by a
  threshold reads a relative phase (`no_linear_threshold_reads_relative_phase`). The pump's
  monodromy carries it at second order (`reflection_mul_reflection`), and a bank of receiving
  parametrons at declared pump phases reads its class by its lock pattern (the square law,
  [objects](../../docs/ELEMENTARY_OBJECTS.md)).

[measured] The read is the design's diagonal modes (`K = 8`, turns chosen by the symbol, forward
jets, complex deposit) on the 2,027,360 base-four digits of the repository's own English (record
2026-10-22 §6.6), with η = 0.02 and ρ = 0.95. It is an exterior float read, and the quadratic face
is `a_c += zᴴ H_c z` with `H_c` Hermitian. "Alone" means online over the first 80% and held out
frozen; "with the tree" is prequential.

| face | alone, online | alone, held-out | with the depth-6 tree |
|---|---|---|---|
| none (tree alone) | | | 0.9286 |
| linear, K = 8 | 1.2710 | 1.3878 | 0.9221 |
| linear, K = 16 (record 2026-10-22) | 1.245 | 1.378 | 0.9205 |
| quadratic, K = 8 | 1.2163 | 1.3444 | 0.9196 |

What the table says:
- The square law on eight modes reads more than a linear read of sixteen.
- Joined with the tree it adds 0.009 bits a digit, against 0.0065 for the linear read.
- The tree still holds nearly all the conjunctions within six digits, and the field's reach
  beyond them is small at this width.
- The linear arm reproduces the earlier harness exactly (1.271 and 1.388), which checks the new
  harness.

## 5. The tree's second spectral placement: the passage tree

The design thread measured that diagonal modes add nothing once the receiving tree reaches depth 16
(0.614 against 0.613 bits a cell, GSM8K). It asked what a mode bank should carry that the tree
cannot.

**The bound.** Beyond a tree of depth `D` with context `C_t`, any read adds at most
`I(u_t ; u_(<t−D) | C_t)`. A mode splits as `z_t = N_t + λ^D z_(t−D)` with `N_t` a function of
`C_t`, so only the damped far part can add anything, and a shared read sees it mixed with `N_t`.
At `|λ| = 0.95` a cell the far share of a mode's energy is `|λ|^(2D)`: 0.19 at `D = 16` and 0.085 at
`D = 24`. The bank's memory, `1/(1 − |λ|) = 20` cells, sits inside the tree's horizon.

**The address.** In text, what the far past says given `C_t` is mostly the passage's own
statistics: this problem's names, numbers and units recur, and global counts dilute them. That is
a function of (context, next symbol), which a bank addressed only by the current symbol cannot
hold. A KT count `n(c, a)` is the `λ = 1` mode of the indicator `[context c, next a]`. The passage
term is the same indicator's mode at `λ = 1 − 2^(−m)`, a decayed count `l(c, a)` at every node.
This makes a two-by-two table:

| address | `λ = 1` | `|λ| = 1 − 2^(−m)` |
|---|---|---|
| the current symbol only | unigram counts | the design's diagonal bank |
| tree context | the tree | the passage tree |

In exact arithmetic the decay is a dyadic release with the residue carried
(`CarriedRelease.residueRun_conserves`); the plain floor silences counts below `2^m`
(`plainTransported_silences`). No routine looks up an earlier occurrence. Copying is what the
counts read when the passage repeats itself.

**Measurement.** The read is an exterior float read on the first 1,000 GSM8K training problems,
2,084,620 quarter-character cells, scored before each cell is counted. The tree is context-tree
weighting over depths `0..D`, one tree per frame phase, with each node's estimator
`q(a) = (c_a + ½)/(C + 2)`. The plain tree has `c = n`, and the passage tree has `c = n + w·l`. The
control uses a horizon of `2^24` cells, longer than the passage, so `c ≈ (1 + w) n`: the same
sharpening of the estimator with no locality.

| arm | `D = 16` | `D = 24` |
|---|---|---|
| plain tree | 0.5700 | 0.5553 |
| control, `w = 4` (the best control) | 0.5487 | 0.5288 |
| passage tree, horizon `2^13`, `w = 16` | 0.5139 | 0.5003 |
| passage tree, horizon `2^13`, `w = 64` | | 0.4922 |

- Over the best control, the passage tree gains 0.035 bits a cell at `D = 16` (`w = 16`) and
  0.037 at `D = 24` (`w = 64`), 6 to 7%.
- The gain holds through the passage: in the last quarter, 0.4543 against 0.4921 at `D = 24`.
- A horizon of `2^13` cells (about 2,000 characters, four problems) beats `2^11` (0.5019) and
  `2^15` (0.5068) at `D = 24`.
- The weight is not bracketed: 16, 32 and 64 give 0.5003, 0.4937 and 0.4922.
- The horizon and weight were chosen over 17 arms on the same online run. In the machine they are
  located by deposition, not taken from this grid.
- This tree is weaker than the design's own (0.533 and 0.507 at `D = 16` and `24` on the design's
  rendering of the same 1,000 problems). How much of the gain survives on that tree is not
  measured.

## 6. Owed (#410)

- The summed contact material is the sheaf Laplacian: `Σ_e w_e J_e*DJ_e = δᵀ W δ`, its kernel the
  global sections, and the tower's obstruction the cokernel of `δ`, at the contact and tower
  owners.
- Commuting selected moves see only symbol counts: with linear parts that commute, each entry
  `β(u_t)` reaches the state transported by `∏_a λ_a^(n_a)`, with `n_a` the count of `a` after
  `t` (`Finset.prod_comp`).

## Receipts

- [`quad_field.py`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/quad_field.py),
  output [`quad_field.txt`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/quad_field.txt).
- A development read on 200,000 cells measured at most 114.38 µs a cell (the quadratic face with
  the tree, three runs together). The projection was 232 s and the deadline 240 s.
- The three full runs went together, one thread each: 110.9 s, 176.2 s and 228.3 s, all at 48 to
  49 MiB peak. The ratio of measured to projected for the slowest run is 0.98.
- [`passage_ctw.rs`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/passage_ctw.rs)
  (built with `rustc -O`), the rendering
  [`render_gsm8k.py`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/render_gsm8k.py),
  and every arm's output in
  [`passage_ctw.txt`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/passage_ctw.txt).
  The rendering is `question\nanswer\n` a problem, 153 bytes longer over 100 problems than the
  design's.
- A development read on 100 problems measured at most 12.74 µs a cell, at `D = 24`. Allowing twice
  that for the larger table, the projection was at most 53 s a run, and the deadline was 60 s a run.
  Runs went four together, one thread each. The slowest took 28.0 s (ratio 0.53), with a peak of
  489 MiB.
- No Rust or Lean in the crates or the Lean package changed.
