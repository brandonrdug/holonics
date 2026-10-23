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

## 5. Owed (#410)

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
- No Rust or Lean changed.
