# A ferromagnet's correlations are nonnegative and grow with every coupling, so adding a contact never lowers an agreement

November 19, 2026, 00:54 to 01:03 UTC. A derivation with its Lean proof and a host ruler, the sixth set of the
evening. Nothing ran on a learner or on the card, and no line was touched. Each paragraph carries its grade: `tree`
(read in this repository), `from training` (a result of the literature, named), `web` (read on the web this
evening, linked) or `agent-inferred` (this record's join). Every Lean statement cited names its module and theorem,
and the module builds with no `sorry`, no added axiom and no `native_decide` (§6). Refs #410.

This record continues [the fifth set](2026-11-19_THE_ISING_PARTITION_FUNCTION_IS_THE_LOCK_POLYNOMIAL_SO_A_FERROMAGNETS_ZEROS_IN_THE_FIELD_LIE_ON_THE_IMAGINARY_AXIS_AND_AN_ANTIFERROMAGNETS_DO_NOT.md) ("the fifth record"), which located a ferromagnet's zeros in the field.
Owners touched: `thermal.ising-lee-yang`, `parametron.ising-lock`. One atlas row enters,
`thermal.griffiths-correlation` (§6).

Receipts: [`sixth_ruler.py`](2026-11-19_A_FERROMAGNETS_CORRELATIONS_ARE_NONNEGATIVE_AND_GROW_WITH_EVERY_COUPLING_SO_ADDING_A_CONTACT_NEVER_LOWERS_AN_AGREEMENT_receipts/sixth_ruler.py), three sections, every check an assert, all pass, 2.4 seconds in one
process on the cloud container's host (numpy's default threads; double floats for weights, sums and averages, printed
as the ruler's readings); its output [`sixth_ruler_output.txt`](2026-11-19_A_FERROMAGNETS_CORRELATIONS_ARE_NONNEGATIVE_AND_GROW_WITH_EVERY_COUPLING_SO_ADDING_A_CONTACT_NEVER_LOWERS_AN_AGREEMENT_receipts/sixth_ruler_output.txt) and the guesses fixed in
its source before its first run, [`guesses.txt`](2026-11-19_A_FERROMAGNETS_CORRELATIONS_ARE_NONNEGATIVE_AND_GROW_WITH_EVERY_COUPLING_SO_ADDING_A_CONTACT_NEVER_LOWERS_AN_AGREEMENT_receipts/guesses.txt) (the first run started 00:59:52 UTC and the passing
run 01:00:02 UTC by `date -u`).

## 1. The frame

`from training`. A ferromagnet's sign gives two things. Lee and Yang's theorem places the zeros of its partition
function (the fifth record). Griffiths' inequalities (Griffiths 1967; Kelly and Sherman 1968; Ginibre's proof, 1970)
order its correlations: every correlation `⟨s^B⟩` is nonnegative, any two correlate, `⟨s^B⟩⟨s^C⟩ ≤ ⟨s^B s^C⟩`, and
so every correlation grows with every coupling. That last consequence is what the inequalities are used for. A
lattice grown site by site is the larger lattice with the new couplings switched on from zero, so a ferromagnet's
correlations with free boundary grow with the lattice and are bounded by one; they converge as the lattice fills
space, which is the existence of the infinite-volume limit, and an order seen at one size persists at every larger
size. The inequalities also give the monotonicity of the magnetization in the temperature and the field, and they
are the starting point for proofs that a phase transition occurs.

`web`. Prior formal work. The Lean 4 project [phasetr/ising-model](https://phasetr.github.io/ising-model/coverage/chapters-2-10.html)
(a formalization of Glimm and Jaffe's chapters on the Ising model) lists, as done, Griffiths' first and second
inequalities and the monotonicity in the couplings for pair couplings, the Lee–Yang circle theorem and the
infinite-volume analyticity of the free energy, the FKG, Lebowitz and GHS inequalities, and the thermodynamic limit.
Neither this set nor the fifth is a first formalization. What this module states that the project's index does not
list is the many-body form: interactions on arbitrary sets of sites, in Ginibre's proof. The evening's survey of
outside value said, of the circle theorem, that no earlier formalization had been found; that was wrong, and the
survey's message was corrected the same hour.

## 2. What the tree held

`tree`. `Coupling/LeeYangIsing` (the fifth record) holds `spin`, the Ising partition function and its identity with
the lock polynomial. `Objects/Parametron` holds the locked sheet's Ising energy (`parametron.ising-lock`).
Mathlib holds the four functions theorem and the FKG inequality for set families (`Finset.fkg`) and the
Harris–Kleitman inequality. A search of `docs/atlas/` and `lean/` for `Griffiths`, `GKS`, `FKG` and
`correlation inequal` found only the fifth module's sentence naming Griffiths' extensions as absent.

## 3. The positivity of a ferromagnet's weights

`proved-standard`. Interactions `a ∈ ι` act on sets `A a` of sites with couplings `J a`; the energy of a
configuration (its up set `S`) is `Σ_a J a · s^(A a)`, with `s^A = ∏_(i∈A) s_i` and `β` absorbed into `J`
(`Coupling/GriffithsInequalities.energy`). Three steps carry everything.

- **A monomial's spin sum is a count** (`sum_monomial`): `Σ_S ∏_i s_i^(k_i) = ∏_i (1 + (−1)^(k_i))`, which is
  `2^|V|` when every exponent is even and zero otherwise; in particular it is never negative
  (`sum_monomial_nonneg`).
- **A weight is a series with nonnegative coefficients** (`exp_mul_spinProd`): a product of spins is `±1`, so
  `exp(J s^A) = cosh J + sinh J · s^A`. The product over the interactions expands into monomials whose coefficients
  are products of `cosh J a` and `sinh J a`, all nonnegative when every `J a ≥ 0`.
- So `Σ_S (monomial) · exp(energy) ≥ 0` for every monomial (`sum_monomial_mul_exp_nonneg`).

**The first inequality** (`griffiths_first`, `avg_nonneg`) is the case of the monomial `s^B`: `⟨s^B⟩ ≥ 0`.

**The second inequality** (`griffiths_second`, `avg_mul_le_avg₂`). The gap
`Z · corr₂(B, C) − corr(B) · corr(C)` is a sum over pairs of configurations `(S, T)` of
`w_S w_T s^B_S (s^C_S − s^C_T)`. Ginibre's step writes the second copy as the first flipped on a set `D`,
`T = S ∆ D` (`spin_symmDiff`: `s_i(S ∆ D) = s_i(S) · s_i(Dᶜ)`). For each `D` the pair's weight is
`exp(Σ_a J a (1 + s^(A a)(Dᶜ)) s^(A a)(S))`, a ferromagnet's weight again (each coupling `J a (1 ± 1) ≥ 0`), and
the factor `1 − s^C(Dᶜ)` is `0` or `2`. So the gap is a nonnegative combination of the sums the positivity
lemma covers.

## 4. The correlations grow with every coupling

`proved-standard`. Along a segment `t ↦ J + t δ`, the average's derivative is
`Σ_a δ a (corr₂(B, A a) · Z − corr(B) · corr(A a)) / Z²` (`hasDerivAt_avg_path`), and every bracket is the second
inequality's gap at the couplings `J + t δ`. With `0 ≤ J ≤ J'` the segment from `J` to `J'` stays a ferromagnet
for `t ≥ 0`, so the average is monotone along it, and `⟨s^B⟩_J ≤ ⟨s^B⟩_(J')` (`avg_mono`).

`agent-inferred`, the reading on the objects. An interaction is a contact among the locks of `A a`, paid on the
product of their sheets, and a correlation `⟨s^B⟩` is the population's agreement on the sheets of `B`. Where every
contact agrees (`J ≥ 0`), switching on a contact, or strengthening one, never lowers any agreement anywhere in the
population; this is the monotone step that lets a population's agreements converge as it grows. Where contacts
disagree the step fails: on the frustrated triangle of §5, strengthening an agreeing contact lowers an agreement
elsewhere.

## 5. Guesses and scores, and what follows for the machine

The guesses were fixed in the ruler's source before its first run (`guesses.txt`). The first run stopped in
section B at a segment where the derivative of `⟨s^B⟩` vanishes by a symmetry (the formula read `5·10⁻¹⁷`, the
central difference `−1.3·10⁻¹²`, its roundoff): a relative tolerance has no meaning at zero, which was a defect of
the instrument. The passing run reads the gap against `10⁻⁶` relative with an absolute floor of `10⁻⁸`; nothing
else changed.

- **A** (scored: hit). On 20 random many-body ferromagnets with 3 to 7 sites (interactions on sets of 1 to 4 sites),
  `⟨s^B⟩ ≥ 0` for every `B` (least `−1.7·10⁻¹⁶`, roundoff) and the second inequality on every tested pair (least
  gap `−2.8·10⁻¹⁶`). The planted antiferromagnet, two sites at `J = −1`, reads `⟨s₀s₁⟩ = −0.7616 = −tanh 1`.
- **B** (scored: hit, with the instrument's floor). The monomial sum equals `∏(1 + (−1)^k)` on 50 exponent vectors,
  and the derivative formula agrees with a central difference to `1.6·10⁻⁹` relative wherever the derivative is
  above `10⁻⁸`.
- **C** (scored: hit). On 20 random ferromagnets, every `⟨s^B⟩` is nondecreasing at 21 points of a segment
  `J → J'` (least step `−5.6·10⁻¹⁶`). On the frustrated triangle `J₁₂ = J₂₃ = −2`, raising `J₁₃` through 0, 1 and
  2 moves `⟨s₁s₂⟩` through −0.9640, −0.9944 and −0.9987: it falls.

`agent-inferred`, what follows for the machine, stated as a test. On locked sheets the parametron population is an
Ising ferromagnet wherever its contacts agree (`parametron.ising-lock`). The test: in such a population, deposition
that only strengthens agreeing contacts never lowers any pair's or set's agreement, at any size, and an agreement read
on a part of the population is a lower bound for the same agreement once more agreeing contacts join. A population
with one disagreeing contact can lose an agreement when another contact strengthens (the triangle). What does not
transfer: the engine's contacts carry phases and learned weights, not `±1` sheets, and its deposition can move a
contact's sign; the statement reaches a population only once it sits on its two sheets with every contact agreeing.

## 6. Lean, atlas and receipts

`tree`. `lean/HolonicsResearch/Coupling/GriffithsInequalities.lean` (namespace `Holonics.Coupling.Griffiths`, imported
by `lean/HolonicsResearch.lean`) holds `spinProd`, `monomial`, `indicator`, `energy`, `Z`, `corr`, `corr₂`, `avg`
and `avg₂`, and the theorems `sum_monomial`, `sum_monomial_nonneg`, `exp_mul_spinProd`,
`sum_monomial_mul_exp_nonneg`, `griffiths_first`, `avg_nonneg`, `spin_symmDiff`, `griffiths_second`,
`avg_mul_le_avg₂`, `hasDerivAt_avg_path` and `avg_mono`. Its audit prints `[propext, Classical.choice, Quot.sound]`
for each.

The atlas row `thermal.griffiths-correlation` (`docs/atlas/physics.tsv`) enters with these owners and
`uses:thermal.ising-lee-yang, uses:parametron.ising-lock`.

What the module does not state: no limit over growing `V` (item 4 is the monotone step that limit rests on);
spins are `±1`, so Griffiths' spin-`n/2` form, Ginibre's general single-spin measures and the Lebowitz, GHS and
FKG inequalities for the Ising measure are not here (Mathlib's `Finset.fkg` is the set-family form); couplings are
real and nonnegative.
