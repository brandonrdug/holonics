# The constraint ecology carrier generalizes the fold across environments

**Date:** 2026-09-17
**Kind:** substrate recovery, one decisive commuting audit with a computational witness, and a
dependency-ordered construction specification. It schedules nothing.
**Authority boundary:** [`docs/plans/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) remains the
sole construction order and [`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) the sole current
position. Neither is modified by this record. The live roadmap carries **no** protein, fold, M5 or
binder line; this record does not add one.
**Truth status:** `established-bounded` for inspected owners and their exact capability;
`counterexample` for the atom→residue restriction verdict; `proved-standard` for the rigidity,
kinetic and thermodynamic identities under their hypotheses; `definition` for the proposed carrier
and receiver atlas; `interpretation` for the tower correspondence; `historical` for external
dataset and publication testimony; `open` for every capability named as missing.
**Evidence:** `source-inspected`, `implemented-exact`, `computational-witness`, `measured`.
**Prior local evidence:**
[the constraint-ecology audit](2026-08-21_THE_FOLD_IS_A_CONSTRAINT_ECOLOGY_THE_ACTIVE_SITE_IS_A_CATALYTIC_RECEIVER_AND_THE_CODEC_RECOVERS_ARCHETYPES.md),
[the M5 return](2026-08-21_THE_FOLD_RETURNED_ITS_CONSTRAINT_COMPLEX_THE_SHARED_JUNCTION_SEPARATED_THE_PRESENTATIONS_AND_M5_PASSED.md),
[the stratified-ecology synthesis](2026-09-02_PROTEIN_FOLDING_IS_A_STRATIFIED_CONSTRAINT_ECOLOGY_AND_GENERATIVE_FLOW_MATCHING_CROSSES_THE_HOLONIC_LATTICE.md).

---

## 0. Ruling

[established-bounded; source-inspected] The repository holds a genuine, exact, protein-agnostic
**representation and analysis substrate** for one contact receiver at one grain in one environment,
plus a single completed case study that used it. It does **not** hold a generator, a rigidity
receiver, a spectral receiver, a topological receiver, a physicochemical receiver, a selection
cascade, an evaluation harness, or any reusable structural-biology intake path.

[established-bounded; source-inspected] **The repository does not establish — and this record does
not claim — that an HNN generates better binders than RFdiffusion, RFdiffusion3, BoltzGen,
BindCraft, PXDesign, Genie3, Proteina-Complexa or any protein language model.** No HNN has ever
generated a protein sequence or backbone here. What is established is that an exact
constraint-incidence calculus transported into real predicted coordinates without a
protein-specific solver, and returned a reconstruction fibre instead of a verdict.

[counterexample; computational-witness] **The atom→residue restriction does not commute with the
tower's own contact law.** It is currently not even a restriction: `crates/holonic-life/examples/m5/cif.rs:247`
discards every non-`CA` atom row at parse time, so no atom-grain face is ever constructed and no
commuting square is ever formed. Where the square can be formed by recomputation from the same
source files, it fails in one direction on 1,070 of the same 70,632 addressed pairs M5 classified.
Section 2 gives the witness.

---

## 1. The recovered substrate

### 1.1 `physical_constraint_complex` — exact, domain-blind, library-resident

[established-bounded; source-inspected] `crates/holonic-engine/src/physical_constraint_complex.rs`
(598 lines) is declared at `crates/holonic-engine/src/lib.rs:301` as `pub mod
physical_constraint_complex;` — a plain `pub mod`, not glob re-exported, so consumers spell the
full path. Its 225-line test module is `crates/holonic-engine/src/physical_constraint_complex/tests.rs`.

**Contact classification law.** `DistanceAperture::classify`
(`physical_constraint_complex.rs:182-190`) over an exact squared-distance interval `D` and exact
squared aperture `a`:

```text
D.upper <= a   ->  Inside     (physical_constraint_complex.rs:183-184)
D.lower >  a   ->  Outside    (physical_constraint_complex.rs:185-186)
otherwise      ->  Open       (physical_constraint_complex.rs:187-188)
```

`ContactClass` is the three-state enum at `:150-154`, wired `Outside=0, Inside=1, Open=2` at
`:157-163`. The squared distance itself is an interval product:
`CoordinateBox3::squared_distance` (`:48-59`) composes `difference` (`:62-67`) and `square`
(`:69-81`); `square` correctly returns lower bound `0` when the interval straddles zero (`:72-76`).
Every coordinate is `ExactInterval { lower: Rat, upper: Rat }`
(`crates/holonic-engine/src/exact_value.rs:90-93`), i.e. `num_rational::BigRational`. **No float
selects a class.** The `Open` state is the load-bearing one: it is the aperture-ambiguous fibre, not
an error.

**1-cell founding.** Two disjoint sources.
*Polygonal* edges are founded in `found` (`:307-309`) from consecutive residues within one
component: `for pair in ids.windows(2) { polygonal_edges.insert(ConstraintEdge::new(pair[0], pair[1])?.0); }`.
*Contact* edges are founded in `found_contact_family` (`:398-401`) **only** for
`ContactClass::Inside` readings. `Open` and `Outside` readings are retained in the family
(`:220-221`: "The complete receiver population, including outside and open pairs") but found no
edge. `ConstraintEdge::new` (`:122-146`) canonicalizes to `lower < upper` and returns the hand
`±1`; a self-loop refuses as `CollapsedEdge`.

**2-cell founding condition.** `:408-427`. A face `[p_i, p_{i+1}, q_j]` is founded **iff** the
polygonal step `p_i → p_{i+1}` exists **and** both contact edges `(p_i,q_j)` and `(p_{i+1},q_j)` are
already in `contact_edges`. The comment at `:406-407` states the rule: "A higher cell is founded by
actual incidence: one polygonal step and two admitted contacts to the same junction. No display
triangulation is promoted into topology."

**Algebraic boundary convention.** `ConstraintFace::boundary` (`:232-240`):
`∂[a,b,c] = [b,c] − [a,c] + [a,b]`, with `ConstraintEdge::new` supplying each edge's hand relative to
canonical orientation and the middle term carrying the extra minus (`:239`). Coefficients accumulate
into `boundary.two_chain_boundary` (`:420-423`) and zero coefficients are pruned (`:428-430`).

**Unresolved-fibre return.** `cross_presentation_fibre` (`:483-549`) compares one lineaged contact
family across two distinct presentation occurrences. It requires equal ordered monomer sequences as
a *kinship witness only* (`:489-493`, error `ComponentSequenceDisagrees` at `:585-589`) and equal
addressed pair order (`:509-511`). It partitions the pair family into five populations —
`shared_inside`, `shared_outside`, `left_only_inside`, `right_only_inside`, `unresolved` — and
returns the lexicographically first `shortest_separator` (`:519-526`, `:530-537`). `CrossPresentationFibre`
is at `:470-479`.

**Admission audit.** `found_contact_family` (`:346-438`) recomputes every class on the CPU from the
exact intervals and refuses with `CarrierDisagrees` (`:378-384`) if the enacted (GPU) class differs,
**before any incidence changes**. Missing uncertainty at any pair refuses (`:395-397`).

[established-bounded; source-inspected] **It is genuinely protein-agnostic.** Confirmed three ways:
its own doc header (`:1-11`: "This owner does not know proteins, atom names, predictors, or
assays"); its import list (`:13-21` — only `EventId`, `ExactInterval`, `Rat`, serde, thiserror,
num-traits; no chemistry, no adapters); and its vocabulary — `ComponentMaterial.lineage` is
documented at `:92` as "Exterior source lineage, retained as testimony and never used as a semantic
taxon", `monomer` is an opaque `String`, and `PresentedComponent.sequence` is a `Vec<String>` used
only for kinship equality. Nothing in the file knows what an amino acid is.

[open] Two structural limits of this owner, both consequential:

1. **It has zero library consumers.** `grep` for `PhysicalConstraintComplex` across `crates/`
   returns only `crates/holonic-life/examples/m5/{fold,visual,artifact}.rs`. Nothing in any `src/`
   tree consumes it.
2. **It is not a `GradedCausalComplex`.** It owns its own `BTreeSet<ConstraintEdge>` /
   `BTreeMap<ConstraintFaceId, ConstraintFace>` incidence and never touches
   `crates/holonic-engine/src/algebraic.rs`'s `GradedCausalComplex` (`found_cell` at `algebraic.rs:314`).
   This single missing adapter is why homology, sheaf Hodge theory, graph receivers and grain
   quotients — all of which already exist — cannot see the fold. See §8.

### 1.2 The environment-indexed protein holon `P_eta`

[definition] From the 2026-08-21 audit `§5` (lines 182-189 of that record), restated verbatim in the
2026-09-02 synthesis `§4.1` (lines 164-176):

```text
P_eta = (V, C_eta, q, F_eta, J_eta, G, E_eta, R_eta, Gamma_eta)
```

- `V` — situated atom/residue/body population (the 0-cells);
- `C_eta` — the **active** constraints in environment `eta` (covalent, H-bond, salt bridge,
  hydrophobic contact);
- `q` — the configuration;
- `F_eta(q) = 0` — the differentiable constraint map;
- `J_eta = D F_eta(q)` — the rigidity Jacobian;
- `G = SE(3)` — the admitted rigid-body gauge;
- `E_eta` — the energy/free-energy section;
- `R_eta` — the receiver family (active sites, allosteric interfaces);
- `Gamma_eta` — the open exterior/reconstruction fibre.

[proved-standard] At a regular configuration (2026-08-21 `§5` lines 194-197; 2026-09-02 `§4.2`
lines 181-183):

```text
infinitesimal motions            = ker J_eta
self-stresses / constraint reactions = ker J_eta^T   (equivalently ker J_eta^*)
internal degrees of freedom      = dim ker J_eta − dim se(3)
```

`ker J_eta` is the **motion** side: what the structure can still do. `ker J_eta^*` is the **reaction**
side: the space of tensions/compressions the bars can carry against each other at zero external
load. The two are not complementary readings of one number. The 2026-08-21 record is explicit
(lines 199-202) that "Degrees of freedom are not obtained by subtracting branch counts
independently. A shared constraint can simultaneously couple distant branches and carry a
reaction/self-stress." 2026-09-02 `§4.2` lines 185-186 states the dynamic law: adjoining a *linearly
independent* contact row decreases `dim ker J_eta` by one (a motion is arrested); adjoining a
*redundant* row enters `ker J_eta^T` as a self-stress, locking the sub-complex against thermal
fluctuation without removing a degree of freedom.

[established-bounded; formal-checked] The repository's formal statement of the shared junction is
`formal/elementary-holonics/ElementaryHolonics/Millennium/Rigidity.lean:263`
(`theSharedJunctionFibreIsTheIntersection`: `ker (F.prod G) = ker F ⊓ ker G`), `:268`
(`removingTheSecondConstraintCanOnlyEnlargeTheFibre`) and `:277`
(`aContinuationSeenOnlyByTheSecondConstraintIsASeparator`). The file's own header (`:41-47`) is
scrupulous: Maxwell counting, Maxwell–Calladine, Connelly super-stability and
Gortler–Healy–Thurston are **cited, not proved and not used**; what is proved is the exact linear
algebra of two named rational witnesses (a braced square at `:74-77`, a collinear triangle at
`:186-188`).

### 1.3 Zipping-and-assembly, contact order, and why Levinthal dissolves

[proved-standard] From the 2026-09-02 record `§2.1`, reading Dill, Ozkan, Shell & Weikl (2008):
the **Zipping and Assembly (ZA)** model says a protein solves its global optimization as a series of
*local* optimizations. Local segments (helices, hairpins) nucleate — "zip" — independently, and
once formed, coalesce — "assemble" — into tertiary motifs (2026-09-02 lines 39).

[proved-standard] The **contact-order relation** (Plaxco, Simons & Baker 1998), 2026-09-02 line 43:

```text
CO = (1 / (L · N_contacts)) · sum over (i,j) in C of |i − j|
```

Proteins dominated by local contacts — low CO, e.g. α-helical bundles — fold orders of magnitude
faster than proteins whose contacting residues are far apart in sequence — high CO, e.g.
antiparallel β-sheets (2026-09-02 line 45). Effective Contact Order (ECO) is the same reading taken
through already-formed structure rather than raw sequence separation.

[interpretation] **Levinthal dissolves because the chain never searches `R^{3N}` unconstrained.**
2026-09-02 lines 48-50, restated: the formation of each local 2-cell acts as a projection map;
*every closed contact adds a row to the constraint Jacobian and immediately contracts `ker J`*. The
folding funnel is then a quotient manifold whose metric is contracted by active constraint
boundaries, not a search heuristic. Low-ECO contacts close first and quench local freedom before
tertiary assembly begins (2026-09-02 line 229), so the accessible configuration volume collapses
multiplicatively along the folding order rather than being enumerated.

[open] This is a correspondence with a live falsifier, not a theorem the repository has proved. Its
first derivation target is exactly the one named in §2: a `J_eta` actually assembled from the
founded 1-cells and 2-cells of a `PhysicalConstraintComplex`, whose `kernel_basis` is exhibited and
whose dimension is watched as contacts are adjoined in ECO order. That object does not exist yet.

### 1.4 The completed RBX1 binder case study (M5)

[established-bounded; implemented-exact; measured] The 2026-08-21 M5 record documents one completed
deed. Precisely what it did:

- **Design UUID binding.** It addressed the documentation/tables tier *first*, selected UUID
  `c29097fd-ea46-5842-8b8f-b38ad7e732ae` (`mythos_preview_multi_target_rbx1_rank05`), and only then
  mounted the five structure/uncertainty payloads that occurrence names. The ~84 GB structure tier
  was never downloaded or scanned. The selection predicate is hard-coded at
  `crates/holonic-life/examples/m5/input.rs:192-198`: `target == "RBX1"`,
  `adaptyv_binding == "binder"`, `twist_binding == "non_binder"`,
  `vendor_agreement == "adaptyv_only_bind"`.
- **Designed vs. predicted as distinct occurrences.** The designed CIF and two Protenix predictions
  returned as *separate* `PhysicalConstraintComplex` values (`m5/fold.rs:225`, `:252`). Equal ordered
  monomer sequences witnessed component kinship; they never identified the occurrences.
- **binary16 PAE decoded to exact dyadic intervals.** Two matrices, `207×207` and `573×573`, carrying
  42,849 and 328,329 finite IEEE binary16 words. Each `<f2` word is decoded by
  `crates/holonic-engine/src/exact_value.rs:1495` `decode_binary16_bits` (module `pub mod ieee754` at
  `:1136`) into its exact dyadic rational, with the format ULP carried **separately**
  (`PairUncertainty.row_given_column_ulp` / `column_given_row_ulp`,
  `physical_constraint_complex.rs:200-201`). Both directions are retained
  (`row_given_column`, `column_given_row`, `:198-199`) because PAE is frame-relative and
  non-symmetric. The record states plainly that PAE is predictor testimony and is not substituted
  for coordinate uncertainty or physical measurement.
- **Inside/Outside/Open residue contacts.** Declared receiver: C-alpha distance ≤ 8 Å
  (`m5/fold.rs:20`, `const CONTACT_RADIUS_ANGSTROMS: u64 = 8`). Coordinates retained as exact decimal
  centres with one full source last-place unit outward, projected outward onto a common
  seven-decimal-place denominator `10,000,000` so the squared aperture fits the resident `u64` law —
  the omitted source refinement stays in the exterior interval fibre, not rounded to a point. Free
  occurrence: 59 inside binder/RBX1 pairs. CUL1-RBX1 occurrence: 45 inside binder/RBX1 and 133
  inside CUL1/RBX1. Higher cells: 16 in the free presentation, 96 across the complex's two families,
  11 surviving in the cross-presentation intersection.
- **Free-RBX1 vs. CUL1-RBX1 environment comparison.** Adaptyv presented free RBX1 and called the
  design a binder; Twist presented the CUL1-RBX1 complex and called it a non-binder. The coordinate
  return *independently* found CUL1 contact with RBX1 residues `19–37, 50, 51, 60, 61, 105–108`, and
  nine of the table-declared designed epitope residues (`21, 23, 24, 27, 28, 30, 31, 33, 37`) lie in
  that set.
- **Shortest structural separator.** Over the complete 10,368-pair binder/RBX1 family: 40
  shared-inside, 10,304 shared-outside, 19 free-only inside, 5 complex-only inside, 0 crossing the
  coordinate aperture ambiguously. The lexicographically first separator is binder local residue 2 /
  RBX1 local residue 23 — inside free, outside in complex.
- **What it explicitly REFUSED to conclude.** M5 record lines 98-102: "the release does not supply a
  calibrated law proving occlusion, binding energetics, assay comparability or a molecular cause.
  The overlap is a load-bearing structural question for a later receiver, not an answer manufactured
  from correlation." It further refused (lines 154-157) any training/cultivation claim: "no returned
  passage changes reusable morphology", and (lines 227-228) folding, chemistry-from-PAE, assay
  causation and reusable protein morphology all remain open. The separator is called "a receiver
  separator between two occurrences with sequence kinship, not evidence that either occurrence is
  the other or that this single contact causes the assay result."

### 1.5 Adapters, and the library/example boundary

[established-bounded; source-audit] The entire structural-biology intake path is **2,608 lines
living inside one example binary's private module tree**. The driver
`crates/holonic-life/examples/the_physical_fold_returns_as_an_exact_constraint_complex.rs` is 42
lines and pulls in six `#[path = "m5/..."]` private modules. Their `pub` markers widen visibility
only *within that binary*; nothing outside it can call them.

| Adapter | Path | Extent | Capability | Library? |
|---|---|---:|---|---|
| mmCIF atom-site reader | `crates/holonic-life/examples/m5/cif.rs:184` `pub fn read` | 382 | One `loop_`, seven required tags, whitespace split; **`:247` filters `label_atom_id == "CA"`**; `:305` `parse_decimal` → exact `Rat` ± one last place; `:356` `one_letter` hard-errors on any non-canonical monomer | **No** |
| PAE / NumPy reader | `crates/holonic-life/examples/m5/npy.rs:123` `pub fn read`, `:63` `pair_uncertainty` | 347 | NPY v1/v2/v3 header, three locked dtypes (`<f2`,`<i4`,`<U`); refuses Fortran order (`:243`) and non-finite binary16 (`:172-176`); builds directional `PairUncertainty` both ways | **No** |
| Release mount | `crates/holonic-life/examples/m5/input.rs:101` `pub fn mount` | 386 | SHA-256-pinned admission of 8 table members + 5 structure payloads; `:340` private CSV parser | **No** |
| Complex assembly / CUDA deed | `crates/holonic-life/examples/m5/fold.rs:96` `pub fn enact` | 686 | Founds both complexes, three contact families, cross-presentation fibre | **No** |
| Mesh + SVG | `crates/holonic-life/examples/m5/visual.rs:57` `pub fn derive`, `:269` `fn svg` | 353 | Exact mesh over denominator `2·d`; hashes topology before/after gauge and refuses a gauge that changed incidence (`:114-128`) | **No** |
| Artifact emission | `crates/holonic-life/examples/m5/artifact.rs:64` `pub fn emit` | 454 | RON/JSON/SVG manifest | **No** |

[established-bounded; source-inspected] **Library-resident and reusable**: the exact binary16 mouth
(`exact_value.rs:1136` `pub mod ieee754`, `:1495` `decode_binary16_bits`, `:1352`
`BinaryFloatDatum::enclosure`, `:1310` `unit_in_last_place`); the constraint owner itself
(`lib.rs:301`); the CUDA contact kernels (`crates/holonic-engine/kernels/refine_shell/refine_shared.cuh:504`
`contact_class_of_pair`, pure integer interval arithmetic returning `1/0/2`;
`kernels/refine_shell/situated_transport.cuh:4` `classify_contact_pairs`;
`:25` `compare_contact_presentations`) and their host binding
(`crates/holonic-engine/src/cuda_refine/device_contact.rs:11` `contact_passage_on_device`,
exported via `cuda_refine.rs:42` and `lib.rs:139`); and the library SVG owner
`crates/holonic-engine/src/presentation_gauge.rs` (`:161` `place`, `:264` `render`, `:321`
`rasterize`) — which `m5/visual.rs` **duplicates instead of composing**, the exact drift
`presentation_gauge.rs:27-34` was written to end.

[open] Explicit missing intake: no general CIF/mmCIF parser (no key-value items, multi-line `;`
fields, multiple data blocks, save frames, altlocs, occupancies, models, hetero/nucleic/ligand
monomers); no `.npz` reader at all (no zip/deflate dependency in either crate — the PAE arrives as a
directory of hand-extracted `.npy` files, `m5/fold.rs:110`, `:115`); no FASTA reader anywhere in the
repository; no PDB-format reader; **no CPU fallback for contact classification** — `m5/fold.rs:181`
hard-requires a CUDA device. No release data is committed: all paths are absolute pointers into
`/home/b/Downloads` with env-var overrides (`m5/input.rs:102-123`).

**Answer to the posed question: M5 exists only as an example driver. There is no reusable library
path for any protein adapter.**

---

## 2. The tower, and the decisive commuting question

### 2.1 The correspondence, stated exactly

[definition] The operator's thesis instantiates the continuing-object/computable-tower pattern as:

| Tower notion | Protein instantiation | Repository status |
|---|---|---|
| index `i` | `(environment eta, grain ∈ {atom, residue, domain}, precision k)` | **absent** — no index type; grain is implicit in what the caller passed to `found` |
| `Face(i)` | the exact constraint complex at that aperture | **present at one index only**: `PhysicalConstraintComplex` |
| restriction `r_{fine→coarse}` | atom → residue → domain coarse graining | **absent, and refuted where reconstructible** (§2.3) |
| `CompatibleSection` | a conformer consistent at every aperture | **absent** |
| `ObservationFibre` | all structures compatible with a predicted face given its PAE interval | **partially present**: `CrossPresentationFibre` retains a two-occurrence fibre; PAE intervals are decoded but never used to widen a coordinate enclosure |
| generators | physical passages (fold, bind, protonate) **and** design passages (mutate, redesign, refold) | **absent** — no passage type; each occurrence is founded independently |
| receivers | interface / rigidity / spectral / topological / physicochemical / assay | **one of six**: the exact geometric interface receiver |

[interpretation] The correspondence is structurally sound and the repository already owns the
abstract machinery for most of it — see §8. What it does **not** own is the law that makes a tower a
tower: the restriction must commute.

### 2.2 The repository already owns the commuting requirement

[definition] This is not an imported standard. Three live clauses state it:

1. `AGENTS.md:307-310`: "A condensation is lawful for the declared future receiver family. Dynamic
   condensation also owes `q T_i = U_i q` for every admitted generator."
2. `docs/HOLON.md:93` (Encode/reopen row): `Ê_next T = U Ê`.
3. `formal/elementary-holonics/ElementaryHolonics/Foundation/ReceiverHistoryCompression.lean:43-45`,
   field `generatorExact`:
   `∀ generator source, present.quotient (sourceTransport generator source) = quotientTransport generator (present.quotient source)`,
   whose consequence `quotientCommutesWithEveryOrderedWord` (`:65`) is discharged with no `sorryAx`
   (`#print axioms` audit at `:154-160`).

[definition] Under this law, a coarse-graining `r` is admissible exactly when, for every admitted
generator `T` of the fine index (here: *found a contact at aperture `a`*, *adjoin a 2-cell*,
*change environment*), there is a coarse generator `U` with `r ∘ T = U ∘ r`. The Lean file's own
finite control (`StaticControl`, `:120-147`) shows why a static agreement is insufficient: two
occurrences agree under the present quotient and receiver, then **one** successor transport
separates them.

### 2.3 Verdict and the computational witness

[counterexample; computational-witness] **The atom→residue restriction does not commute, and it is
not currently even implemented as a restriction.**

*First, the structural finding.* `crates/holonic-life/examples/m5/cif.rs:247` is:

```rust
for row in rows.into_iter().filter(|row| unquote(row[atom]) == "CA") {
```

Every non-CA atom row is discarded before anything is founded. `CifResidue`
(`m5/cif.rs:112-117`) carries `{ source_ordinal, monomer, ca: CifPoint }` — one point. So
`ResidueMaterial.position` (`physical_constraint_complex.rs:87`) is the CA atom's own exact box, not
an aggregate over the residue's atoms. **There is no atom-grain face in the system.** Consequently
there is no commuting square to check, no test asserts one, and the four tests in
`physical_constraint_complex/tests.rs` (`:81`, `:121`, `:179`, `:200`) cover contact founding,
cross-presentation kinship, the `Open` class and carrier disagreement — none covers grain. The tower
law is **assumed, silently, by the act of selecting one atom.**

*Second, the refutation.* Reconstructing both grains from the same three source CIFs at the same
declared 8 Å aperture, in exact rational arithmetic, over exactly the 70,632 addressed pairs M5
classified:

| Occurrence | Family | Pairs | Fine (all-atom) `Inside` | Coarse (CA) `Inside` | Fine-only `Inside` | Coarse-only `Inside` |
|---|---|---:|---:|---:|---:|---:|
| designed free RBX1 | binder × RBX1 | 10,368 | 303 | **64** | 239 | **0** |
| Protenix free RBX1 seed 2 | binder × RBX1 | 10,368 | 366 | **59** | 302 | **0** |
| Protenix CUL1-RBX1 seed 0 | binder × RBX1 | 10,368 | 260 | **45** | 215 | **0** |
| Protenix CUL1-RBX1 seed 0 | CUL1 × RBX1 | 39,528 | 468 | **133** | 314 | **0** |
| | **total** | **70,632** | 1,397 | **301** | **1,070** | **0** |

The coarse column reproduces M5's published counts exactly — 59, 45 and 133 — and the pair totals
reproduce its 10,368-pair family and its 70,632-pair passage, so the apparatus is calibrated against
the recorded deed. Fine-only counts exclude four residues carrying a mispredicted atom more than
12 Å from their own CA (one per structure at most; the census is reported so the witness does not
rest on a predictor artifact). Among the retained fine-only pairs the median CA–CA distance is
9.65–10.44 Å and the maximum is 16.7 Å: these are ordinary side-chain contacts, not outliers.

*The mathematical content of the table.* Writing `F_a` for the fine (min-over-atom-pairs) contact
predicate and `C_a` for the coarse (CA–CA) predicate at the same aperture `a`:

- `C_a ⟹ F_a` holds in all 70,632 pairs, and holds **as a theorem**, not as a measurement: the CA
  atoms are themselves an atom pair, so a CA–CA distance within `a` is a witness for the fine
  predicate. The zero column is therefore expected, and its agreement with the computation is a
  correctness check on the apparatus.
- `F_a ⟹ C_a` fails in 1,070 pairs — **76.6 % of all fine-grain contacts are invisible to the coarse
  receiver at equal aperture.** Side chains touch across a backbone gap the CA representative cannot
  see.

Therefore the square

```text
       atom face  --T_a-->  atom face
           |                    |
         r |                    | r
           v                    v
    residue face --U_a-->  residue face
```

does **not** commute for `T_a = U_a = classify at aperture a`. It commutes only laxly, in one
direction, and only for the `Inside` class; the `Open` class does not transport at all, because the
coarse `Open` is an interval overlap on one CA pair while the fine `Open` is an overlap on a minimum
over many atom pairs.

[definition] **What honest repair looks like.** Three admissible options; the carrier must make the
caller choose one explicitly rather than let the CA filter decide silently:

1. `ApertureRelation::Inflated` — declare a coarse aperture `a_c > a_f` together with an exhibited
   inflation witness (the maximum CA-to-own-atom radius actually present in the mounted material),
   so that `F_{a_f} ⟹ ¬Outside_{a_c}` is a *checked* implication and every residual lands in `Open`.
   This is a lax/monotone restriction, not an isomorphism, and it must say so.
2. `ApertureRelation::Independent` — declare the residue face a genuinely different receiver, retain
   the fine classes in the fibre, and forbid the coarse face from being described as a
   coarse-graining of the fine one.
3. Carry atom grain natively and derive the residue face, with a `GrainRestrictionReceipt`
   recomputed and refused on disagreement — the same discipline `found_contact_family` already
   applies to the GPU carrier at `physical_constraint_complex.rs:378-384`.

[open] Domain grain does not exist in any form. There is no domain population, no CATH/ECOD
ingestion, and no restriction from residue to domain. Nothing about it is refuted; nothing about it
is built.

---

## 3. `EnvironmentIndexedConstraintEcology` — specification

[definition] The carrier generalizing `PhysicalConstraintComplex`. **Specification only; no
implementation is written by this record.** It *wraps* the existing owner and does not replace it:
the exact interval law, the founding conditions and the boundary convention are reused verbatim.

```rust
// ---- index ------------------------------------------------------------------

/// A declared environment. Not a semantic label: it addresses the constitutive
/// conditions every receiver in this ecology is relative to.
pub struct EnvironmentId(pub u64);

pub struct EnvironmentDeclaration {
    pub id: EnvironmentId,
    pub lineage: String,                                  // exterior testimony only
    /// pH, ionic strength, temperature, partner presence, immobilization,
    /// valency, redox, crowding — each an exact interval with an explicit unit chart.
    pub conditions: BTreeMap<ConditionName, TypedInterval>,
    /// The apertures THIS environment declares, per contact family kind.
    pub apertures: BTreeMap<ContactFamilyKind, DistanceAperture>,  // REUSED type
}

pub enum Grain { Atom, Residue, Domain }

pub struct EcologyIndex {
    pub environment: EnvironmentId,
    pub grain: Grain,
    /// Outward projection depth of the coordinate carrier (M5's `10^-7`).
    pub precision: u32,
}

// ---- typed occurrence population --------------------------------------------

pub enum OccurrenceKind {
    Designed { generator: GeneratorId, sequence_method: SequenceMethodId, rounds: u32 },
    Predicted { predictor: PredictorId, seed: u32, stoichiometry: StoichiometryId,
                target_form: TargetFormId },
    Measured { apparatus: ApparatusId, immobilization: ImmobilizationId, valency: Valency },
}

pub struct SourceLineage {
    pub design_uuid: String,             // the release's join key
    pub lineage_family: String,          // e.g. "mythos_preview_multi_target_il7ra"
    pub rank: Option<u32>,
    pub parents: Vec<OccurrenceId>,      // design-passage ancestry
    pub digests: BTreeMap<String, String>,
}

pub struct TypedOccurrence {
    pub id: OccurrenceId,
    pub kind: OccurrenceKind,
    pub lineage: SourceLineage,
    pub index: EcologyIndex,
    /// REUSED VERBATIM. One occurrence, one index, one exact complex.
    pub complex: PhysicalConstraintComplex,
}

// ---- dynamic contact families ------------------------------------------------

/// The edge status. The exact geometric class is NEVER overwritten by it.
pub enum ContactStatus {
    Formed,
    Excluded,
    Open,                                                  // from ContactClass::Open
    KineticallyInaccessible { barrier: ExactInterval, chart: UnitChart },
    EnvironmentDependent { formed_in: BTreeSet<EnvironmentId>,
                           excluded_in: BTreeSet<EnvironmentId>,
                           open_in: BTreeSet<EnvironmentId> },
    Competing { with: Vec<ConstraintEdge>, exclusivity: ExclusivityWitness },
}

pub struct ContactEdgeState {
    pub edge: ConstraintEdge,                              // REUSED
    pub geometric: ContactClass,                           // REUSED, authoritative, immutable
    pub squared_distance: ExactInterval,                   // REUSED
    pub status: ContactStatus,                             // NEW
    pub uncertainty: BTreeMap<ReceiverId, DirectionalUncertainty>,  // NEW (plural)
    pub evidence: EvidenceLineage,                         // NEW
}

/// Generalizes PairUncertainty from one (row|col, col|row) pair to a per-receiver
/// family, each keeping its own direction and its own format ULP.
pub struct DirectionalUncertainty {
    pub receiver: ReceiverId,
    pub source_lineage: String,
    pub forward: ExactInterval, pub forward_ulp: Rat,
    pub reverse: ExactInterval, pub reverse_ulp: Rat,
}

pub struct DynamicContactFamily {
    pub kind: ContactFamilyKind,
    pub left: ConstraintComponentId, pub right: ConstraintComponentId,   // REUSED
    /// One aperture per environment — not one aperture for the family.
    pub apertures: BTreeMap<EnvironmentId, DistanceAperture>,            // REUSED
    pub states: BTreeMap<(u32, u32), ContactEdgeState>,
}

// ---- constitutive content ----------------------------------------------------

pub struct StoredQuantity { pub name: QuantityName, pub value: ExactInterval, pub units: UnitChart }
pub struct Current { pub name: QuantityName, pub flux: ExactInterval,
                     pub units: UnitChart, pub through: BoundaryRef }

// ---- discrete topology-changing events --------------------------------------

/// (K, Theta)_{t+} = Phi_e((K, Theta)_{t-}).
/// K is incidence/transport and Theta constitutive material — the same (K,Θ) object
/// `docs/plans/THE_ROADMAP.md:33` and `docs/HOLON.md:83,:90,:93` already name.
pub enum EcologyEvent {
    Fold { order: FoldingOrder },
    Bind { partner: OccurrenceId, interface: ContactFamilyKind },
    Protonate { site: ConstraintVertexId, p_ka: ExactInterval },
    Mutate { at: ConstraintVertexId, from: String, to: String },
    Redesign { generator: GeneratorId },
    Refold { predictor: PredictorId, seed: u32 },
    EnvironmentChange { from: EnvironmentId, to: EnvironmentId },
}

pub struct EcologyPassage {
    pub event: EcologyEvent,
    pub before: OccurrenceId, pub after: OccurrenceId,
    pub incidence_delta: IncidenceDelta,        // edges/faces founded and withdrawn
    pub constitutive_delta: ConstitutiveDelta,  // stored quantities and currents
}

// ---- restriction (the law §2 refuted) ---------------------------------------

pub enum ApertureRelation {
    Equal,                                    // REFUTED for CA selection — see §2.3
    Inflated { coarse_squared: Rat, witness: InflationWitness },
    Independent,
}

pub struct GrainRestriction {
    pub fine: EcologyIndex, pub coarse: EcologyIndex,
    pub support: BTreeMap<ConstraintVertexId, BTreeSet<ConstraintVertexId>>,
    pub aperture_relation: ApertureRelation,
}

pub struct GrainRestrictionReceipt {
    pub agreeing: usize,
    pub fine_only_inside: Vec<(u32, u32)>,
    pub coarse_only_inside: Vec<(u32, u32)>,
    pub commutes: bool,                       // refuses rather than assumes
}

// ---- retained open relations -------------------------------------------------

pub struct RetainedOpenRelation {
    pub subject: OpenSubject,     // an Open contact, an untested environment, an
                                  // inconclusive assay, an unresolved predictor split
    pub why: String,
    pub closed_by: Vec<ReceiverId>,   // which future receiver would resolve it
}

// ---- the carrier -------------------------------------------------------------

pub struct EnvironmentIndexedConstraintEcology {
    pub schema: String,
    pub environments: BTreeMap<EnvironmentId, EnvironmentDeclaration>,
    pub occurrences: BTreeMap<OccurrenceId, TypedOccurrence>,
    pub families: Vec<DynamicContactFamily>,
    pub restrictions: Vec<(GrainRestriction, GrainRestrictionReceipt)>,
    pub passages: Vec<EcologyPassage>,
    pub stored: BTreeMap<(OccurrenceId, QuantityName), StoredQuantity>,
    pub currents: BTreeMap<(OccurrenceId, QuantityName), Current>,
    pub open: Vec<RetainedOpenRelation>,
}
```

### 3.1 Exactly what is reused and what is new

| Reused verbatim | From |
|---|---|
| `ExactInterval`, interval difference/square/classify | `exact_value.rs:90`; `physical_constraint_complex.rs:48,62,69,182` |
| `ContactClass` three-state law | `physical_constraint_complex.rs:150,182` |
| `DistanceAperture` | `physical_constraint_complex.rs:176` |
| `ConstraintEdge` + canonical hand | `physical_constraint_complex.rs:116,122` |
| `ConstraintFace::boundary` alternating convention | `physical_constraint_complex.rs:232` |
| `PhysicalConstraintComplex` as the per-occurrence face | `physical_constraint_complex.rs:258` |
| exact binary16 → dyadic mouth | `exact_value.rs:1136,1495,1352` |
| integer contact kernel + host binding | `kernels/refine_shell/refine_shared.cuh:504`; `cuda_refine/device_contact.rs:11` |
| Pareto non-domination over declared axes | `resident_section/geometry.rs:309` |

| New | Why the existing owner cannot express it |
|---|---|
| `EnvironmentId` / `EnvironmentDeclaration` / `EcologyIndex` | no index type exists; `PhysicalConstraintComplex` has one implicit grain and no environment |
| `OccurrenceKind` / `SourceLineage` / `TypedOccurrence` | `presentation_lineage: String` is a single opaque string (`:260`) with no typed provenance |
| `ContactStatus` | `ContactClass` is a *geometric* three-state; kinetic inaccessibility, competition and environment dependence are not geometric facts |
| `DirectionalUncertainty` map | `ContactReading.uncertainty` is `Option<PairUncertainty>` — one receiver, one source (`:212`) |
| `DynamicContactFamily` with per-environment apertures | `ContactFamily` holds exactly one `aperture` (`:219`) |
| `StoredQuantity` / `Current` | the complex holds no constitutive content at all |
| `EcologyEvent` / `EcologyPassage` | occurrences are founded independently; there is no passage between them |
| `GrainRestriction` + receipt | §2.3 |
| `RetainedOpenRelation` | `CrossPresentationFibre.unresolved` retains ambiguity for exactly two occurrences of one family; nothing retains an untested environment or an inconclusive assay |

### 3.2 Dependency-ordered build list

[open] Each item names its blocking predecessor. Nothing here is scheduled by this record.

| # | Item | Depends on | Note |
|---|---|---|---|
| **B0** | `GrainRestriction` + `GrainRestrictionReceipt`, regression-tested against the four M5 occurrences | — | **First, because everything downstream assumes it.** The §2.3 table is the fixture. |
| **B1** | `PhysicalConstraintComplex → GradedCausalComplex` adapter | — | **Highest leverage single item.** Unlocks B7, B8, B9 and grain quotients at once. `algebraic.rs:314` `found_cell`. Independent of B0; can proceed in parallel. |
| **B2** | Lift intake into a library crate: all-atom CIF retention, non-canonical monomers, CPU contact fallback | B0 | Removes the `== "CA"` filter (`m5/cif.rs:247`) and makes the CA projection an explicit declared restriction. Needs a `.npz` (zip/deflate) reader or a declared pre-extraction contract. |
| **B3** | `EnvironmentDeclaration`, `EcologyIndex`, `OccurrenceKind`, `SourceLineage`, `TypedOccurrence` | B2 | Pure wrapping; no change to the inner complex. |
| **B4** | `ContactEdgeState`, `ContactStatus`, `DirectionalUncertainty`, `DynamicContactFamily` | B3 | Generalizes `ContactReading`/`ContactFamily`. |
| **B5** | n-way fibre: generalize `cross_presentation_fibre` from 2 occurrences to a family; retain the **separator set**, not the first separator | B4 | `physical_constraint_complex.rs:483` currently returns `Option<ContactSeparator>`. |
| **B6** | `EcologyEvent` / `EcologyPassage` / `Phi_e`, with `IncidenceDelta` and `ConstitutiveDelta` | B4 | The `(K,Θ)` law. |
| **B7** | **Rigidity receiver**: assemble `J_eta` from founded 1-/2-cells; `kernel_basis`, `cokernel_annihilator`, `rank` | B1, B2 | **The largest genuine gap.** No rigidity matrix, self-stress space, rigid-cluster decomposition or pebble game exists anywhere in `crates/`. Needs atom grain (B2) to be physically meaningful. |
| **B8** | **Topological receiver**: Betti/torsion over the founded complex | B1 | `rebase_invariants.rs:723` `rebase_invariants`, `:650` `boundary_matrix`, `:601` `betti_vector` already exist and are exact (Smith normal form over `BigInt`). Only the B1 adapter is missing. |
| **B9** | **Spectral receiver**: contact-graph Laplacian spectrum; sheaf Hodge Laplacian | B1 | `sheaf_diffusion.rs:307` `hodge_laplacian`, `:274` `coboundary`; `lattice_gauge.rs:1039` `exact_spectrum`; `winding_inertia.rs:700` `cycle_laplacian`. Missing: a general (non-circulant) graph Laplacian constructor and harmonic *representatives* (only `harmonic_dimension: usize` at `sheaf_diffusion.rs:577` exists). |
| **B10** | **Physicochemical receiver**: burial, charge complementarity, unsatisfied polars, clashes, composition | B2 | Needs atom grain and a chemical-component table. Entirely new. |
| **B11** | Selection cascade: hard filters → `non_dominated_by` → worst-environment `R(c)` → quality-diversity → structural clustering | B5, B7–B10 | `resident_section/geometry.rs:309` supplies the Pareto rule. |
| **B12** | Design-equivalence law: apply `ReceiverHistoryCompression` to candidate collapse | B11 | §5.2. |
| **B13** | Evaluation splits over the release table | B3 | §6. |
| **B14** | Cost-aware cascade + run receipts recording optimization mode | B11 | §7. |

---

## 4. The receiver atlas

[definition] One predicted occurrence must produce a **receiver vector**, not a score. Six species:

**(1) Exact geometric / interface.** *Exists.* `PhysicalConstraintComplex` — Inside/Outside/Open pair
populations, contact edges, founded 2-cells, algebraic boundary, cross-presentation fibre, shortest
separator. Owner: `physical_constraint_complex.rs`. Exact.

**(2) Rigidity.** *Absent.* Required: `J_eta` assembled from the founded constraints; `nullity =
dim ker J_eta`; rigid-cluster decomposition; hinge (flexible-joint) identification; self-stress space
`ker J_eta^T`; and contact-removal sensitivity — for each contact `c`, the change in `dim ker J_eta`
when `c` is withdrawn, which is exactly the object
`Rigidity.lean:268` `removingTheSecondConstraintCanOnlyEnlargeTheFibre` states abstractly. Available
exact linear algebra: `exact_linear.rs:761` `rank`, `:770` `kernel_basis` (vectors *exhibited*, not
counted), `:796` `image_basis`, `:814` `cokernel_annihilator`, `:823` `preimage_fibre`, `:890`
`factorization`; and `inertia.rs:375` `inertia` returning `(positive, zero, negative)` with
`Inertia::zero` as the nullity of a symmetric form, `:728` `pullback_inertia_bound`. **Everything
needed to compute rigidity exists except the matrix itself.**

**(3) Spectral.** *Partially available, not connected.* Required: contact-graph Laplacian spectrum;
sheaf Hodge-Laplacian spectrum; elastic-network Hessian modes; interface mode participation (what
fraction of a mode's weight sits on interface residues); resolvent amplification; spectral gaps under
mutation and environment change. Available: `sheaf_diffusion.rs:307` `hodge_laplacian(grade)` —
`Δ_k = δ_{k-1}^T δ_{k-1} + δ_k δ_k^T` over `Rat`, exact, built from `:274` `coboundary` on a
`GradedCausalComplex` with stalks and `CellularRestriction` (`:185`); `sheaf_diffusion.rs:939`
`harmonic_dimension = dim C^k − rank Δ_k`; `lattice_gauge.rs:1039` `exact_spectrum` returning
`ExactSpectrum` (`:908`) with exact rational eigenvalues-with-multiplicity, an **unresolved
polynomial factor** for non-rational roots (never approximated), and consecutive-eigenvalue
`intervals` — the nearest thing to a spectral gap in the repository; `exact_linear.rs:336`
`characteristic_polynomial` (Faddeev–LeVerrier, exact); `winding_inertia.rs:589` `winding_inertia`
naming each eigendirection by winding number with Sturm-certified `ExactInterval` isolation (`:490`
`Passage`, `:512` `enclosure`), and `:700` `cycle_laplacian`. **Missing:** a general graph-Laplacian
constructor (only the circulant cycle case exists), harmonic *representatives* (only a dimension
count), no `resolvent` symbol, no `spectral_gap` symbol, no elastic-network Hessian.

**(4) Topological.** *Machinery exists; adapter missing.* Required: loops, entanglement
(knot/knotoid/writhe under a declared closure receiver), contact-community persistence, interface
homology, cavities. Available: `rebase_invariants.rs:723` `rebase_invariants` → `GradeInvariants`
(`:577`, `betti = cells − boundary_rank − filling_rank`, plus integer torsion) via Smith normal form
over `BigInt` (`:440`), `:601` `betti_vector`, `:615` `euler_characteristic`, `:625`
`cell_euler_characteristic` as a cross-check, `:663` `boundary_matrix_on` for a restricted closed
support (directly usable for *interface* homology); `matroid_chow.rs:431` `characteristic_polynomial`.
**Missing:** persistent homology entirely — no `filtration`, `persistence_diagram` or
`persistence_pair` symbol anywhere; no knot/writhe/Gauss-integral owner; no cavity detector.

**(5) Physicochemical.** *Absent entirely.* Burial (relative solvent accessibility), charge
complementarity across the interface, unsatisfied buried polars, steric clashes, composition
statistics. All require atom grain (B2) and a chemical-component table. Nothing exists.

**(6) Assay.** *External testimony, present as data.* Two physically different systems, their
kinetics, expression, aggregation and cross-reactivity panels. §6.

### 4.1 In what sense a protein is a "compressed spectral object"

[definition] The claim is defensible **only relative to a declared atlas**, and with two explicit
guards:

1. **Relative to a declared atlas.** A protein occurrence is a compressed spectral object *for the
   receiver family `R`* when the spectra named in `R` — contact-graph Laplacian, Hodge Laplacian per
   grade, elastic-network Hessian — jointly determine every face `R` admits. This is a statement
   about `R`, never about the protein. Change `R` and the compression changes, exactly as
   `resident_section/geometry.rs:288-289` says of a Pareto front: "Changing the axis set changes the
   set, which is the falsifier: a return that did not move under a changed declaration was ranking."
2. **No single spectrum identifies geometry or function.** Isospectral non-isomorphic graphs exist;
   the Laplacian spectrum does not determine the graph, let alone the embedded geometry, let alone
   the catalytic conduct. A spectral face is a *receiver reading*, and `AGENTS.md:383-385` already
   governs it: "Counts, entropy, loss, accuracy, time and energy are receiver measurements, not
   substitutes for current, lineage, morphology or the full defect."
3. **Spectral equality must preserve a preimage fibre.** When two occurrences agree on every declared
   spectrum, the lawful return is not "they are the same" but "they lie in one retained preimage
   fibre" — exactly `ReceiverHistoryCompression.lean:54` `preimageFibre` and `:58`
   `quotientEqPlacesBothOccurrencesInOneFibre`. And by `:109`
   `separatingSuccessorReopensTheProposedQuotient`, a single admitted future transformation under
   which the two disagree refutes the collapse outright.

[interpretation] So: **a protein is compressible into a spectral chart, and is not identical to
one.** The compression is a declared quotient with a retained fibre and a standing obligation
(`q T_i = U_i q`) for every admitted generator. This is the same clause that §2.3 refutes for the
grain restriction — which is precisely why the restriction must be fixed before any spectral
compression is claimed.

---

## 5. Selection and equivalence

### 5.1 Robust plural selection

[definition] Five stages, in order. `R` is **one receiver**, never a candidate's identity.

1. **Hard physical constraints first.** Expressibility/expression, aggregation, clash, chain-break,
   unsatisfied-buried-polar and sequence-liability filters. These *admit or refuse*; they do not
   score. A refusal is recorded with its reason, not silently dropped.
2. **Pareto filtering over a declared axis set.** `resident_section/geometry.rs:309`
   `non_dominated_by` applies unchanged to any candidate species: each axis is a ratio oriented so
   greater is better, compared by exact `u128` cross-multiplication, and **no axis is summed with
   another** (`:286-288`: "they are different species and a sum would be a scalar governor over
   incomparable coordinates"). Axes here: interface contact count, self-stress redundancy, worst
   directional PAE on interface pairs, buried area, spectral gap, predictor agreement.
3. **Worst-environment ranking.** `R(c) = min over positive environments of the receiver face −
   max over negative environments of the receiver face`. This is deliberately a *minimax over
   declared environments*, so a candidate that excels in one condition and fails in another cannot
   average its way through. It requires the environment index of §3 to exist.
4. **Quality-diversity.** Fill a declared behavioural grid (epitope region × fold class × binder
   length × generator) and keep the best occupant of each cell, so the release is not 200 variants of
   one lineage.
5. **Explicit structural clustering.** Cluster by contact-map overlap and interface identity, and
   release cluster representatives with their cluster retained — never a flat top-N.

[project-postulate] `R(c)` enters the return **as one coordinate of the receiver vector**, alongside
the geometric, rigidity, spectral, topological and physicochemical faces. It is never promoted to
the candidate's identity, and a candidate is never named "the `R = 0.87` design". `AGENTS.md:91-95`
governs exactly this: a scalar may participate in a declared decision law; the prohibited
substitution is "an incidental gauge/apparatus reading or authored score promoted into intrinsic
semantic identity or admission".

### 5.2 The compression law applied to design equivalence

[definition] Two designs may be merged into one equivalence class **only when every declared
receiver, every declared environment and every admitted future transformation agrees.** This is not
a new rule; it is `ReceiverHistoryCompression.lean:87` `allSuccessorHistories` — the quotient is
exact for the receiver family *enlarged by every admitted successor word* — paid for by the local
generator commuting law `:43` rather than by enumerating histories. Its contrapositive `:109`
`separatingSuccessorReopensTheProposedQuotient` is the operative rule: **one separating future
receiver refutes the collapse.** The finite control `:139`
`aStaticCompressionCanReopenUnderOneSuccessor` shows the failure mode concretely: two occurrences
agree on the present quotient *and* the present receiver, then one successor transport separates
them.

### 5.3 Four concrete instances

[established-bounded; measured; source-inspected] All four are checkable in the mounted release
table (`tables/design_summary.csv`, 1,440 rows, 65 columns, 1,440 distinct UUIDs).

**(a) Equal affinity estimate does not imply equal design.**
`mythos_preview_multi_target_trka_rank13` (TrkA, RFdiffusion3, 73 aa) and
`mythos_preview_single_target_trka_rank10` (TrkA, FreeBindCraft, 107 aa) have final apparent
`K_D` of **322.69 nM** and **328.77 nM** — 1.85 % apart — and both bind at both vendors. The first is
a mouse-TrkA **non-binder**; the second binds mouse TrkA at **0.566 nM**. A three-order-of-magnitude
separation on a receiver outside the collapsed set.

**(b) Equal predicted structure does not imply equal behaviour.**
`mythos_preview_multi_target_il7ra_rank01` and `..._rank02` (both PXDesign/SolubleMPNN, both 85 aa,
same target, both `both_bind`) have essentially equal predicted-interface receivers —
`ipsae_min_ptxv2` 0.9075 vs 0.9172, `sc_dockq_ptxv2` 0.96503 vs 0.96286, `sc_dockq_boltz2` 0.93624
vs 0.94945 — while their human `K_D` differ ~5.8× (229.9 vs 1337.6 nM) and their mouse cross-reactivity
differs **qualitatively** (non-binder vs binder at 1140 nM). Equal predicted structure, separated by
the next receiver.

**(c) Equal binding to one homolog does not imply equal cross-reactivity.** Among the 253
`both_bind` designs, mouse outcomes split 122 binder / 78 non-binder / 53 not-tested and cyno
outcomes split 145 / 10 / 98. Six targets (IL-7Ra, PD-L1, TrkA, VEGF-A, EGFR, TNFa) each contain
`both_bind` designs that disagree on mouse binding. Cross-reactivity is a *separate environment*, not
a corollary.

**(d) Equal coarse contact map does not imply equal dynamics.** This is §2.3 turned into a design
statement: 1,070 of 1,397 all-atom contacts in the four RBX1 occurrences are invisible at the CA
receiver. Two designs can share an identical CA contact map while differing in 76 % of their actual
atomic contacts — and therefore in packing, in `ker J_eta`, and in every dynamical face that depends
on side-chain constraint.

**(e) — and a fifth the release forces on us:** equal design does not imply equal assay. The same
design measured in two systems can differ by more than 10× in fitted `K_D` (release reason code
`KD_DIFFERS_GT_10X`, 83 designs); TrkA rank13 above reads 231 nM at Adaptyv and 8,000 nM at Twist.

---

## 6. Evaluation discipline

[established-bounded; source-inspected; measured] The mounted documentation/tables tier
(`/home/b/Downloads/holonics-m5-protein-binder-docs-tables/protein_binder_design_data_release`,
49 MB, SHA-256-pinned at `m5/input.rs:127`) is what the splits must respect. Measured structure:

- 1,440 designs, 1,440 distinct UUIDs, **16 targets** (TNFa 150, Mature GDF-8 120, then 90 each for
  BBF-14, BHRF1, Cas9, EGFR, IL-7Ra, MBP, Nipah-G, PD-L1, RBX1, TREM2, TrkA, VEGF-A; Latent GDF-8 60;
  15-PGDH 30).
- **10 generators**: PXDesign 387, RFdiffusion3 298, Genie3 213, BoltzGen 158, FreeBindCraft
  (BindCraft) 142, RFdiffusion 120, Proteina-Complexa 104, FoldCraft 14, BoltzDesign1 2, Protein
  Hunter 2. **4 sequence-design methods** (SolubleMPNN 1243, Caliby 114, native co-design 62,
  ProteinMPNN 21). 0–26 optimization rounds.
- **10 predictors** with `ipsae_min_*` and `sc_dockq_*` columns each (ef2fast, ef2full, ptxv2, odde,
  afm3, boltz2, chai1, of3, rf3, af3of3); all complete at 1,440 except afm3 at 1,350.
- **Two assay systems with different physics.** `docs/DATA_NOTES.md:7`: Adaptyv immobilized each
  design as a **monovalent** ligand (cell-free expression) with antigen as analyte, SPR single-cycle
  (2,467 replicates) or BLI (345); Twist captured each design as a human **IgG1 Fc fusion** on an
  anti-Fc surface, so the Twist ligand is a **bivalent** design-Fc homodimer for every target.
- **Oligomeric analytes make `K_D` apparent** (`DATA_NOTES.md:9`): VEGF-A, mature GDF-8 and 15-PGDH
  homodimers, TNF-α homotrimer, latent GDF-8 a dimeric pro-complex, Nipah-G ectodomain a tetramer,
  and the Twist RBX1 antigen the CUL1-RBX1 complex. 420 designs carry `assessment_kd_is_apparent`.
- **Vendor agreement**: 846 neither, 253 both, 69 Adaptyv-only, 67 Twist-only, 61 Adaptyv-only-tested,
  19 Twist-only-tested, 5 not tested, 120 blank. 83 designs carry `KD_DIFFERS_GT_10X`.
- **Cross-reactivity panels**: mouse (157 binder / 562 non-binder / 721 untested), cyno (170/429/841),
  CLEC12A (19/426/995), GDF11 (**120 inconclusive, 0 resolved**), Cas9-apo (11/79/1350).
- **48 design-lineage families** by `full_name` prefix (campaign × target), typically 30 ranked
  variants each; `binder_final` 354 True / 966 False / 120 blank; 131 designs have
  `design_model_status == "none"` (absent design complex).

[definition] **Required splits.**

| Split | Group key | What it tests |
|---|---|---|
| Leave-one-target-out | `target` (16 folds) | generalization to an unseen epitope surface |
| Leave-one-interface-family-out | epitope-residue-set clusters within and across targets | generalization to an unseen interface *geometry*, which LOTO does not isolate |
| Leave-one-generator-out | `generator` (10 folds) | whether a receiver learned the generator's stylistic prior instead of physics |
| Assay-specific calibration | `adaptyv_*` and `twist_*` calibrated **separately**, never pooled | the monovalent/bivalent and antigen-form difference is physical, not noise |
| Predictor-disagreement subsets | quantile bands of spread across the 10 `ipsae_min_*` / `sc_dockq_*` pairs | where predicted structure is itself the unresolved variable |
| Positive/negative environment pairs | (human target, mouse ortholog), (target, counter-target), (free antigen, complexed antigen) | the `R(c)` minimax of §5.1 requires matched positive and negative environments |

[project-postulate] **Forbidden: mixing close variants of one design lineage across train and
validation.** Grouping must be by lineage family (`full_name` prefix, 48 groups) — or by sequence
identity cluster where that is tighter — **never by UUID**. Splitting on UUID puts
`..._il7ra_rank01` in train and `..._il7ra_rank02` in validation: same generator, same method, same
length, same target, near-identical predicted interface. That is leakage, and §5.3(b) shows the
receivers that do separate them are exactly the ones a UUID split would never test.

[project-postulate] **Environment-relative disagreement must be preserved, not forced into one
binary label.** Concretely, the following are distinct returns and must never be merged into a single
`binder` bit:

- `both_bind` (253) — agreement;
- `adaptyv_only_bind` (69) and `twist_only_bind` (67) — **environment-relative binding**, attributable
  to valency, immobilization, antigen form or transport, and the M5 RBX1 case study is exactly one of
  these 69;
- `neither_bind` (846) — agreement in refusal;
- `*_only_tested` (80) — **missing testimony**, not a negative;
- blank (120) and GDF11's 120 `inconclusive` — **unresolved**, and per the 2026-08-21 audit line 131
  the mature GDF-8 aggregation case makes the wet-lab question inconclusive "rather than producing
  negative binder labels".

`binder_final` (354 True) is a Claude-applied rubric over the physical testimony, not a measurement
(2026-08-21 record line 133-134). It may be reported as one receiver. It may not be the label.

---

## 7. Hardware reality and the cost-aware cascade

[established-bounded; measured] Apparatus (`AGENTS.md:356-359`,
`docs/AGENT_PROTOCOL.md` apparatus entry): Ryzen 9 7900X, ~30 GiB measured system memory (32 GB
installed), one RTX 4080 SUPER with 16 GiB VRAM, M.2 SSD rated 7300/6300 MB/s. M5's own measured
cost: one card passage classified 70,632 pairs with 694,944 ingress / 81,000 egress / 775,944
resident octets, two kernels, one terminal synchronization; the full driver returned exit zero in
≈61.2 s including the GPU deed, the exact CPU admission audit, a Lean return and complete exterior
serialization.

[definition] **Cost-aware cascade**, widest and cheapest first:

| Stage | Work | Fits in 16 GiB VRAM? |
|---|---|---|
| S1 sequence filters | length, composition, liability motifs, pLM embedding + cheap classifier | **Yes** — small pLMs (≤650 M params) at fp16 are ~1.3 GB weights; batching is the only pressure |
| S2 moderate structural population | monomer folding / fast co-folding at reduced recycling, one seed | **Yes** for binder-sized monomers and small complexes; a 650 M-class folding trunk plus activations for ≤600 tokens fits comfortably |
| S3 constraint / interface receiver | exact contact classification, founded 2-cells, boundary, rigidity (B7), topology (B8) | **Yes, and it is not the binding constraint** — M5's whole resident footprint was 775,944 octets. Exact rational CPU work dominates, not VRAM |
| S4 expensive plural prediction | multiple predictors × multiple seeds × multiple stoichiometries, full PAE | **Conditionally.** Single large co-folding models over ~600-token complexes fit; a full CUL1-RBX1-class complex at high recycling is where 16 GiB binds first. Large stoichiometries and long targets must be run **sequentially, one predictor at a time**, never batched |
| S5 robust diversity release | Pareto (§5.1.2), `R(c)` minimax, quality-diversity grid, clustering | **Yes** — negligible |

[established-bounded] The 573×573 PAE matrix M5 handled carries 328,329 binary16 words ≈ 657 KB raw;
even 10 predictors × 5 seeds × full PAE for one design is tens of megabytes. **PAE is never the
memory constraint.** The 74.5 GB companion structure tier is a *storage and I/O* constraint, and the
2026-08-21 audit's standing rule applies (lines 434-435): admit the documentation tier first, derive a
receiver question, then mount only the addressed payloads — "The 84+ GB structure population is never
downloaded or scanned merely because it exists."

[historical] The operator reports that Anthropic has released optimization kits for open
protein/genomics tools exposing **off / exact / fast / big** modes with explicit activation. **This
is external testimony and is not verified in this repository** — no such kit, mode flag or
activation path exists anywhere under `/home/b/Workspaces/holonics` (searched for `optimization kit`,
mode-name combinations and `*_MODE` environment variables; zero hits).

[project-postulate] Whatever the kit's provenance, the receipt discipline is already
repository law (`AGENTS.md:366-372`, `:380-382`): **any run receipt must record which mode was
active and that mode's numerical scope.** An `exact` mode's result and a `fast` mode's result are
different receiver testimony and must never be reported under one number. A `fast` or `big` mode that
changes numerics silently is the float-decides-topology failure `physical_constraint_complex.rs:9-10`
and `AGENTS.md:388-391` exist to prevent. A mode flag is apparatus testimony, kept separately from
semantic return, exactly as M5 kept device name, warp size and derived block width separate from
contact testimony.

---

## 8. Reusable versus missing — the owner table

[established-bounded; source-inspected]

| Capability | Owner | Status |
|---|---|---|
| Exact interval arithmetic, contact law | `crates/holonic-engine/src/exact_value.rs:90`; `crates/holonic-engine/src/physical_constraint_complex.rs:48,182` | **Reusable** |
| 1-cell / 2-cell founding, algebraic boundary | `crates/holonic-engine/src/physical_constraint_complex.rs:307,408,232` | **Reusable** |
| Two-occurrence reconstruction fibre + separator | `crates/holonic-engine/src/physical_constraint_complex.rs:483` | **Reusable** (2 occurrences only; n-way is B5) |
| Exact binary16 → dyadic PAE mouth | `crates/holonic-engine/src/exact_value.rs:1136,1495,1352,1310` | **Reusable** |
| Integer contact kernel + host binding | `crates/holonic-engine/kernels/refine_shell/refine_shared.cuh:504`; `crates/holonic-engine/src/cuda_refine/device_contact.rs:11` | **Reusable** (no CPU fallback — `crates/holonic-life/examples/m5/fold.rs:181`) |
| Exact rank / kernel / image / cokernel / preimage | `crates/holonic-engine/src/exact_linear.rs:761,770,796,814,823` | **Reusable** |
| Characteristic & minimal polynomial | `crates/holonic-engine/src/exact_linear.rs:336,367` | **Reusable** |
| Sylvester inertia, nullity, congruence, pullback bound | `crates/holonic-engine/src/inertia.rs:375,597,728` | **Reusable** |
| Sheaf coboundary + Hodge Laplacian (exact) | `crates/holonic-engine/src/sheaf_diffusion.rs:274,307` | **Reusable, unreachable** — needs B1 |
| Harmonic *dimension* | `crates/holonic-engine/src/sheaf_diffusion.rs:939,577` | **Reusable** (representatives absent) |
| Exact spectrum, rational eigenvalues, unresolved factor, gaps | `crates/holonic-engine/src/lattice_gauge.rs:908,1039,946` | **Reusable** |
| Cycle Laplacian, winding-named eigendirections, Sturm isolation | `crates/holonic-engine/src/winding_inertia.rs:700,589,490` | **Reusable** (circulant only) |
| Betti + torsion via Smith normal form | `crates/holonic-engine/src/rebase_invariants.rs:440,577,601,650,663,723` | **Reusable, unreachable** — needs B1 |
| Pareto non-domination over declared axes | `crates/holonic-engine/src/resident_section/geometry.rs:309,290` | **Reusable** |
| Receiver-grain quotient (abstract) | `crates/holonic-engine/src/holonic_complex.rs:190,202`; `crates/holonic-engine/src/receiver_ecology.rs:43` | **Reusable, unreachable** — needs B1 |
| Receiver-history compression law (formal) | `formal/.../Foundation/ReceiverHistoryCompression.lean:43,65,87,109,139` | **Reusable** |
| Shared-junction kernel intersection (formal) | `formal/.../Millennium/Rigidity.lean:263,268,277` | **Reusable** |
| Library SVG / gauge owner | `crates/holonic-engine/src/presentation_gauge.rs:161,264,321` | **Reusable** (M5 duplicates it instead) |
| — | — | — |
| **`PhysicalConstraintComplex` → `GradedCausalComplex`** | — | **MISSING (B1)** — blocks homology, Hodge, grain quotient |
| **Grain restriction + commuting receipt** | — | **MISSING (B0)** — and refuted where reconstructible |
| **Atom grain / all-atom CIF** | `crates/holonic-life/examples/m5/cif.rs:247` discards non-CA | **MISSING (B2)** |
| **General CIF/mmCIF, `.npz`, FASTA, PDB readers** | — | **MISSING (B2)** |
| **Reusable library intake path** | all adapters are `examples/m5/*` | **MISSING (B2)** |
| **Rigidity Jacobian, self-stress, rigid clusters, hinges, pebble game** | — | **MISSING (B7)** — nothing in `crates/` |
| **General graph Laplacian, elastic-network Hessian, resolvent, spectral gap symbol** | — | **MISSING (B9)** |
| **Persistent homology, knots/writhe, cavities** | — | **MISSING (B8+)** |
| **Physicochemical receiver** | — | **MISSING (B10)** |
| **Environment index, typed occurrence population, passages** | — | **MISSING (B3, B6)** |
| **Selection cascade, `R(c)`, quality-diversity, clustering** | — | **MISSING (B11)** |
| **Evaluation splits / harness** | — | **MISSING (B13)** |

---

## 9. Falsifiers and scope boundary

[open] This programme refuses, in addition to the sixteen falsifiers standing at
2026-08-21 `§14`:

17. any claim that a coarse contact map is a coarse-graining of an atom contact map without an
    exhibited `GrainRestrictionReceipt` and a declared `ApertureRelation`;
18. any spectral equality reported as identity rather than as placement in a retained preimage fibre;
19. any candidate named by its `R(c)` value, or any selection that sums incomparable receiver axes;
20. any evaluation split grouped by UUID rather than by design lineage;
21. any merge of `adaptyv_only_bind`, `twist_only_bind`, `*_only_tested`, `inconclusive` and blank
    into a single binary label;
22. any run receipt that omits the active optimization mode and its numerical scope;
23. any statement that an HNN designed, generated or improved a binder — no HNN has produced a
    protein sequence, backbone or structure in this repository.

[established-bounded] **What this record establishes:** the exact capability and file:line location
of every relevant owner; that `physical_constraint_complex` is genuinely protein-agnostic and
library-resident with zero library consumers; that the entire structural-biology intake is
example-local; that `PhysicalConstraintComplex` is disconnected from `GradedCausalComplex` and that
this single adapter blocks three existing receiver families; and, with a calibrated computational
witness over the same 70,632 pairs M5 classified, that the atom→residue restriction does not commute
with the contact law.

[open] **What remains open:** everything in the build list B0–B14. In particular, no rigidity
Jacobian has been assembled, no `ker J_eta` has been exhibited for any protein occurrence, no
spectral or topological receiver has ever read a fold, and no generator of any kind has been
connected to this substrate.
