# The M5 design's predicted structures read against its reference presentations

[definition] This experiment runs a real structure predictor on the M5 object's own sequences and
reads the result against the authenticated reference presentations **through the library's existing
receivers**, with a declared passage. It founds nothing. Every number below came out of a command
recorded here; every refusal, failure and undecided reading is reported as such beside the command
that produced it.

Dated 2026-09-19, on tree `9c1ca6d8`. Issues advanced: **#8** (primary), **#9**, **#36**, **#37**,
**#38**.

---

## 0. Notation

`|presentation⟩` is the construction — one mounted alpha-carbon complex. `⟨receiver|` is one of the
three receivers. The bracket `⟨receiver|presentation⟩` is the face this experiment prints. Upper
index is the ket's port (which chain, which residue window), lower index the bra's (which aperture,
which cut).

The general object is the **tube**: the target chain carried along its own residue index. A
**tower** is one instantaneous frame of it — the rigidity Jacobian at one window. The **staircase**
is the passage between grains: the Markov staircase this experiment reads to order 4.

The four slots of every reading below:

| slot | what stands in it |
|---|---|
| source geometry | one presented alpha-carbon complex, exact decimal decoding, `physical_intake` |
| receiver map | the exact 8 Å aperture · the rigidity Jacobian · the cut section |
| transport | `EnvironmentPassage`, declared per ordered pair, naming every divergent axis |
| returned residual | the environment the claim was read at, carried back by the passage itself |

A passage between neighbouring presentations is an arrow: `designed_↗ boltz2` carries the designed
claim downstream to the predicted environment and `designed_↘ boltz2` is its return. The residual
of `_↗` **is** the environment the claim was read at, which is why the comparison does not lose its
site.

---

## 1. What ran

### Predictors installed on this workstation

| kit | version | run here |
|---|---|---|
| Boltz-2 | 2.2.1 (`~/.boltz/boltz2_conf.ckpt`) | **yes**, four predictions |
| torch | 2.14.0+cu130, CUDA 13.0 | — |
| Protenix | **absent** — `importlib.metadata.version('protenix')` raises `PackageNotFoundError` | no |
| Chai-1 (`chai_lab`) | **absent**, same check | no |
| ESM (`esm`) | **absent**, same check | no |
| ProteinMPNN | present at `.local/tools/ProteinMPNN` | no — it is an inverse-folding model, not a structure predictor, so it produces no second presentation of this object |

So there is **one** installed structure predictor. The second and third independent presentations in
the fibre below are the release's two Protenix v2 runs, which were produced elsewhere and are read
here unchanged; the second *Boltz-2* presentation is a second seed, which is a sample of one
predictor and is labelled as such.

### The sequences

Taken from the authenticated mmCIF files' own `_atom_site` rows, never retyped:

```sh
bash research/experiments/m5_predicted_vs_reference/extract_sequences.sh \
    /home/b/Downloads/holonics-m5-rbx1-rank05/designed-free-rbx1.cif
```

- target, 108 monomers: `MAAAMDVDTPSGTNSGAGKKRFEVKKWNAVALWAWDIVVDNCAICRNHIMDLCIECQANQASATSEECTVAWGVCNHAFHFHCISRWLKTRQVCPLDNREWEFQKYGH`
- binder, 96 monomers: `MSPLEEVIEKGEELIRELGEKYNIPKEVTEKLIELFREYLEKYGVSNEAFRNFLKESLEILLKSGVPKEKAFDFVIELGAELTRWLFWKLRQKGLE`

All three reference presentations carry these two sequences identically, and so do the Boltz-2
outputs. Nothing was edited to make the object check pass.

### The four predictions

```sh
cd .local/m5-prediction-2026-09-19
boltz predict inputs/target-only.fasta   --out_dir out-target-only   --use_msa_server \
    --seed 0 --output_format mmcif --write_full_pae --override          # 26 s
boltz predict inputs/binder-target.fasta --out_dir out-binder-target --use_msa_server \
    --seed 0 --output_format mmcif --write_full_pae --override          # 60 s, after two failures
boltz predict inputs/binder-target-seed1.fasta --out_dir out-binder-target-seed1 \
    --seed 1 --output_format mmcif --write_full_pae --override          # 29 s, MSA reused
boltz predict inputs/target-only-seed1.fasta   --out_dir out-target-only-seed1 \
    --seed 1 --output_format mmcif --write_full_pae --override          # 26 s, MSA reused
```

**MSA mode, stated because it changes what the prediction means.** The colabfold MMseqs2 server at
`https://api.colabfold.com` **was** reachable and **was** used. The target chain received a real
MSA of **11,248 rows**. The de novo binder received a **single-sequence** MSA of **1 row** — the
server found no homolog of a designed sequence, which is the expected and honest outcome and not a
fallback. The seed-1 runs reuse the seed-0 MSA files by path, so the only difference between the
two seeds is the seed.

### The failure, in full

Two of the first three complex runs died inside boltz:

```
File ".../boltz/data/msa/mmseqs2.py", line 266, in run_mmseqs2
    with tarfile.open(tar_gz_file) as tar_gz:
tarfile.ReadError: file could not be opened successfully:
- method gz: ReadError('not a gzip file')
```

The file the server returned is JSON:

```json
{"message":"Route GET:/compute/v1/msa/result/download/<hash> not found","error":"Not Found","statusCode":404}
```

The 404 is **intermittent** and hits the paired or the unpaired download arbitrarily — one run got a
valid paired archive and a 404 unpaired archive in the same invocation. boltz 2.2.1 does not check
the HTTP status before handing the body to `tarfile.open`, so a transient server 404 surfaces as a
tar format error. Retrying is the whole workaround; the successful run is the second attempt.

---

## 2. Intake: the environment index, declared honestly

Seven presentations were mounted. The typed environment index has eight axes and refuses unless
every one is declared with a ground or explicitly undeclared with a reason.

| presentation | kind | conformation | oligomeric | cofactors | assay | index provenance |
|---|---|---|---|---|---|---|
| `designed` | designed | `designed_free` | RBX1 1, binder 1 | ZN × 3 | declared: a design generator's structure | declared by caller |
| `protenix-free` | predicted, seed 2 | `predicted_free` | RBX1 1, binder 1 | ZN × 3 | in-silico, Protenix v2 | **read from the run's own `.npz` arrays** |
| `protenix-cul1` | predicted, seed 0 | `predicted_cul1_bound` | RBX1 1, binder 1, CUL1 1 | ZN × 3 | in-silico, Protenix v2 | **read from the run's own `.npz` arrays** |
| `boltz2-complex-seed0` | predicted, seed 0 | `predicted_free` | RBX1 1, binder 1 | **none** | in-silico, Boltz-2 2.2.1, MSA mode in the string | declared by caller |
| `boltz2-complex-seed1` | predicted, seed 1 | `predicted_free` | RBX1 1, binder 1 | **none** | in-silico, Boltz-2 2.2.1, MSA reused | declared by caller |
| `boltz2-target-seed0` | predicted, seed 0 | `predicted_target_alone` | RBX1 1 | **none** | in-silico, Boltz-2 2.2.1 | declared by caller |
| `boltz2-target-seed1` | predicted, seed 1 | `predicted_target_alone` | RBX1 1 | **none** | in-silico, Boltz-2 2.2.1 | declared by caller |

**pH and solvation are undeclared on every presentation, with a stated reason.** No predictor emits
either and the design pipeline records neither; inventing a value would be a default. Because
agreement requires a declaration on both sides, two presentations that are both silent on pH do
**not** agree there, and every passage below must still name that silence.

**The cofactor axis is where Boltz-2 diverges from every reference presentation.** The three
reference files carry three zinc heteroatoms; nothing was supplied to Boltz-2 and nothing is in its
output. The empty ligand complement is that statement, not a default, and it is one of the axes the
`designed_↗ boltz2` passage has to account for. RBX1 is a RING-domain zinc protein, so this is a
real difference in what was folded and not a bookkeeping nicety.

### The object check refuses the target-only predictions at the contact receiver

```
/…/boltz2-target-seed0.cif carries 0 chains of 96 residues, so the address is not unique
```

A prediction of the target alone has no binder, so the 96 × 108 cross family **cannot be addressed
at all**. It is not a presentation of the M5 object at that receiver. It is admitted at the two
single-chain receivers and refused at the contact receiver, and the refusal names the count.
Nothing was edited to force it in.

---

## 3. Receiver 1 — the alpha-carbon contact family (issue #9)

The declared receiver is one contact family at one aperture: the 96 × 108 = **10,368** addressed
alpha-carbon pairs of the binder against the target, at exact squared distance ≤ 64 Å². The counts
are **computed by `PluralFibre`** from that family; none is supplied.

### Per presentation, the exact classes

| presentation | pairs | `Inside` | `Outside` | `Open` |
|---|---|---|---|---|
| `designed` | 10368 | **64** | 10303 | **1** |
| `protenix-free` | 10368 | 59 | 10309 | 0 |
| `protenix-cul1` | 10368 | 45 | 10323 | 0 |
| `boltz2-complex-seed0` | 10368 | 52 | 10316 | 0 |
| `boltz2-complex-seed1` | 10368 | 43 | 10325 | 0 |

The single `Open` reading is the designed structure's, at the 8 Å aperture; it is carried and
counted on neither side, exactly as the owner's law requires.

### The fibre's roles over all five members

| role | contacts |
|---|---|
| unanimously formed | **34** |
| unanimously excluded | **10273** |
| separating | **60** |
| open-carrying | **1** |
| is a partition | yes |

### Pairwise `(agreeing, separating, open-carrying)`

| left | right | agreeing | separating | open-carrying |
|---|---|---|---|---|
| designed | protenix-free | 10338 | 29 | 1 |
| designed | protenix-cul1 | 10337 | 30 | 1 |
| designed | **boltz2-complex-seed0** | **10323** | **44** | 1 |
| designed | **boltz2-complex-seed1** | **10337** | **30** | 1 |
| protenix-free | protenix-cul1 | 10344 | 24 | 0 |
| protenix-free | boltz2-complex-seed0 | 10331 | 37 | 0 |
| protenix-free | boltz2-complex-seed1 | 10344 | 24 | 0 |
| protenix-cul1 | boltz2-complex-seed0 | 10343 | 25 | 0 |
| protenix-cul1 | **boltz2-complex-seed1** | **10362** | **6** | 0 |
| **boltz2-complex-seed0** | **boltz2-complex-seed1** | **10347** | **21** | 0 |

The first three rows of the three-member sub-fibre — `(10338, 29, 1)`, `(10337, 30, 1)`,
`(10344, 24, 0)` — **reproduce the recorded M5 numbers exactly** through an independently written
composition. That is a receipt on the intake path, not a new result.

The new results are the last three rows:

- **Boltz-2's own seed-to-seed separation (21) is of the same order as its separation from the
  designed structure (44 and 30) and larger than the separation between the two Protenix runs
  (24).** A single predicted presentation therefore does not pin down "the prediction" at this
  receiver; seed variance is not a small correction to it.
- **`protenix-cul1` and `boltz2-complex-seed1` are separated by only 6 contacts** — two different
  predictors, under two different declared conditions, agreeing with each other far more closely
  than either agrees with the design.

### The typed refusal, and the passage that lifts it

Comparing two presentations with **no** passage returns, by design:

```
EnvironmentsDiffer { target conformation, pH and protonation assumption,
                     membrane or soluble context, assay format, … }
```

With the passage declared and accounting for exactly those axes:

| passage | axes it must account for | pairs | agreeing | separating |
|---|---|---|---|---|
| `designed_↗ protenix-free` | conformation, pH, solvation, assay | 10368 | 10338 | 30 |
| `designed_↗ protenix-cul1` | conformation, **oligomeric state**, pH, solvation, assay | 10368 | 10337 | 31 |
| `designed_↗ boltz2-complex-seed0` | conformation, pH, solvation, **cofactors**, assay | 10368 | 10323 | 45 |
| `designed_↗ boltz2-complex-seed1` | conformation, pH, solvation, **cofactors**, assay | 10368 | 10337 | 31 |

The separating count here is one higher than the fibre's in every row: `compare_through` is class
identity pair by pair, so the designed structure's single `Open` reading separates there, while the
fibre carries it as open-carrying on neither side. Both readings are correct at their own scope and
the difference is exactly the one undecided contact. The environment the left claim was read at
comes back as the passage's own residual rather than being dropped.

---

## 4. Receiver 2 — rigidity, on two declared windows of the target chain

The same receiver for every presentation: backbone steps as polygonal rows, every pair inside the
exact 8 Å aperture as a contact row, over a 40-residue window. **Two** windows, because the first
one is not representative of the chain.

### Window A, target residues 1–40 — RBX1's N-terminal arm

| presentation | constraints | rank J | dim ker J | internal motions | dim ker Jᵀ | rigid clusters | load-bearing | redundant | inf. rigid |
|---|---|---|---|---|---|---|---|---|---|
| `designed` | 140 | 114 | 6 | **0** | 26 | **1** | 0 | 140 | **yes** |
| `protenix-free` | 123 | 101 | 19 | 13 | 22 | 14 | 29 | 94 | no |
| `protenix-cul1` | 84 | 84 | 36 | 30 | 0 | 31 | 84 | 0 | no |
| `boltz2-complex-seed0` | 129 | 113 | 7 | 1 | 16 | 12 | 44 | 85 | no |
| `boltz2-complex-seed1` | 89 | 87 | 33 | 27 | 2 | 28 | 75 | 14 | no |
| `boltz2-target-seed0` | 120 | 109 | 11 | 5 | 11 | 6 | 47 | 73 | no |
| `boltz2-target-seed1` | 152 | 110 | 10 | 4 | 42 | 5 | 8 | 144 | no |

### Window B, target residues 41–80 — the RING core

| presentation | constraints | rank J | dim ker J | internal motions | dim ker Jᵀ | rigid clusters | inf. rigid |
|---|---|---|---|---|---|---|---|
| `designed` | 153 | 114 | 6 | 0 | 39 | 1 | yes |
| `protenix-free` | 149 | 114 | 6 | 0 | 35 | 1 | yes |
| `protenix-cul1` | 146 | 114 | 6 | 0 | 32 | 1 | yes |
| `boltz2-complex-seed0` | 156 | 114 | 6 | 0 | 42 | 1 | yes |
| `boltz2-complex-seed1` | 160 | 114 | 6 | 0 | 46 | 1 | yes |
| `boltz2-target-seed0` | 163 | 114 | 6 | 0 | 49 | 1 | yes |
| `boltz2-target-seed1` | 158 | 114 | 6 | 0 | 44 | 1 | yes |

**On the core the rigidity receiver cannot separate anything.** `rank J = 114`, `dim ker J = 6` —
the six rigid motions of three-space, nothing internal — and exactly one rigid cluster, in all seven
presentations including the design. Two predictors, four seeds, three declared conditions and the
design all read identically. The **only** channel that still separates them is the self-stress
dimension, 32 to 49, which is the redundancy of the contact graph and tracks the constraint count.

**On the arm only the designed structure is rigid** and every prediction is floppy, from 1 internal
motion to 30. This is not a small effect: it is the difference between a packed arm and an arm that
is free to go anywhere, and it is the same place where the exterior RMSD is 10–23 Å.

### The binder's first twelve residues

| presentation | constraints | rank J | dim ker J | internal | dim ker Jᵀ | clusters |
|---|---|---|---|---|---|---|
| `designed` | 39 | 30 | 6 | 0 | 9 | 1 |
| `protenix-free` | 38 | 30 | 6 | 0 | 8 | 1 |
| `protenix-cul1` | 39 | 30 | 6 | 0 | 9 | 1 |
| `boltz2-complex-seed0` | 38 | 30 | 6 | 0 | 8 | 1 |
| `boltz2-complex-seed1` | 38 | 30 | 6 | 0 | 8 | 1 |

The binder is the thing the design pipeline made, and every predictor reproduces its N-terminal
helix so well that the rigidity receiver separates the five presentations by one self-stress
dimension and nothing else.

---

## 5. Receiver 3 — the hinge section profile, and #38's question

`hinge_by_minimal_section` at interior margin 4 over the same windows. A **local minimum** is a cut
whose section is no greater than either neighbour's, reported once per maximal run at the run's
first cut; a strict inequality would miss every plateau and these profiles are mostly plateaus.

Beside each minimum: **how many maximal rigid clusters straddle it**. That is the reading #38 asks
for. A cut with zero straddling clusters separates rigid bodies. A cut that lies **inside** one
rigid cluster cannot be a conformational hinge whatever its section is: the two sides move together
under every admissible infinitesimal motion, so a narrow section there is a statement about the
contact graph's connectivity at the declared aperture — **packing** — and not about motion.

### Window A, residues 1–40

| presentation | minimal cut | section | clusters straddling it | local minima `(cut, section, straddling)` |
|---|---|---|---|---|
| `designed` | 7 | 9 | **1** | (5,10,1) (**7,9,1**) (13,12,1) (**16,11,1**) (20,15,1) (**23,13,1**) (**26,12,1**) (**30,9,1**) |
| `protenix-free` | 4 | 3 | 2 | (5,3,2) (19,9,1) |
| `protenix-cul1` | 4 | 3 | 2 | (5,3,2) (18,3,2) (21,4,1) (23,3,2) (25,4,1) (27,3,2) |
| `boltz2-complex-seed0` | 23 | 7 | 4 | (6,13,2) (8,11,2) (14,16,3) (**23,7,4**) (26,9,5) (31,9,5) |
| `boltz2-complex-seed1` | 8 | 3 | 2 | (8,3,2) (15,5,1) (17,4,1) (19,3,2) (25,4,1) (27,3,2) (35,4,1) |
| `boltz2-target-seed0` | 4 | 3 | 2 | (9,7,1) (15,15,1) (20,16,1) (27,19,1) (29,20,1) |
| `boltz2-target-seed1` | 36 | 3 | 2 | (10,25,1) (13,30,1) (16,29,1) (20,30,1) |

The designed structure's minima at cuts **7, 16, 23, 26, 30** reproduce the recorded 40-residue scan
exactly. They are **all inside the single rigid cluster** — so on the designed structure not one of
them is a hinge. They are where the contact graph is thinnest.

The minima do **not** recur across presentations here. Cut 23 appears in `designed`, `protenix-cul1`
and `boltz2-complex-seed0`, but it has 1, 2 and 4 clusters straddling it in the three, so it is a
different kind of object in each and the coincidence of the cut index carries no reading.

### Window B, residues 41–80 — where the minima do recur

| presentation | minimal cut | section | local minima `(cut, section, straddling)` |
|---|---|---|---|
| `designed` | 29 | 11 | (**6,14,1**) (**11,16,1**) (16,20,1) (23,18,1) (**29,11,1**) |
| `protenix-free` | 4 | 12 | (**6,14,1**) (**11,17,1**) (16,21,1) (18,20,1) (24,16,1) (**29,12,1**) |
| `protenix-cul1` | 28 | 11 | (**6,14,1**) (**11,15,1**) (16,19,1) (18,18,1) (24,14,1) (**28,11,1**) |
| `boltz2-complex-seed0` | 4 | 12 | (**6,14,1**) (**11,17,1**) (17,22,1) (21,21,1) (**29,12,1**) |
| `boltz2-complex-seed1` | 29 | 11 | (**6,14,1**) (**11,16,1**) (18,20,1) (21,21,1) (**29,11,1**) |
| `boltz2-target-seed0` | 4 | 12 | (**6,14,1**) (**11,18,1**) (18,23,1) (22,24,1) (**29,12,1**) |
| `boltz2-target-seed1` | 4 | 12 | (**6,14,1**) (**11,17,1**) (17,22,1) (22,21,1) (**29,12,1**) |

**Cut 6 is a local minimum with section exactly 14 in all seven presentations.** Cut 11 is a local
minimum in all seven, with sections 15–18. Cut 28 or 29 is a local minimum in all seven, with
sections 11–12. Two independent predictors, four seeds, three declared conditions and the design
place the same three minima at the same cuts with sections agreeing to within 3.

And **every one of those recurring minima has exactly one rigid cluster straddling it.** The window
is infinitesimally rigid in all seven; the cut lies inside the one rigid body.

> **#38, answered on this material.** A section minimum that recurs across predicted and reference
> presentations is **not thereby a conformational hinge**. Recurrence is evidence that the receiver
> is reading the fold rather than one run's noise; it is not evidence of motion. What decides is the
> rigid-cluster straddle count, and here it says 1 everywhere on the core: these are **packing
> features** of the contact graph at the 8 Å aperture. Conversely, where a cut does separate
> clusters — `boltz2-complex-seed0`, window A, cut 23, section 7, four clusters straddling — the
> reading is hinge-shaped, and it appears in exactly the window where the presentations disagree
> most, which is the reading the design itself does not support.

---

## 6. The whole chain reading, on two common 12-residue windows

`elastic_chain` at the interior hinge of the window, read whole: the joint chart is 3 × 12 = 36
coordinates.

### Residues 1–12

| presentation | cut | section | neck rank | rank bound | attained | bound attained | residuals zero | balances | rel. degree | neck | tube sections | analytic width |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `designed` | **8** | **4** | 4 | **4** | **4** | yes | yes / yes | yes | 1 | open | [24,24,4,12,12] | `NotDecidedWithinBound` |
| `protenix-free` | 4 | 3 | 3 | 3 | 3 | yes | yes / yes | yes | 1 | open | [12,12,3,24,24] | `NotDecidedWithinBound` |
| `protenix-cul1` | 4 | 3 | 3 | 3 | 3 | yes | yes / yes | yes | 1 | open | [12,12,3,24,24] | `NotDecidedWithinBound` |
| `boltz2-complex-seed0` | 8 | 4 | 4 | 4 | 4 | yes | yes / yes | yes | 1 | open | [24,24,4,12,12] | `NotDecidedWithinBound` |
| `boltz2-complex-seed1` | 8 | 3 | 3 | 3 | 3 | yes | yes / yes | yes | 1 | open | [24,24,3,12,12] | `NotDecidedWithinBound` |
| `boltz2-target-seed0` | 4 | 3 | 3 | 3 | 3 | yes | yes / yes | yes | 1 | open | [12,12,3,24,24] | `NotDecidedWithinBound` |
| `boltz2-target-seed1` | 4 | 3 | 3 | 3 | 3 | yes | yes / yes | yes | 1 | open | [12,12,3,24,24] | `NotDecidedWithinBound` |

The designed row — **cut 8, section 4, exact transfer rank 4, residuals 0** — reproduces the
recorded designed-structure chain reading exactly.

### Residues 41–52 (the core)

| presentation | cut | section | neck rank | bound | attained | residuals zero | tube sections |
|---|---|---|---|---|---|---|---|
| `designed` | 7 | 8 | 8 | 8 | 8 | yes / yes | [21,21,8,15,15] |
| `protenix-free` | 6 | 9 | 9 | 9 | 9 | yes / yes | [18,18,9,18,18] |
| `protenix-cul1` | 6 | 8 | 8 | 8 | 8 | yes / yes | [18,18,8,18,18] |
| `boltz2-complex-seed0` | 6 | 8 | 8 | 8 | 8 | yes / yes | [18,18,8,18,18] |
| `boltz2-complex-seed1` | 6 | 8 | 8 | 8 | 8 | yes / yes | [18,18,8,18,18] |
| `boltz2-target-seed0` | 6 | 8 | 8 | 8 | 8 | yes / yes | [18,18,8,18,18] |
| `boltz2-target-seed1` | 6 | 8 | 8 | 8 | 8 | yes / yes | [18,18,8,18,18] |

**Every reading of every presentation, on both windows:** the transport residual and the rate-form
residual are exactly zero, the power balance closes, the neck's section bounds the cross-domain
transfer and the bound is **attained** at both probes, the relative degree is 1 and there is no
direct feedthrough.

The neck reads `open` — not `Pinhole` — at grain 2 everywhere, because the section (3 to 9) exceeds
the declared grain. That grain is a declared scope, not a property of the structure.

**The analytic width is `NotDecidedWithinBound { extent: 36, ceiling: 24 }` in all fourteen chain
readings, and no width is invented.** That is issue **#36** on real material, fourteen times.

---

## 7. The exterior float baseline

[definition] **Exterior, float, and load-bearing for nothing.** Cα RMSD after Kabsch superposition,
computed in `f64` inside `mod exterior_float_baseline`, which reads the mmCIF decimal tokens' own
retained strings and never a library value; nothing it returns enters a library call. Verified
against an independent numpy SVD implementation to all printed digits.

| presentation | target 108 | target core 21–108 | window 1–40 | window 41–80 | binder 96 | both 204 |
|---|---|---|---|---|---|---|
| `designed` | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| `protenix-free` | 14.554 | **2.400** | 19.670 | **1.334** | 1.281 | 10.836 |
| `protenix-cul1` | 20.028 | 12.060 | 23.137 | **1.179** | 0.359 | 21.727 |
| `boltz2-complex-seed0` | 10.379 | 8.889 | 10.683 | **1.734** | 0.594 | 8.510 |
| `boltz2-complex-seed1` | 20.147 | 11.039 | 23.340 | **1.950** | 0.969 | 19.381 |
| `boltz2-target-seed0` | 12.186 | 8.802 | 11.468 | **1.972** | — | — |
| `boltz2-target-seed1` | 12.094 | 9.322 | 11.317 | **1.691** | — | — |

The predictor's own confidence, also exterior float
(`predictor_confidence.json`, produced by `predictor_confidence.py`):

| presentation | confidence | pTM | ipTM | mean pLDDT target | core 21–108 | arm 1–20 | binder | mean PAE core | mean PAE interface |
|---|---|---|---|---|---|---|---|---|---|
| `boltz2-target-seed0` | 0.653 | 0.588 | — | 0.670 | 0.710 | 0.493 | — | 10.44 | — |
| `boltz2-target-seed1` | 0.623 | 0.579 | — | 0.634 | 0.666 | 0.490 | — | 11.12 | — |
| `boltz2-complex-seed0` | 0.795 | 0.802 | 0.897 | 0.667 | 0.711 | 0.473 | 0.884 | 8.59 | 12.63 |
| `boltz2-complex-seed1` | **0.859** | 0.830 | **0.938** | 0.773 | 0.801 | 0.649 | 0.913 | 5.50 | 10.18 |

The predictor knows about the arm: its pLDDT on residues 1–20 is 0.47–0.65 against 0.67–0.80 on the
core, in every run. It is the only axis on which its self-report and the exact receivers agree
without qualification.

---

## 8. What agreed, what separated, what failed

### Agreed

- The exact contact numbers `(10338, 29, 1)`, `(10337, 30, 1)`, `(10344, 24, 0)` and the designed
  chain reading `cut 8, section 4, rank 4, residuals 0` reproduce the recorded M5 values through an
  independently written composition.
- On the RING core, **every** receiver except the self-stress dimension agrees across all seven
  presentations: same rank, same kernel, one rigid cluster, the same three section minima, the same
  neck rank and the same attained rank bound.
- The binder — the designed object — is reproduced by both predictors at 0.36–1.28 Å and reads
  identically at the rigidity receiver up to one self-stress dimension.

### Separated

| what separates them | which receiver | which cannot |
|---|---|---|
| designed vs predicted, at the interface | contact family: 29–44 separating of 10368 | rigidity on the core: identical |
| free vs CUL1-bound | contact family (24 separating) and arm rigidity (14 vs 31 clusters) | core rigidity, core chain reading |
| Boltz-2 seed 0 vs seed 1 | contact family, 21 separating — comparable to the designed-vs-predicted gap | core rigidity, core chain reading |
| target-alone vs cofolded (same predictor, same seed) | arm rigidity (6 vs 12 clusters, 120 vs 129 constraints) and the arm chain reading (cut 4 / section 3 vs cut 8 / section 4) | the core rigidity, the core hinge minima and the core chain reading, which are identical; and the contact receiver, which refuses the target-alone presentation by object check rather than reading it |
| the N-terminal arm | rigidity (rigid vs 30 internal motions), hinge profile, RMSD 10–23 Å | the contact family, which addresses no arm-to-arm pair |

The contact receiver and the exterior RMSD **rank the two Boltz-2 seeds oppositely**: seed 1 is
closer to the design at the interface (30 separating against seed 0's 44) while seed 0 is closer in
whole-target RMSD (8.9 Å against 11.0 Å). They are not in conflict — the cross family is the
binder–target interface and the RMSD is the target's own fold — but it is a concrete case where one
number would have hidden the other. The predictor's own confidence ranks seed 1 higher, agreeing
with the contact receiver and not with the RMSD.

### Failed or refused

| what | where |
|---|---|
| colabfold MSA download returned HTTP 404 as a JSON body; boltz 2.2.1 fed it to `tarfile.open` | two of the first three complex runs; fixed by retrying |
| paired MSA is unavailable for a de novo binder | the binder's MSA is 1 row. This is correct, not a failure, and it is stated because it changes what the prediction means |
| the object check refuses the target-only predictions at the 96 × 108 receiver | `carries 0 chains of 96 residues, so the address is not unique` |
| the analytic width | `NotDecidedWithinBound { extent: 36, ceiling: 24 }`, fourteen times (issue #36) |
| the whole 204-monomer complex at the rigidity and chain receivers | **not run.** See cost, below |

---

## 9. Cost

Wall clock, from `std::time::Instant` inside the example, release build, one core.

| step | cost |
|---|---|
| Boltz-2 prediction, 108 tokens, MSA server | 26 s |
| Boltz-2 prediction, 204 tokens, MSA server | 60 s, after two retries |
| Boltz-2 prediction, 204 tokens, MSA reused | 29 s |
| peak GPU memory, 204 tokens | **13,823 MiB device-wide** (desktop baseline 920 MiB), of 16,376 MiB |
| intake of one presentation (read, object check, exact decode, complex, environment) | 1.4 – 444 ms |
| the whole 10,368-pair plural fibre: partition, roles, all 10 pairwise separators | **8.7 ms** |
| `rigidity_reading`, 120 coordinates, 84–163 constraints | 0.8 – 6.8 s |
| `rigid_clusters`, same | 0.03 – 0.26 s |
| `removal_sensitivity`, same | < 1 ms |
| `hinge_by_minimal_section`, 33 cuts, 120 coordinates | 2.2 – 2.9 s |
| the whole chain reading, 36 coordinates | 10.6 – 39.7 s |
| the whole example, 7 presentations × 2 windows | **390.7 s** |

### Where the exact arithmetic is the bottleneck, and what would not scale

- **The contact receiver is not the bottleneck and never will be.** 10,368 exact interval
  classifications plus the complete fibre cost 8.7 ms. At 204 × 204 it would still be milliseconds.
- **`rigidity_reading` is an exact RREF over Q** and its cost is dominated by coefficient growth,
  not by shape: the same 120 × N shape ranges over 0.8–6.8 s depending on the presentation, and the
  slowest is the one with the most constraints and the densest geometry. Scaling to the full
  204-monomer complex means 612 coordinates, about 130× the elimination work before any bit growth
  — hours, not seconds, and the intermediate rationals grow with it.
- **The chain reading is the real wall.** 36 coordinates cost 10–40 s, and the dominant term is the
  pair of exact resolvent inverses on the joint chart. `RESOLVENT_EXTENT_CEILING = 96` already caps
  it at 32 residues. The 204-monomer complex is 612 coordinates: **out of reach today**, by the
  owner's own declared bound and not only by wall clock.
- **The analytic width stops at 24 coordinates** and refused all fourteen times. Every window this
  experiment can afford is already above that ceiling, so the analytic face of the width triple was
  never once available on real material. That is issue #36's whole point, measured.
- **The hinge scan recomputes a full exact RREF per cut** (issue #37): 33 cuts cost 2.2–2.9 s here,
  and consecutive cuts differ by one residue's three columns, so the incremental rank update that
  issue asks for would take the scan to roughly one rank computation plus 32 updates.

---

## 10. Reproducing this

```sh
# 1. the predictions (GPU, one process at a time)
cd .local/m5-prediction-2026-09-19
PATH=/opt/cuda/bin:$PATH ../venv-protein/bin/boltz predict inputs/binder-target.fasta \
    --out_dir out-binder-target --use_msa_server --seed 0 \
    --output_format mmcif --write_full_pae --override      # retry on tarfile.ReadError

# 2. the receivers (exact, over Q)
PATH=/opt/cuda/bin:$PATH cargo run --release -p holonic-engine \
    --example m5_predicted_vs_reference -- \
    --structure-root /home/b/Downloads/holonics-m5-rbx1-rank05 \
    --boltz-root .local/m5-prediction-2026-09-19/presentations \
    --out research/experiments/m5_predicted_vs_reference/receiver_readings.json

# 3. the exterior self-report, and the assembly
.local/venv-protein/bin/python \
    research/experiments/m5_predicted_vs_reference/predictor_confidence.py \
    .local/m5-prediction-2026-09-19 \
    > research/experiments/m5_predicted_vs_reference/predictor_confidence.json
python3 research/experiments/m5_predicted_vs_reference/assemble_results.py
```

Files here:

| file | what it is |
|---|---|
| `receiver_readings.json` | the Rust example's output: every exact reading, over Q |
| `predictor_runs.json` | what the predictor ran, hand-recorded from the commands and their logs |
| `predictor_confidence.json` | Boltz-2's own confidence, exterior float |
| `results.json` | the three above, concatenated, with the float statistics kept in their own branch |
| `inputs/*.fasta` | the two Boltz-2 inputs |
| `extract_sequences.sh` | the sequences, out of the authenticated mmCIF rows |
| `predictor_confidence.py`, `assemble_results.py` | the two small scripts |

Bulk predictor outputs, logs and the staged mmCIF presentations live untracked under
`.local/m5-prediction-2026-09-19/`.

---

## 11. What is **not** decided

- **Nothing here says any prediction is right.** Agreement at a receiver is
  `R`-indistinguishability of the members and never realization; the owner refuses to turn it into
  one, and so does this document. The reference is a *design*, not a measured structure, so
  "predicted against reference" here means "predicted against the design", and no experimental
  structure of this complex entered anything.
- **Five presentations is a small fibre.** The 60 separating contacts and the recurring core minima
  are readings over these five and seven presentations, and a finite reading proves nothing beyond
  its scope.
- **One installed predictor.** Two of the three "independent presentations" at the contact receiver
  come from a predictor that is not installed here and whose runs could not be reproduced. The
  second Boltz-2 presentation is a seed, not an independent model.
- **Whether the recurring core minima are packing in general** is not decided. What is decided is
  that on this material they lie inside a single rigid cluster and therefore are not hinges *here*.
- **The zinc is absent from every Boltz-2 run.** RBX1 is a RING zinc protein; the predictions were
  made without the cofactor the reference files carry. Every reading above that compares Boltz-2
  with a reference presentation is a reading across that axis, and the passage names it.
- **The arm is undecided, not wrong.** Residues 1–20 have pLDDT 0.47–0.65 and 10–23 Å RMSD across
  every presentation including the two references. The receivers report that the presentations
  disagree there; none of them says which one is right, and none can.
- **The 204-monomer complex has not been read** at the rigidity or chain receivers, for the cost
  reasons in §9. Whether the core's receiver agreement survives at full extent is open.
