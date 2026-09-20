# The M5 design's predicted structures read against its reference presentations

[historical] Reading order: sections 1–11 retain the first September 19 run, including its
analytic-width refusals and former resolvent limit. Sections 12 onward record the later measured
population and theorem-backed chain. The elastic specialization's structural analytic width is
now decided at admitted extents; the later assembly/arithmetic limits remain. The
[plan audit](../../records/2026-09-19_THE_PLAN_AUDIT_RECONNECTS_SHARED_LAWS_CONSUMERS_AND_HARDWARE.md)
separates these historical measurements from the next conditioned-response construction.

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
    <M5_STRUCTURE_ROOT>/designed-free-rbx1.cif
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
    --structure-root <M5_STRUCTURE_ROOT> \
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

---
---

# 2026-09-20 — a **measured** RBX1 enters, the zinc is supplied, and one seed becomes a population

[definition] Dated 2026-09-20, on tree `c3078f72` (dirty: this directory and
`crates/holonic-engine/examples/m5_predicted_vs_reference.rs`). Issues advanced: **#43**, **#9**,
**#44**. Tracker **#47**. Everything above is unchanged and still reproduces from its own command
line; this section is a second reading of the same three receivers on three new kinds of
presentation, plus one receiver the atlas already owned and the 2026-09-19 run did not use.

The three gaps §11 left open, and what happened to each:

| the gap | what was done | what came out |
|---|---|---|
| no experimentally measured structure had entered anything | three measured RBX1 entries entered through the existing mmCIF intake, one of them a 20-model NMR ensemble | the measured structures separate from **each other** by 40 contacts, and the design is **farther** from them than most predictions are |
| Boltz-2 was run without RBX1's zinc | 16 further runs supplied `ZN × 3` as CCD ion entities, with no positional constraint | Boltz-2 puts the ions in the RING cross-brace unprompted; the zinc **halves** the seed spread and moves the prediction toward the measured structure at the contact receiver, on the arm, and at the exterior RMSD |
| one seed pair showed seed variance of the order of the separation from the design | 8 seeds × 4 conditions = 32 runs, one invocation each | the predictor's seed spread, the NMR ensemble's experimental spread and the predicted-vs-measured separation are **all the same order**, and the zinc is the only thing that changes that |

---

## 12. What ran

### The seed population

32 `boltz predict` invocations, all exit 0 on the first attempt, **no MSA-server call at all**
(one of them, `target-zn` seed 0, was the probe invocation that validated the ion syntax; the
driver then skipped it). Each
`(condition, seed)` is its **own** invocation, because boltz 2.2.1 calls `seed_everything(seed)`
once per process and batching four inputs would make the second input's sampling depend on the
first's.

```sh
cd .local/m5-prediction-2026-09-20
PATH=/opt/cuda/bin:$PATH ../venv-protein/bin/boltz predict inputs/<condition>.yaml \
    --out_dir out/<condition>-seed<S> --seed <S> \
    --output_format mmcif --write_full_pae --override
# conditions: target · target-zn · complex · complex-zn ;  seeds 0..7 ;  driver: run_all.sh
```

| condition | binder | ZN | seeds | wall seconds (min–max) | MSA |
|---|---|---|---|---|---|
| `target` | — | — | 0–7 | 23–36, median 26 | the 2026-09-19 target run's own csv, by path, 11,248 rows |
| `target-zn` | — | 3 | 0–7 | 22–46, median 27 | the same file |
| `complex` | yes | — | 0–7 | 24–43, median 33 | the 2026-09-19 complex run's own two csv files, 11,248 and 1 rows |
| `complex-zn` | yes | 3 | 0–7 | 24–34, median 31 | the same files |

**The MSA server was never contacted**, so issue #46's intermittent 404 could not occur and did
not; the MSA is byte-identical across all 32 runs and the only difference between two runs of one
condition is the seed. An unrelated user process held **5,165 MiB** of the 16,376 MiB device
throughout and every run still fit.

> **Determinism receipt.** The 2026-09-20 `complex` seed-0 run reproduces the 2026-09-19
> `binder-target` seed-0 run's 204 alpha-carbon coordinate tokens **exactly**, although one was
> driven by a FASTA input and the other by a YAML input. The population is therefore a
> continuation of yesterday's runs and not a different experiment.

### The zinc, and the ion syntax that worked

```yaml
sequences:
  - protein: {id: A, sequence: <the 108-mer>, msa: <the 2026-09-19 csv>}
  - ligand:  {id: [C, D, E], ccd: ZN}
```

`boltz predict --help` documents no ion flag; the syntax is the YAML schema's `ligand` entity with
a CCD code, documented in the installed package's `boltz/data/parse/schema.py` docstring. **No
`pocket` and no `contact` constraint was supplied**, so where the three ions went is the
predictor's own statement and not a placement this experiment made.

**Exterior float, load-bearing for nothing:** the four protein atoms nearest each placed ion, in
`boltz2-target-zn-seed0`, are

| ion | nearest four | distance (Å) |
|---|---|---|
| 1 | His80 ND1, Cys83 SG, Cys45 SG, Cys42 SG | 2.16, 2.16, 2.34, 2.49 |
| 2 | His82 ND1, Cys53 SG, … | 2.17, … |

That is RBX1's RING **C3HC4 cross-brace**, which the predictor was not told about. Every ion's
coordination is in `predictor_runs_2026-09-20.json`.

**The zinc broke the intake, and the break is stated.** boltz writes an ion as a `HETATM` row whose
`_atom_site.label_seq_id` is `.`, and `physical_intake::mmcif` requires an integer there. Each
zinc prediction is therefore staged to a `-protein.cif` carrying its `ATOM` rows **verbatim**
before the library reads it; `assemble_manifest.py` does this and records what it dropped.

### The measured structures

Chosen out of an RCSB sequence search of the M5 target's own 108 monomers — extracted by
`extract_sequences.sh` from the authenticated mmCIF rows, never retyped — against experimental
entries at identity cutoff 0.9. **118 polymer entities matched.** Every download is recorded with
its URL and byte count in `predictor_runs_2026-09-20.json`.

| URL | bytes | what |
|---|---|---|
| `https://search.rcsb.org/rcsbsearch/v2/query` (POST) | 7,373 | the sequence search |
| `https://search.rcsb.org/rcsbsearch/v2/query` (POST, verbose) | 111,898 | the same search with every hit's alignment |
| `https://data.rcsb.org/graphql` (POST) | 273,247 | method, resolution, model count, ligands, entities and crystallisation conditions of all 118 entries |
| `https://files.rcsb.org/download/2LGV.cif` | 2,869,696 | **2LGV** |
| `https://files.rcsb.org/download/3DPL.cif` | 447,489 | **3DPL** |
| `https://files.rcsb.org/download/7Z8R.cif` | 1,634,578 | **7Z8R** |

Nothing else was downloaded and nothing was installed.

**The three, and why each.**

| entry | method | resolution / models | chain | aligned to M5 | identity | resolved M5 residues | unresolved | ZN | partners present | pH |
|---|---|---|---|---|---|---|---|---|---|---|
| **2LGV** | solution NMR | — / **20 models** | `A` | M5 12–108 ↔ subject 4–100 | **95.8 %**, 4 mismatches | **9–108**, all 100 in every model | 1–8 | **3** | none: RBX1 alone | undeclared |
| **3DPL** | X-ray | **2.6 Å** | `B` | M5 4–108 ↔ subject 2–106 | 99 %, 1 mismatch | **19–108 less 64–66** (87) | 1–18, 64–66 | **3** | cullin-5 | **8.0**, 277 K |
| **7Z8R** | cryo-EM | **2.7 Å** | `C` | M5 4–108 ↔ subject 2–106 | 99 %, 1 mismatch | **21–106** (86) | 1–20, 107–108 | **3** | CUL1, CAND1 | undeclared |

Three methods, three environments, three ligand-identical (`ZN × 3`) depositions. 2LGV is RBX1
**alone**, which no other measured entry in the search is; 3DPL is the highest-resolution RBX1 in
the whole search; 7Z8R is the measured environment nearest the release's own CUL1-bound predicted
condition.

**The two sequence divergences, named.** 3DPL and 7Z8R differ from the M5 target at exactly one
aligned position (M5 residue 4, `A → S`, an expression remnant) — and that residue is unresolved in
both, so it never reaches a receiver. **2LGV differs at seven:** M5 9–11 are a `GGG` linker and M5
**27, 30, 32, 33** are `W27S, V30S, L32Q, W33S`, the solubilising substitutions that let RBX1 be
studied without a cullin. That is a real difference in what was measured and it is carried, not
smoothed: see §13.

**What the staging filter did**, recorded in `measured_staging.json`: kept the `ATOM` rows of one
`label_asym_id` in one `pdbx_PDB_model_num` that carry an integer `label_seq_id` and are not a
repeated alternate location (there were none in any of the three); copied every coordinate token
**verbatim**; wrote the source's own `_atom_site` header. The library's exact decimal intake
therefore reads the depositor's own decimal strings and **no float exists anywhere on this path**.
The 20 NMR models become 20 separate presentations — the ensemble is a **plural fibre of the
measured presentation**, and model 1 is not picked.

**57 presentations mounted, 0 refused**: 22 measured models, the design, the release's two Protenix
runs, and the 32-run seed population.

---

## 13. The declared receiver for a target-only comparison, and the refusal it has to lift

[definition] A measured RBX1 carries **no binder**, so the 96 × 108 cross family cannot be
addressed at all — exactly the refusal §2 exhibits for the target-only predictions. Forcing the
complex check would be the error. The lawful receiver is the one the object check already licenses
and the 2026-09-19 run did not use: the target chain's **within-component** family,
`Occurrence::founded_family(c, c)`, at the **same exact 8 Å aperture**, over the residues every
member resolves, at a declared minimum chain separation of **3** — `i, i+1` and `i, i+2` are inside
any protein aperture whatever the fold does and carry no reading, and the owner refuses a
separation below 2 as covalent.

Two declared scopes, and the typed refusal between them:

| scope | residues | addressed pairs | members |
|---|---|---|---|
| **commonly resolved** — resolved in every measured model | **83** (21–63, 67–106) | `C(81,2) = ` **3,240** | 37 |
| **commonly resolved and identically typed** — the above, less the four residues 2LGV mutates | **79** | `C(77,2) = ` **2,926** | **57** |

At the 83-residue scope the whole fibre **refuses**, by name:

```
occurrence OccurrenceId(1021) is a face of a different object; a fibre stands over
one candidate and agreement between two candidates narrows nothing
```

That is `FibreRefusal::ObjectDiffersInTheFibre` reading the NMR construct's four substitutions off
the component's own monomer sequence. **All 20 NMR models are excluded there**, and the fibre is
taken over the 37 that share the design's kinship. Dropping the four mutated residues lifts the
refusal and all 57 enter. Nothing was edited to force anything in.

**The unresolved residues are carried, never counted as agreeing.** Residues 1–20, 64–66 and
107–108 are outside the common range because some measured entry does not resolve them, and
`measured_staging.json` lists which entry omits which. A pair touching one of them is **not
addressed at this receiver at all** — it is not classified `Open`, because `Open` is the owner's
name for an exact interval straddling the aperture, and a residue with no coordinate is a different
thing: an absent address, not an undecided distance. Both are reported separately and neither is
counted on either side.

### Per presentation, the exact classes at the 79-residue scope

| presentation | pairs | `Inside` | `Outside` | `Open` |
|---|---|---|---|---|
| `measured-2LGV` (model 1) | 2926 | 176 | 2750 | 0 |
| `measured-3DPL` | 2926 | 165 | 2761 | 0 |
| `measured-7Z8R` | 2926 | **141** | 2785 | 0 |
| `designed` | 2926 | 168 | 2757 | **1** |
| `protenix-free` | 2926 | 175 | 2751 | 0 |
| `protenix-cul1` | 2926 | 161 | 2765 | 0 |
| `boltz2-target` (8 seeds) | 2926 | 156–179 | — | 0 |
| `boltz2-target-zn` (8 seeds) | 2926 | 153–176 | — | 0 |
| `boltz2-complex` (8 seeds) | 2926 | 153–178 | — | 0 |
| `boltz2-complex-zn` (8 seeds) | 2926 | 152–167 | — | 0 |

The fibre over all 57: **105** unanimously formed, **2,471** unanimously excluded, **340**
separating, **10** open-carrying — a partition, computed by `PluralFibre` and supplied by nothing.

---

## 14. The three spreads, as numbers

[definition] This is what issue **#43** asked for. Every entry is a count of separating contacts out
of 2,926, at the 8 Å aperture, over the 79 commonly resolved and identically typed residues, and
every one is `PluralFibre::separator_between`'s own output.

### Within a population — the predictor's seed spread and the experiment's own spread

| population | ordered pairs | min | q1 | **median** | q3 | max |
|---|---|---|---|---|---|---|
| `boltz2-target` — 8 seeds, no zinc | 28 | 29 | 39 | **47** | 59 | 65 |
| `boltz2-target-zn` — 8 seeds, **with zinc** | 28 | 10 | 15 | **21** | 30 | 36 |
| `boltz2-complex` — 8 seeds, no zinc | 28 | 9 | 22 | **32** | 37 | 48 |
| `boltz2-complex-zn` — 8 seeds, **with zinc** | 28 | 9 | 13 | **25** | 28 | 32 |
| **`measured-2LGV` — the 20-model NMR ensemble** | 190 | 17 | 37 | **44** | 52 | 75 |

### Between two measured structures — the experimental spread across methods

| pair | separating |
|---|---|
| `measured-3DPL` vs `measured-7Z8R` (2.6 Å X-ray vs 2.7 Å cryo-EM) | **40** |
| `measured-2LGV` vs `measured-3DPL` (20 pairs) | 62 – **75** – 98 |
| `measured-2LGV` vs `measured-7Z8R` (20 pairs) | 56 – **70** – 90 |

### Predicted against measured

| population | vs `measured-3DPL` | vs `measured-7Z8R` | vs `measured-2LGV` |
|---|---|---|---|
| `boltz2-target` | 33 – **51** – 58 | 37 – **50** – 64 | 47 – **85** – 120 |
| `boltz2-target-zn` | 31 – **34** – 59 | 30 – **42** – 55 | 50 – **72** – 105 |
| `boltz2-complex` | 34 – **44** – 59 | 30 – **39** – 63 | 48 – **74** – 111 |
| `boltz2-complex-zn` | 33 – **40** – 54 | 31 – **38** – 52 | 44 – **71** – 100 |
| `protenix-free` | **50** | **48** | 74 – **84** – 106 |
| `protenix-cul1` | **40** | **48** | 64 – **77** – 102 |
| **`designed`** | **65** | **61** | 80 – **93** – 110 |

> **The answer to #43, on measured material.** Predicted-vs-measured separation (median 34–51
> against the two crystal/cryo-EM structures) is **the same order as** the predictor's own seed
> spread (median 21–47) and **the same order as** the experimental spread between two measured
> structures (40) and within one NMR ensemble (median 44). It is not larger than either. A single
> predicted presentation therefore does not pin down "the prediction" at this receiver, and a
> single measured presentation does not pin down "the structure" either: the 2.6 Å crystal and the
> 2.7 Å cryo-EM model of the same protein separate at 40 of 2,926 contacts, which is more than the
> median distance between two zinc-bearing Boltz-2 seeds.
>
> **And the design is the outlier.** `designed` is 65 and 61 separating contacts from the two
> measured structures — **farther than every predicted population's median**, and farther than
> either Protenix run. On this receiver the predictions agree with measured RBX1 where the design
> does not; the reverse case does not occur.

### Systematic disagreement against sampling

For each measured reference and each 8-seed population: contacts where **every** member differs
from the reference (a systematic property of that condition) against those where the members split
(sampling).

| reference | population | unanimously separating | flipping between seeds |
|---|---|---|---|
| `measured-3DPL` | `boltz2-target` | 13 | **136** |
| `measured-3DPL` | `boltz2-target-zn` | 18 | **61** |
| `measured-3DPL` | `boltz2-complex` | 17 | **79** |
| `measured-3DPL` | `boltz2-complex-zn` | 23 | **56** |
| `measured-7Z8R` | `boltz2-target` | 15 | 136 |
| `measured-7Z8R` | `boltz2-target-zn` | 21 | 61 |
| `measured-7Z8R` | `boltz2-complex` | 13 | 79 |
| `measured-7Z8R` | `boltz2-complex-zn` | 18 | 56 |

**Most of the disagreement with the measured structure is sampling, not systematic**: 3–8 times as
many contacts flip between seeds as are unanimously wrong. Supplying the zinc **more than halves
the flipping set** (136 → 61 for the target alone, 79 → 56 for the complex) while slightly
*raising* the unanimous set — the zinc does not remove the systematic disagreement, it removes the
sampling.

---

## 15. Does the zinc move the prediction toward the measured structure?

| reading | no zinc | with zinc | direction |
|---|---|---|---|
| seed spread, target alone (median separating) | 47 | **21** | **halved** |
| seed spread, complex | 32 | **25** | narrower |
| vs `measured-3DPL`, target alone (median) | 51 | **34** | **toward** |
| vs `measured-3DPL`, complex | 44 | **40** | toward |
| vs `measured-7Z8R`, target alone | 50 | **42** | toward |
| vs `measured-7Z8R`, complex | 39 | **38** | flat |
| flipping contacts vs `measured-3DPL`, target alone | 136 | **61** | **halved** |
| exterior Cα RMSD vs `3DPL`, whole 79-residue range, target alone (median) | 9.55 Å | **4.93 Å** | **toward** |
| exterior Cα RMSD vs `3DPL`, **arm** 21–40, target alone | 9.63 Å | **2.24 Å** | **toward, strongly** |
| exterior Cα RMSD vs `3DPL`, **core** 41–80, target alone | 1.70 Å | 1.73 Å | **flat** |
| Boltz-2's own confidence, target alone (median) | 0.620 | **0.829** | up |
| its own pLDDT on the arm 1–20 (median) | 0.490 | **0.692** | up |

**Yes, and the whole effect is in the arm.** On the RING core the zinc changes nothing the exterior
RMSD can see — 1.70 Å against 1.73 Å — because the core was already right. On the arm it changes
9.63 Å into 2.24 Å. That is the mechanism one would predict from the chemistry: the three ions
staple the cross-brace, and the arm that §4 and issue #44 found floppy in every zinc-free
presentation is the thing they hold.

**And the passage says it too.** With the zinc supplied, the `cofactors and ligands` axis **drops
out** of the declared `EnvironmentPassage` between the measured entry and the prediction, because
both now carry `ZN × 3`:

| passage | axes the passage must account for | separating |
|---|---|---|
| `measured-3DPL_↗ boltz2-target-seed0` | conformation, oligomeric state, pH, solvation, **cofactors**, assay | 43 |
| `measured-3DPL_↗ boltz2-target-zn-seed0` | conformation, oligomeric state, pH, solvation, assay | 59 |
| `measured-3DPL_↗ boltz2-complex-seed0` | conformation, oligomeric state, pH, solvation, **cofactors**, assay | 49 |
| `measured-3DPL_↗ boltz2-complex-zn-seed0` | conformation, oligomeric state, pH, solvation, assay | 54 |
| `measured-3DPL_↗ measured-7Z8R` | conformation, oligomeric state, pH, solvation, assay | 40 |
| `measured-3DPL_↗ designed` | conformation, oligomeric state, pH, solvation, assay | **66** |

Two things are visible at once. The zinc **removes an axis from the passage** — the comparison is
now across one fewer divergence. And **seed 0 is not the median seed**: these rows are single seeds
and the zinc rows happen to be worse than their own population's median (34 and 40), which is
precisely the point §14 makes. A single ordered pair is not the reading; the population is.

Also note that **`measured-3DPL` and `measured-7Z8R` do not compare without a passage either** —
`compare_here` refuses two measured structures of the same protein by the same typed refusal it
gives a prediction, naming conformation, oligomeric state, pH and solvation. The receiver does not
privilege a measurement.

---

## 16. Receiver 2 again — rigidity, on the commonly resolved windows

The same receiver, the same aperture, on the M5 residue index. A step is **polygonal only when the
two occurrences are consecutive in the M5 index**: a measured structure with an unresolved loop has
a jump there and calling it a backbone bond would invent a constraint no presentation carries.
Every presentation reads the same occurrence set, so what differs is geometry and nothing else.

### The core, M5 41–80 ∩ common = **37 residues** (41–63, 67–80)

| presentation | constraints | rank J | dim ker J | internal | self-stress | clusters | inf. rigid |
|---|---|---|---|---|---|---|---|
| `measured-2LGV` m1 | 156 | 104 | 7 | 1 | 52 | 4 | no |
| `measured-2LGV` m2 | 148 | 105 | 6 | 0 | 43 | **1** | **yes** |
| **`measured-3DPL`** | 144 | 105 | 6 | 0 | 39 | **1** | **yes** |
| `measured-7Z8R` | 129 | 103 | 8 | 2 | 26 | 5 | no |
| `designed` | 139 | 104 | 7 | 1 | 35 | 2 | no |
| `protenix-free` | 138 | 104 | 7 | 1 | 34 | 2 | no |
| `protenix-cul1` | 135 | 104 | 7 | 1 | 31 | 2 | no |
| `boltz2-target-seed0` | 138 | 103 | 8 | 2 | 35 | 5 | no |
| `boltz2-target-zn-seed0` | 135 | 103 | 8 | 2 | 32 | 5 | no |
| `boltz2-complex-seed0` | 134 | 104 | 7 | 1 | 30 | 4 | no |
| `boltz2-complex-zn-seed0` | 137 | 104 | 7 | 1 | 33 | 4 | no |

**This is not §4's result and the difference is the receiver, not the material.** §4 read a
contiguous 40-residue core and found *every* presentation infinitesimally rigid with one cluster.
Removing residues 64–66 — which two of the three measured entries do not resolve — breaks the chain
and the window stops being rigid for almost everything. The highest-resolution measured structure
is one of only two presentations that stay rigid across the break. **A window is a declaration, and
changing it changes what the receiver can say**: that is issue **#44**'s point, now with a second
instance.

### The whole commonly resolved and typed range, **79 residues, 237 exact coordinates**

Taken on a declared short list — every measured reference's first model, the design, both
Protenix runs and **seed 0** of each predicted condition — because the exact RREF at 237
coordinates costs 14–53 s per presentation and the whole 57 would have been half an hour for
this one table. The cost is the reported cost.

| presentation | constraints | rank J | dim ker J | internal | self-stress | clusters | `rigidity_reading` cost |
|---|---|---|---|---|---|---|---|
| `measured-2LGV` m1 | 324 | 213 | 24 | 18 | 111 | 15 | 14.3 s |
| `measured-3DPL` | 311 | 216 | 21 | 15 | 95 | 8 | 18.6 s |
| `measured-7Z8R` | 288 | 214 | 23 | 17 | 74 | 12 | 20.0 s |
| `designed` | 320 | 224 | 13 | 7 | 96 | 6 | 25.7 s |
| `protenix-free` | 326 | 225 | 12 | 6 | 101 | 5 | **52.9 s** |
| `protenix-cul1` | 307 | 215 | 22 | 16 | 92 | 9 | 46.0 s |
| `boltz2-target-seed0` | 317 | 224 | 13 | 7 | 93 | 9 | 44.5 s |
| `boltz2-target-zn-seed0` | 324 | **226** | **11** | **5** | 98 | 8 | 34.2 s |
| `boltz2-complex-seed0` | 312 | 220 | 17 | 11 | 92 | 13 | 30.6 s |
| `boltz2-complex-zn-seed0` | 315 | **227** | **10** | **4** | 88 | **7** | 32.2 s |

**Nothing is infinitesimally rigid at 79 residues** — every presentation, measured included, has
4–18 internal motions at the 8 Å alpha-carbon aperture. And the ordering is the opposite of what
"closer to measured is better" would predict: the **zinc-bearing predictions are the stiffest**
(10–11 dimensional motion space against the measured structures' 21–24). The predictions are
*tighter* than the measured structures, not closer to them. That is a real separation and this
receiver does not say which side is right.

---

## 17. Receiver 4 — the topological one, on the same complex

[definition] The receiver atlas already owned this and the 2026-09-19 run did not use it. The
aperture filtration of the same within-component complex, truncated at the **same** 8 Å squared
ceiling and at top grade 1, ordered by `OrderLaw::ByLowerBound`, reduced over **ℚ** by
`persistence` — which enforces its own grade-zero cross-check against the independent elder-rule
union–find before it returns. The two integer invariants are the contact graph's connected
components and its independent cycles.

| presentation | components | independent cycles |
|---|---|---|
| `measured-3DPL` | **2** | 234 |
| `measured-7Z8R` | **2** | 211 |
| `measured-2LGV` (20 models) | 1 or 2 | 239–271 |
| `designed` | 1 | 242 |
| `protenix-free` | 1 | 248 |
| `protenix-cul1` | **2** | 230 |
| `boltz2-target` (8 seeds) | 1 or 2 | 225–249 |
| `boltz2-target-zn` (8 seeds) | 1 or 2 | 223–246 |
| `boltz2-complex` (8 seeds) | 1 or 2 | 223–248 |
| `boltz2-complex-zn` (8 seeds) | 1 or 2 | 222–237 |

Both high-resolution measured structures' contact graphs are **disconnected** over the common range
while the design's and the free Protenix run's are connected; the predicted populations straddle
the two. `order_is_determinate` is **false** for every presentation, because the coordinate boxes
at the 7-place resident denominator are intervals and some entry values overlap without coinciding.
The reading above is therefore **one member of the order family**, taken at the declared lower-bound
law, and that is said rather than hidden.

---

## 18. Issue #9 — the held-out agreement count over a declared receiver family

### What could not be used, and why the owner says so

`Split::leave_one_out` is constructible only from `LineageClasses`, which is constructible only
from a `DesignFamily`, and `DesignFamily::declare` **refuses** a population of one object read many
times:

```
designs {left} and {right} are about the same object, so they are one object read twice;
the vertical index and the plural fibre own that population
```

A seed population **is** exactly that. So the lineage-class split is structurally unavailable here,
and the owner's own refusal names the object that owns the population instead: the plural fibre.
`evaluation_discipline`'s fibre-side owners — `disagreement_subsets` and `performance_on` — are the
ones that apply, and they are what ran.

### What was computed

For each population `P` and each member `h`, the development side is `P \ {h}`. An **addressed
family item** is a contact the development side classifies unanimously, or a rigidity invariant it
reads unanimously, or a topological invariant it reads unanimously. The count is how many of those
`h` agrees at. The contact subsets come from `disagreement_subsets` over the development fibre and
the score from `performance_on`; the rigidity and topological readings are the owners' own.

| population | held-out members | contact items addressed | contact agreeing | rigidity addressed | topological addressed | **family agreeing / addressed** |
|---|---|---|---|---|---|---|
| `boltz2-target` | 8 | 2,800 | 2,790 | 0.12 | 0.12 | **2,790 / 2,800 = 0.9965** |
| `boltz2-target-zn` | 8 | 2,869 | 2,865 | 0.00 | 0.00 | **2,865 / 2,869 = 0.9987** |
| `boltz2-complex` | 8 | 2,852 | 2,847 | 0.00 | 0.00 | **2,847 / 2,852 = 0.9983** |
| `boltz2-complex-zn` | 8 | 2,874 | 2,870 | 0.62 | 0.00 | **2,870 / 2,874 = 0.9987** |
| `measured-2LGV` | 20 | 2,753 | 2,750 | 0.05 | 0.00 | **2,750 / 2,753 = 0.9989** |

(Rigidity and topological columns are means over the held-out members, to two decimals.)

### What the family count means, and three things it cannot say

- It is **agreement between presentations of one object at three receivers, never realization.**
  Nothing here says any member is right.
- The development side's unanimity is a property of **this finite sample**. An item it splits on is
  excluded by construction, so the count is conditioned on that unanimity and the denominator is
  not fixed across populations.
- On the development-**separating** contact subset `performance_on` necessarily returns **zero
  agreeing**, because one class cannot equal two different ones. That zero appears in
  `measured_readings.json` for every held-out member and it is a **structural fact about the
  subset, not a result.** The informative number is the unanimous subset alone.
- It is taken at one aperture, one representative atom, one residue range and one chain separation,
  and says nothing outside them.

### The negative result, which is the more useful half

**The rigidity and topological receivers contribute almost nothing to a held-out count over a seed
population, because the development side is almost never unanimous.** Across 52 held-out members
and six rigidity invariants at two windows:

| window | invariant | development side unanimous |
|---|---|---|
| arm 21–40 | rank J, dim ker J, internal, clusters, constraints | **0 / 52** |
| arm 21–40 | self-stress | 3 / 52 |
| core 41–80 | rank J, dim ker J, internal, clusters | 1 / 52 |
| core 41–80 | constraints, self-stress | 0 / 52 |

So `contact ∧ rigidity ∧ topological` over a seed population is, on this material, **the contact
receiver and nothing else**. A receiver family whose members read integers that are not stable
across sampling cannot fold into a held-out count at that granularity. Either the invariants need a
coarser face (a rigidity *class*, not a rank), or the population needs to be over something other
than seeds. **That is the precise object #9 still owes**, and it is named rather than claimed.

---

## 19. Exterior float baseline against the measured structures

[definition] Exterior, float, load-bearing for nothing. Cα RMSD after Kabsch superposition over the
79 commonly resolved and identically typed residues, computed in the same `mod
exterior_float_baseline`, from the mmCIF decimal tokens' own retained strings.

| population | vs `3DPL`, whole (median [min, max]) | core 41–80 | arm 21–40 |
|---|---|---|---|
| `measured-7Z8R` | **2.34** | 1.66 | 1.78 |
| `measured-2LGV` (20 models) | 16.39 [8.71, 17.04] | 2.73 | 4.26 |
| `designed` | 8.92 | 1.43 | 8.19 |
| `protenix-free` | 8.80 | 0.85 | 8.05 |
| `protenix-cul1` | 6.65 | 0.98 | 2.65 |
| `boltz2-target` | 9.55 [5.84, 10.53] | 1.70 | 9.63 |
| **`boltz2-target-zn`** | **4.93** [3.19, 8.17] | 1.73 | **2.24** |
| `boltz2-complex` | 7.15 [3.10, 9.10] | 1.42 | 11.66 |
| **`boltz2-complex-zn`** | 6.84 [**1.94**, 9.06] | 1.32 | 9.28 |

The best single member of the whole population, `boltz2-complex-zn-seed1` at **1.94 Å**, is closer
to the 2.6 Å crystal structure than the 2.7 Å cryo-EM structure of the same protein is (2.34 Å).
The **core is 0.85–2.73 Å for everything including the NMR ensemble**; every difference between
presentations lives in the arm, exactly as §8 and issue #44 said.

The NMR ensemble's own internal spread is the same shape: over its 20 models against model 1, the
median Cα RMSD is **0.67 Å on the core** and **6.10 Å on the arm** (12.65 Å over the whole common
range, up to 15.61 Å). The arm is not undecided because the predictors are bad at it; it is
undecided because RBX1's N-terminal arm does not have one conformation when it is not holding a
cullin — the measurement says so about itself.

---

## 20. Cost

Wall clock from `std::time::Instant`, release build, one core, on the integrated tree.

| step | cost |
|---|---|
| RCSB sequence search, metadata for 118 entries, three mmCIF downloads | < 10 s total, 5.3 MB |
| staging 22 measured model files out of three depositions | 0.43 s (python) |
| Boltz-2 prediction, 108 tokens, MSA reused, no zinc | 23–36 s |
| Boltz-2 prediction, 111 tokens (108 + 3 ions), MSA reused | 22–46 s, **median 27 s against 26 s without — the zinc is free** |
| Boltz-2 prediction, 204 / 207 tokens | 24–43 s, median 33 s (no zinc) and 31 s (zinc) |
| **the whole seed population** | **916 s = 15.3 min** of driver wall clock over 31 runs, plus the one probe invocation, no retries |
| intake of one presentation, indexed into the M5 residue numbering | 1.0 – 8.2 ms |
| one within-component family: 2,926 exact classifications, enacted and audited | 50 – 82 ms |
| the topological receiver on the same complex: filtration, order, ℚ persistence, grade-0 cross-check | 37 – 57 ms |
| the whole 57-member fibre: partition, roles, **all 1,596 ordered separators** | **10 ms** |
| `rigidity_reading`, 48 coordinates (arm 21–40), 57 presentations | 0.008 – 0.159 s |
| `rigidity_reading`, 111 coordinates (core 41–80), 57 presentations | 1.57 – 3.94 s |
| **`rigidity_reading`, 237 coordinates (whole common range)** | **14.3 – 52.9 s** |
| `rigid_clusters`, 48 / 111 / 237 coordinates | 0.011 – 0.060 / 0.026 – 0.050 / 0.1 – 0.3 s |
| the whole 2026-09-20 reading, 57 presentations | **494.4 s** |

### What would not scale, and why

- **The contact receiver still is not the bottleneck.** 2,926 exact classifications cost 50 ms and
  the complete 57-member fibre with all 1,596 ordered separators costs **10 ms**. Doubling the
  residue range quadruples the pairs and it would still be milliseconds.
- **The topological receiver at top grade 1 is cheap and at grade 2 would not be.** 79 vertices and
  ~325 edges reduce over ℚ in 40 ms. Grade 2 would found up to `C(79,3) = 79,079` triangles before
  the ceiling gate, and the reduction is cubic in the cell count: that is the wall, and it is why
  the reading above is components and cycles and not cavities.
- **`rigidity_reading` is the wall, and the growth is not in the shape.** 48 coordinates cost
  0.008–0.16 s, 111 cost 1.57–3.94 s, and 237 cost **14.3–52.9 s**. Between the last two rows that
  is ~2× the coordinates for ~8× the time, which is coefficient growth in the exact RREF on top of
  the `O(n²m)` elimination count. The spread *within* one size — 14.3 s against 52.9 s for the same
  237 × ~320 shape — is the presentation's geometry driving the bit length of the intermediate
  rationals. The full 204-monomer complex is 612 coordinates: extrapolating the observed growth
  puts it in **hours**, and §9's estimate stands.
- **The seed population multiplies every exact receiver by the population size.** 57 presentations
  × 2 windows, plus 10 at the whole range, is 124 exact RREFs; that is most of the 494 s. A 32-seed
  population at the whole range would be an hour of CPU for one reading. The contact receiver
  would not notice.
- **The measured side does not scale by being measured.** Reading 20 NMR models costs 20× one
  model at every receiver, and the ensemble is the honest object.

---

## 21. What agreed, what separated, what failed — 2026-09-20

### Agreed

- The 2026-09-20 `complex` seed-0 run reproduces the 2026-09-19 seed-0 run's 204 alpha-carbon
  coordinates **exactly**, from a different input format.
- On the **RING core** every presentation agrees to 0.85–2.73 Å exterior RMSD, including three
  measured structures by three methods, a design, two predictors and 32 seeds.
- Boltz-2 places three unconstrained `ZN` ions on RBX1's RING **C3HC4 cross-brace** (His80, Cys83,
  Cys45, Cys42 at 2.16–2.49 Å) without being told where they go.
- The zinc-bearing predictions and the measured structures carry the **same ligand complement**, so
  the `cofactors` axis drops out of the declared passage between them.

### Separated

| what separates | which receiver | which cannot |
|---|---|---|
| the NMR construct from the M5 object | the object check: `ObjectDiffersInTheFibre`, by four substitutions | — it is a refusal, not a reading |
| two measured structures of RBX1 | contact family, 40 of 2,926; exterior RMSD 2.34 Å | core rigidity: both read rank 103–105 |
| the **design** from measured RBX1 | contact family, 65 and 61 — the largest gap of any presentation | core exterior RMSD, 1.43 Å |
| zinc from no zinc | seed spread (47 → 21), flipping contacts (136 → 61), arm RMSD (9.63 → 2.24 Å), confidence (0.620 → 0.829) | the core, at every receiver |
| the measured structures from the predictions | topology: both high-resolution measured contact graphs are **disconnected**, most predictions' are connected; whole-range rigidity, 21–24 dimensional motion space against 10–17 | the core contact family and the core RMSD |
| the arm | everything | — |

### Failed or refused

| what | where |
|---|---|
| the 96 × 108 cross receiver on a measured structure | refused by object check: a measured RBX1 carries no binder. The **within-component** family is the lawful receiver and is what was declared |
| the whole 57-member fibre at the 83-residue scope | `ObjectDiffersInTheFibre`, naming the NMR construct's occurrence. Lifted by dropping the four mutated residues, not by editing anything |
| `Split::leave_one_out` over a seed population | structurally unavailable: `DesignFamily::declare` refuses one object read many times, and its refusal names `PluralFibre` as the owner instead |
| the rigidity and topological receivers inside the held-out family count | the development side is unanimous on 0–3 of 52 held-out members per invariant, so the family fold is the contact receiver and nothing else |
| `physical_intake::mmcif` on a deposited or zinc-bearing mmCIF | it requires an integer `_atom_site.label_seq_id`, which a `HETATM` row does not carry. Every such file is staged first and the staging is recorded |
| `order_is_determinate` at the topological receiver | **false** for all 57: the resident coordinate boxes are intervals and entry values overlap. The reading is one member of the order family, at the declared lower-bound law |
| `holonic_chain::AnalyticScope` gained a `StructurallyPlaced` variant mid-run | wave 9 worker L's change. This example records the variant by `Debug` rather than repairing an owner it does not own; the 2026-09-19 chain reading is otherwise unchanged |

---

## 22. What is **not** decided — 2026-09-20

- **Still nothing says any prediction is right.** Three measured structures that disagree with each
  other by 40 contacts and 2.34 Å do not constitute a ground truth; they constitute three more
  members of the fibre, at three more environments.
- **The measured structures are all partial.** 21 to 29 of the M5 target's 108 residues are
  unresolved in at least one of them, including the whole N-terminal arm 1–18, which is precisely
  the region every receiver says the presentations disagree about. **The question the arm poses has
  not been answered by measurement; it has been declared out of scope by measurement.**
- **The NMR entry is a mutant.** 2LGV's four substitutions exist so that RBX1 can be studied without
  a cullin. Reading it against the wild-type object needed a 79-residue restriction, and whether
  the substitutions change the fold near residues 27–33 is not decided here.
- **One predictor, one checkpoint.** 32 runs of Boltz-2 2.2.1 are 32 samples of one model. The two
  Protenix runs remain irreproducible on this workstation.
- **Whether the zinc effect is RBX1-specific** is not decided. One zinc protein, one predictor, one
  aperture.
- **The chain reading has not been taken on the measured structure.** It is the primary's join step
  and the command is in the worker return.
- **Nothing was read at the 204-monomer extent**, for the cost reasons in §20.

---

## 23. Reproducing the 2026-09-20 section

```sh
# 1. the measured structures (rcsb.org only)
curl -sS -X POST https://search.rcsb.org/rcsbsearch/v2/query -H 'Content-Type: application/json' \
     -d @query.json -o .local/m5-prediction-2026-09-20/measured/seqsearch-verbose.json
for id in 2LGV 3DPL 7Z8R; do
  curl -sS -o ".local/m5-prediction-2026-09-20/measured/$id.cif" \
       "https://files.rcsb.org/download/$id.cif"
done
python3 research/experiments/m5_predicted_vs_reference/stage_measured.py \
    --out .local/m5-prediction-2026-09-20/measured/staging.json

# 2. the seed population (GPU, one process at a time, ~16 min)
bash .local/m5-prediction-2026-09-20/run_all.sh

# 3. the manifest, which also stages the zinc predictions' protein rows
python3 research/experiments/m5_predicted_vs_reference/assemble_manifest.py

# 4. the receivers (exact, over Q)
PATH=/opt/cuda/bin:$PATH cargo run --release -p holonic-engine \
    --example m5_predicted_vs_reference -- \
    --manifest .local/m5-prediction-2026-09-20/manifest.json \
    --out-measured research/experiments/m5_predicted_vs_reference/measured_readings.json \
    --whole-range-rigidity --skip-2026-09-19

# 5. the exterior self-report
.local/venv-protein/bin/python \
    research/experiments/m5_predicted_vs_reference/predictor_confidence_population.py \
    .local/m5-prediction-2026-09-20/out \
    > research/experiments/m5_predicted_vs_reference/predictor_confidence_population.json
```

Files added here:

| file | what it is |
|---|---|
| `measured_readings.json` | the Rust example's 2026-09-20 output: every exact reading, over ℚ |
| `measured_staging.json` | which residues each measured entry resolves, which monomers differ, what the staging filter did |
| `predictor_runs_2026-09-20.json` | the 32 runs, the download URLs and byte counts, and the exterior ion-coordination report |
| `predictor_confidence_population.json` | Boltz-2's own confidence over the population, exterior float |
| `stage_measured.py` | the measured staging, which computes no geometry |
| `assemble_manifest.py` | the presentation manifest and the zinc predictions' protein-row staging |
| `predictor_confidence_population.py` | the 2026-09-19 confidence reader, widened to the population |

Bulk predictor outputs, the downloaded depositions, the staged model files and the logs live
untracked under `.local/m5-prediction-2026-09-20/`.

---

## 24. The join: the theorem-backed chain reading on measured, designed and predicted structures

[measured] `--chain-join`, tree `d3ef0a75` plus the wave 9 library changes, 929 s for 30 readings,
0 refusals. Windows are consecutive and resolved in every presentation: arm 21–32, core 41–52
(36 coordinates each) and core 41–63 (69 coordinates). Short list: the three measured RBX1
structures (first NMR model), the design, both Protenix runs, seed 0 of each Boltz-2 condition.
Machine-readable rows: `chain_join.json`.

In **all 30 readings** the rank is determined by the nullity theorem with no resolvent inverse and
equals the neck's section; the transport and rate-form residuals are exactly zero; every gap
balances; the relative degree is 1; and the analytic face is **decided by structure**
(`StructurallyPlaced`, a real spectrum), where every earlier reading returned
`NotDecidedWithinBound`. One reading costs 1–18 s at 36 coordinates and 39–99 s at 69.

| window | measured 2LGV / 3DPL / 7Z8R | designed | Protenix free / CUL1 | Boltz-2 target / +Zn / complex / +Zn |
|---|---|---|---|---|
| arm 21–32: cut, section | 4, 3 / 7, 3 / 7, 3 | 4, **9** | 4, **9** / 7, 3 | 4, 4 / 4, 4 / 4, 4 / 4, 8 |
| core 41–52: cut, section | 6, 10 / 6, 9 / 7, 7 | 7, 8 | 6, 9 / 6, 8 | 6, 8 (all four) |
| core 41–63: cut, section | 19, 6 / 19, 6 / 19, 5 | **11**, 8 | 18, 7 / 18, 7 | 19, 5 / 19, 5 / 19, 6 / 19, 6 |

[measured; interpretation] On the longer core window **all three measured structures and all four
Boltz-2 presentations place the minimal cross-domain section at the same cut (19) with section
5–6**; the Protenix runs sit one residue away; **the design places it at cut 11 with section 8**.
On the arm, the crystal, the cryo-EM map and the CUL1-bound Protenix run agree (cut 7, section 3)
while the design and the free Protenix run carry a section three times wider. This is the contact
receiver's finding of §14 — the design is the outlier, the predictions track the measurements —
read independently through the chain. Scope: one chain, three windows, first models and seed 0;
a minimal section is a packing or hinge feature only once the rigid-cluster verdict of §9 is
applied to it, which this join did not do.
