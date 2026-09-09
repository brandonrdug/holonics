# AC1: the material operator retains its accumulated source geometry

[definition] This implements the accumulated-normal construction derived in the
[retention investigation](2026-09-09_AC1_LOCAL_CONTACT_IMPROVEMENT_COEXISTS_WITH_MATERIAL_FORGETTING.md),
starting from `5167e325`. `OperativeNormal` is a declared material realization over the existing
operative outgoing source. It preserves the paired field, actual source contacts, joint target,
complex-current return and source-preserving actuation. Older models retain their original law.

## Native state and returned comparison

[established-bounded; source-inspected] `field_normal_material.cuh` accumulates
`H=I+sum xx†`, `B=sum yx†`, and `C=sum ||y||²` for actual observed source/target relations.
It also accumulates the source-normal, cross-source and target-energy family bounds. Every
moment has an exact signed 544-bit integer numerator over the common dyadic scale squared.
The initial identity is the previously declared unit coefficient metric. A self-actuation
adds no observation; its ordinary current still advances through the field.

[established-bounded; source-inspected] The native matrix is obtained through the existing LDL
and solve owners. A real-block proposal rounds H to the declared grain and adds `2m` grain units
to its diagonal, where m is the actual complex source dimension. This is a derived rounding
majorant: each of the `2m` real-block entries in a row differs by less than one grain unit, so
the shift makes the proposal positive. It changes no exact accumulated moment. The complete
normal residual is then evaluated against exact H and B, rather than against that proposal.

[proved-derived] For the numerical matrix Mhat, source-family bounds EH and EB, and
`R=Mhat Hhat-Bhat`, the coefficient-family radius is bounded by
`||R||_F+||Mhat|| EH+EB`, since every admitted `H_true` is at least the initial identity.
The implementation uses integer L1 upper bounds and directed conversion to the declared grain.
Its exact statistics and numerical matrix retain the oriented residual as an executable
expression. This preserves source/target uncertainty without selecting a unique source.

[established-bounded; source-inspected] Exact zero increments leave their statistics unchanged;
the corresponding family-bound increments are still added. Target rows with an exactly zero
normal right-hand side have an exactly zero nominal solution. These arithmetic restrictions do
not filter the packet receiver or remove the original target domain. The complete material
state is copied into the successor only after all preparations and checks succeed.

## Historical operators and persistence

[established-bounded; source-inspected] `normal.rs` owns the state/report layout, initial
metric, exact moment decoder and validation. Normal reports retain their actual source current,
observed target and exact statistic increments. The former projection-gain decoder is not used
to describe that source-current suffix. Common material prediction and observation receivers
share only their actual common fields.

[established-bounded; source-inspected] An older producing operator is decoded by subtracting
the later observed statistic increments, then executing the same finite normal solve. The
material adjoint uses that operator and the original source's coefficient radius. Applied
material faces do not enter the increment journal. No host semantic replay or Lean executor is
introduced. All admitted hot normal work remains on the GPU.

[established-bounded; source-inspected] Cold persistence validation checks the signed integer
format, source-current incidence, exact accumulated statistics, matrix norm, complete normal
residual and family bound. The normal error radius is recomputed and may decrease; the old
projection learner's monotone error rule is retained for its original variants. Native normal
reports and checkpoints have their own explicit source tag and extents.

## Controls and first actual-data return

[established-bounded; implemented-exact; measured] The native normal control returns exact H,
B and C against independently accumulated source observations. The numerical matrix contains
the independent exact normal solution within its reported coefficient radius. A delayed return
uses the original nonzero material operator after later material and contact changes. Complete
subsequent development is identical after serialization and remount. The separate tensor-target
control retains complex phase, an independent target extent and its native adjoint.

[established-bounded; measured] The full field suite passes 115 cases before the subsequent
joint-target admission repair. The final two focused normal controls pass after that repair and
the exact-zero increment restriction. Together these cover 116 field cases at their stated
execution scopes. The first actual text attempt exposed the missed joint-target admission
branch before any occurrence committed. Its pending source/input checkpoint was preserved and
resumed successfully after the repair.

[established-bounded; measured] The resumed first-family study completes 75 occurrences and
74 observed contact returns. At the same five external receiving positions used in the prior
study, retention losses improve as follows. Each learner is evaluated on its own original
source family; matching the external observations does not identify their latent currents.

| Receiving occurrence | Previous material law at 75 occurrences | Accumulated normal law at 75 occurrences |
|---|---:|---:|
| 2 | 0.706228 | 0.142292 |
| 3 | 0.711534 | 0.218489 |
| 4 | 0.651285 | 0.341677 |
| 5 | 0.722155 | 0.278853 |
| 7 | 0.556047 | 0.310050 |

[established-bounded; measured] These are rounded displays of half squared complex-current
discrepancy. Every new upper interval bound is below the corresponding old lower bound. All five
inspected early finite contact returns also still improve their declared diagnostic response.
This establishes a bounded retention improvement, not perfect recall or useful language.

[established-bounded; implemented-exact; measured] A fresh run without diagnostics returns
the identical complete body and 20,526,964-byte checkpoint. Development performs zero numerical
section readouts and takes 21.889 seconds, versus 7.486 seconds for the previous law's matched
75-occurrence run. Whole-process time is 23.498 seconds with peak RSS 244,056 KiB. The diagnostic
run takes 77.497 seconds including its exact rational observations. The new law has a runtime
and standing cost; its improved retention does not erase that cost.

[established-bounded; measured] The additional seven families complete in 794.780 seconds,
reaching 1,930 occurrences and 1,929 observed contact returns. The pre-prompt checkpoint is
450,770,927 bytes; the exterior history is 309,415,515 bytes. All 11,130 developmental section
readouts belong to history placement, with zero outside it. Native residency after development
is 292,000,608 bytes and peak residency is 540,320,388 bytes. Whole-process time including prompt
and diagnostics is 885.022 seconds; peak RSS is 1,021,840 KiB.

[established-bounded; measured] Its first-request response is valid UTF-8 but unusable:
`’m the the the ...` through the 128-byte work limit. Two fresh-process resumes from the saved
1,930-occurrence model reproduce this text. The original prompt protocol takes 48.175 seconds
for prompt/generation. Using the same configured contact response during prompt intake as during
development adds 61 contact deposits and takes 61.780 seconds; the body changes but the text
does not. Self-actuation remains distinct from observation. The new prompt-path control passes.

[established-bounded; measured] The two focused native normal controls also pass after adding
the signed residual decoder assertion (1.34 seconds, CUDA already built). The alpha SDK returns
26 passing controls, and the driver returns three passing controls with its separately marked
partial-actual-part case excluded. The portable [receipt](2026-09-09_normal_material/return.json)
retains check scopes and process metadata. No unchanged full formal campaign was rerun.

[definition] The [parallel mathematical review](2026-09-09_MATHEMATICAL_REVIEW_NORMAL_GEOMETRY_AND_CLOSED_RETURNS.md)
now supplies residual-aware rank-one reuse and objective separation. The
[feedback review](2026-09-09_AC_THE_REPEATED_TEXT_FACE_IS_A_DRIVEN_OPEN_RETURN.md) demonstrates
that the repeated text is over changing currents and identifies the freshly driven codec
boundary. AC1 path/generator reuse and AC2 situated feedback/useful responses remain unfinished;
the wider AC0–AC5 goal is still active.
