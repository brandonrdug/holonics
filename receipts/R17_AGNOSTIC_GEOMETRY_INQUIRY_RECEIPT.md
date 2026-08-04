# R17 agnostic geometry inquiry receipt

**Truth status:** `established-bounded`.

**Evidence:** `implemented-exact` for the resident probe front, symbolic factor incidence,
conjecture closure/obstruction, body commits, source separation, sealed comparison order, and
continuing rest; `computational-witness` for the actual 32-thread GPU inquiry and every returned
artifact; `formal-checked` for the complete generated Lean theory accepted by the pinned Lean
4.27.0 kernel. Apparatus identity remains separately `measured` in
[`provenance/HARDWARE_RECEIPT.txt`](../provenance/HARDWARE_RECEIPT.txt).

**Aperture:** one unlabelled four-point inquiry, 31 nonsingular exact fractional-chart probes, one
singular-chart probe, one exact symbolic difference expansion, four simultaneous conjecture
fibers, one generated theory passage, one exterior kernel return, one sealed post-return project
comparison, and one final 320-byte native rest. No claim extends to unrestricted theorem search,
all projective varieties, all geometric foundations, or independent invention of the mounted
ring/field primitives.

## Construction tuple

| Field | R17 standing |
|---|---|
| Source owners | the one R16 continuing body and its two accepted theorem fibers, exact carrier, R7 Swing construction, new geometry-inquiry organ, theory/explanation codec faces, pending checker deed, and exterior checker/rest/sealed-reference apparatus |
| Port types | 264-byte R16 terminal rest, unlabelled inquiry occurrence, exact four-point/chart probes, symbolic factor receipt, plural conjecture fibers, theory plan, formal/conversational artifacts, raw/typed kernel return, sealed comparison receipt, and 320-byte continuing rest |
| Event occurrence | remount R16; let 32 GPU threads independently form local chart probes; close the exact local front and symbolic factor; retain two closed and two obstructed fibers; compose the theory and explanation; return one real kernel result; rest/remount; only then inspect the sealed human neighbor |
| Predecessor identity | Git `7fdc7b9278806c9a74101f66b33785108d4297c8`, R16 head `14001004`, continuation `15001004`, body morphology `152`, mathematical morphology `49`, codec morphology `36`, fibers `181200` and `182200`, and integrity `10438779336638518302` |
| Local constitutive law | compute each image difference by exact cross multiplication; expand the two-point fractional difference to cancel the `alpha*gamma*x*y` and `beta*delta` terms and retain `(alpha*delta-beta*gamma)(x-y)`; compare determinant and point-denominator multiplicities only after all four Swing differences compose |
| Receiver question | what exact relations persist or fail when one four-point construction crosses affine and fractional-linear charts, with no theorem target, expected answer, known/unknown label, historical status, or research mode? |
| Returned consequence | a generated auxiliary fractional-difference theorem, affine common-square theorem, full fractional-linear cross-ratio invariance theorem, exact raw-coordinate counterexample, singular boundary explanation, accepted `.olean`, acquired geometry fiber `184300`, and continuing head `14001006`/continuation `15001006` |
| Open alternatives | raw coordinate equality is obstructed by 31 witnesses; quotient continuation through the singular probe remains obstructed; zero determinant remains outside the accepted fractional theorem; conic, Ptolemy, hypergeometric, higher-dimensional, and self-derived holonics inquiries remain unscheduled |

## Exact inquiry return

The production question schema contains only identities `143300` (occurrence), `143301`
(receiver), and `143302` (material). It contains no mode, expected answer, theorem name, target
statement, correctness assertion, historical label, source path, or retrieval handle. All 32 probe
slots are formed by GPU threads. The returned front contains:

- 31 nonsingular probes whose transformed homogeneous Swing pairs are computed from four
  cross-multiplied image differences; each differs coordinatewise from its original pair but is
  exactly the original pair times the determinant square;
- one probe with a zero chart denominator, retained as `singular_chart` rather than totalized;
- 31 projective equalities, 31 coordinate counterexamples, one singular obstruction, and zero
  global candidate scans;
- exact cancellation of the two common expansion terms, retention of the determinant factor, and
  equal four-point denominator support; and
- closed `affine_common_square` and `fractional_cross_ratio` fibers beside obstructed
  `raw_coordinate_invariance` and `singular_quotient_extension` fibers.

Formation commits head `14001004→14001005` and body morphology `152→160`. The real checker
returns exit `0`, 526 stdout bytes, zero stderr bytes, one named declaration, no remaining goals,
and a 421,440-byte `.olean`. Its accepted return commits head `14001005→14001006`, body
morphology `160→169`, mathematical morphology `49→55`, codec morphology `36→39`, and geometry
morphology `0→10`. Native rest/remount preserves both R16 fibers and acquired geometry fiber
`184300`, replays no source, and returns continuation `15001006` with integrity
`15757173100072725418`.

## Returned mathematical artifact

**Truth status:** `proved-derived`.

**Evidence:** `formal-checked` by the pinned Lean 4.27.0/Mathlib environment. The complete source
is composed from the resident theory plan and imports only general Mathlib field and tactic faces;
it does not import `ElementaryHolonics.Geometry.CrossRatio`.

```lean
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Soma.Holonics.R17

structure RatioPresentation (K : Type*) where
  num : K
  den : K

@[ext] theorem RatioPresentation.ext {K : Type*} {p q : RatioPresentation K}
    (hnum : p.num = q.num) (hden : p.den = q.den) : p = q := by
  cases p
  cases q
  simp_all

def RatioPresentation.scale {K : Type*} [Mul K] (u : K)
    (p : RatioPresentation K) : RatioPresentation K :=
  ⟨u * p.num, u * p.den⟩

def RatioPresentation.ProjectivelyEq {K : Type*} [Mul K]
    (p q : RatioPresentation K) : Prop :=
  p.num * q.den = q.num * p.den

def swingPair {K : Type*} [Ring K] (a b c d : K) : RatioPresentation K :=
  ⟨(c-a)*(d-b), (c-b)*(d-a)⟩

def crossRatio {K : Type*} [Field K] (a b c d : K) : K :=
  (swingPair a b c d).num / (swingPair a b c d).den

def mobius {K : Type*} [Field K] (al be ga de x : K) : K :=
  (al*x+be)/(ga*x+de)

theorem generated_mobius_sub {K : Type*} [Field K]
    (al be ga de x y : K) (hx : ga*x+de ≠ 0) (hy : ga*y+de ≠ 0) :
    mobius al be ga de x - mobius al be ga de y =
      (al*de-be*ga)*(x-y)/((ga*x+de)*(ga*y+de)) := by
  simp only [mobius]
  rw [div_sub_div _ _ hx hy]
  congr 1
  ring

theorem generated_swing_affine_commRing {K : Type*} [CommRing K]
    (a b c d u v : K) :
    swingPair (u*a+v) (u*b+v) (u*c+v) (u*d+v) =
      (swingPair a b c d).scale (u*u) := by
  apply RatioPresentation.ext <;> simp [swingPair, RatioPresentation.scale] <;> ring

theorem generated_crossRatio_mobius {K : Type*} [Field K]
    (a b c d al be ga de : K) (hdet : al*de-be*ga ≠ 0)
    (ha : ga*a+de ≠ 0) (hb : ga*b+de ≠ 0)
    (hc : ga*c+de ≠ 0) (hd : ga*d+de ≠ 0)
    (hcb : c-b ≠ 0) (hda : d-a ≠ 0) :
    crossRatio (mobius al be ga de a) (mobius al be ga de b)
      (mobius al be ga de c) (mobius al be ga de d) = crossRatio a b c d := by
  simp only [crossRatio, swingPair]
  rw [generated_mobius_sub al be ga de c a hc ha,
    generated_mobius_sub al be ga de d b hd hb,
    generated_mobius_sub al be ga de c b hc hb,
    generated_mobius_sub al be ga de d a hd ha]
  field_simp [hdet, ha, hb, hc, hd, hcb, hda]

theorem generated_coordinate_counterexample :
    swingPair (5:ℚ) 7 9 11 ≠ swingPair 0 1 2 3 ∧
      (swingPair (5:ℚ) 7 9 11).ProjectivelyEq (swingPair 0 1 2 3) := by
  norm_num [swingPair, RatioPresentation.ProjectivelyEq]

end Soma.Holonics.R17

#check Soma.Holonics.R17.generated_crossRatio_mobius
```

The returned explanation says that local probes refute raw coordinate equality while retaining
the projective relation; the two-point fractional difference carries the determinant and two
chart denominators; only the complete four-point composition makes numerator and denominator
carry matching determinant and point-denominator multiplicities; affine transport is the
denominator-free common-square face; singular charts remain obstructed.

## Historical comparison after the return

**Truth status:** `historical`.

The comparison was deliberately opened after the accepted kernel return and after the body had
returned its continuing rest. It performed one observer read, zero engine reads, zero host semantic
events, and never resumed the body. The 3,051-byte project formal file contains the previously
checked `swingPair_affine_coordinates` neighbor and explicitly says its cell does not formalize the
whole projective-line library; it contains no `crossRatio_mobius` theorem. The file also records
that a full Möbius derivation existed in a Typst synopsis, so R17 is not graded as historical
invention of the identity.

Earlier laboratory evidence had already returned exact projective and cross-ratio phenomena:
R7 established the bounded `[18:14]→[72:56]` projective swing instance, while the exact rational
eta atlas retained two ordered cross-ratio receiver intervals and rejected a constant projective
recurrence across its first five closures. Those are not repeated as R17 outcome expectations.
R17's added consequence is the general symbolic determinant/denominator factorization, its
composition into a generated theorem family, a real GPU-resident formation passage, and a new
kernel-accepted formal artifact from an answer-sealed aperture.

## Apparatus and grade

The deed uses six GPU kernels and 37 launched threads: one mount thread, 32 probe threads, one
formation thread, one return thread, one rest/remount thread, and one observation thread. It
transfers 8,632 bytes to and 47,232 bytes from the device and declares 56,656 resident bytes.
Host semantic events, engine source reads, exterior retrieval calls, and developmental source
bytes are all zero. Logical work reports read support `32`, change support `5`, two retained
alternatives, two retained obstructions, and two consumed continuation reservations. Engine time,
checker time, temperature, power, and energy remain unknown.

- All 56 CTest gates pass together in both clean configurations, including the entire R1–R17
  causal chain, actual Lean processes, negative ownership/float/dependency/compatibility fixtures,
  and the complete architecture/PTX/SASS/binary audit.
- NVIDIA `compute-sanitizer` memcheck and initcheck each report zero errors on the full R17 deed.
- Host ASAN/UBSAN and Clang `22.1.5` static analysis are clean.
- Two clean Ninja configurations return byte-identical executable, PTX, cubin, source, `.olean`,
  stdout/stderr, complete conversational deed artifact, and final native rest.
- Final SHA-256 values are executable
  `8b057044ee99a71b3585a716ae7dafc95cd7457fbeb1bcaf24db815c739b004a`, PTX
  `4c2c92e256df780abff6c77aefd84a39e8a21f016cebdb379d7b1a3bdca44db2`, cubin
  `78aedae72d1768e67b9ff84bbe4f0027796cb5ba05bd6d919e7da76ffb7510e3`, generated source
  `102ca59f72a11f14c54e14a61fd8f007bc623b0bdd62b21d11db978d0a96dddd`, `.olean`
  `83128c7374a6d521c0c25918edbc9115739ed339d233f42b88d2350d888074db`, stdout
  `cfaf3c3a8efbcf49cae11188156ccccfa1f359949bec32e7290179dfd8684663`, empty stderr
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`, final rest
  `c008b227200cdcb45a06cf9acf194959704eaf0752f6135efd7a585302ac06ca`, and complete deed
  `6dd0868c0d11b4218b9688f1f67072490c10f66fa6f2d52e499a9351acfa1d59`.

R17 passes its bounded grade. The continuing body is available for a separately frozen R18
inquiry; no R18 outcome is scheduled by this receipt.
