# SKE0: the excitation-founded quotient returned signature identity, intervention cones, and the faithful productive lane

**Date:** 2026-09-03  
**Truth status:** `proved-derived`  
**Evidence:** `formal-checked`  
**Campaign:** SKE0 under
[`THE_SOULKILLER_EXCITES_THE_RESIDENT_REALIZATION_AND_RETURNS_THE_RECEIVER_FAMILY_QUOTIENT_AS_CONE_RESTRICTED_ECOLOGIES.md`](../../blueprint/THE_SOULKILLER_EXCITES_THE_RESIDENT_REALIZATION_AND_RETURNS_THE_RECEIVER_FAMILY_QUOTIENT_AS_CONE_RESTRICTED_ECOLOGIES.md).

## Return

[proved-derived; formal-checked] `Computation/HolonicExcitationFoundedQuotient.lean` (396 lines)
is imported by both the live umbrella and the full umbrella. Over one `FiniteLocalCurrentEcology`
it returns:

- `signature`: the receiver face of a presented state after one ordered history at one rest, with
  `signature_step`: driving the state by a generator is reading the signature at the extended
  history.
- `allHistoryQuotient`: the quotient of presented states by equal signature over every receiver
  and every ordered history, constructed as a `CompleteReceiverHistoryQuotient` whose transport is
  `Quotient.map` of the ecology's step. Its theorems are inherited, not re-proved:
  `nativeEq_iff_signatureEq` and `nativeNe_returnsSeparatingHistory`.
- `DeclaredFamily`: the occurrences an application presents, the receivers reading them, and the
  histories they are driven through; `Exposure`, `Identified`, `familySetoid`, `Class`, and
  `familyCompression`, a `Compression` exact for every declared exposure;
  `identified_faces_eq`, `separatingExposure_reopens`, and `identified_of_nativeEq` (native
  equality identifies whatever every declared exposure identifies).
- `withdraw`, `IsCone` (withdrawal disjoint from the cone leaves the face unchanged),
  `isCone_univ`, `LoadBearing`, and `loadBearing_mem_of_isCone`: every cone contains every
  load-bearing site.
- `DeclaredFamily.extent` (the union of the family's cones), `DeclaredFamily.insufficiency` (its
  complement), and `withdraw_insufficiency_unchanged`: withdrawing any population inside the
  insufficiency leaves every declared face of every occurrence unchanged. This is "you can only
  lift what you infer" as a theorem.
- `ExcitationFoundedReturn`: a `DismantlingReturn` whose productive lane is a
  `FaithfulLocalSectionLift`, with `productive_everyGeneratorWordExact` and the inherited
  `admitted_replaceColdWitness`. A manifestation has no lane of this type.
- `Control`: a two-site ecology and one presented state with equal magnitude at both sites; under
  history `[false]` site 0 is load-bearing and site 1 is inert, under `[true]` the reverse;
  `{0}` is a cone under the first and `{1}` under the second. Equal magnitudes, different cones:
  no magnitude ranking determines the cone.

[proved-derived; formal-checked] The focused check passed; the live umbrella built 3,775 jobs
under the formal gate. Every audited declaration depends only on `propext`, `Classical.choice`,
and `Quot.sound`; no `sorry`, `admit`, or new axiom.

## Grade

[proved-derived] **SKE0 PASSED.** The pass conditions of the blueprint are discharged: identified
occurrences have equal faces on every declared exposure; a separating exposure reopens; withdrawal
outside a cone leaves every declared face unchanged; the control exhibits equal magnitude with
different cones; extent and insufficiency are stated and the insufficiency law is proved; the
productive-lane type is defined. What SKE0 does not do: it does not state which cone is *the*
cone of an occurrence (any sound cone is admitted; minimality is the intervention obligation of
SKE2), and it does not bridge a declared finite family's quotient to a generator-equivariant
transport, which requires the family's histories to be closed under extension and is left to the
all-history quotient.
