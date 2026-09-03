# SKE3: the signature quotient identified two variants under the empty history, and a declared history reopened them

**Date:** 2026-09-03  
**Truth status:** `established-bounded`  
**Evidence:** `implemented-exact`, `source-inspected`, `measured`  
**Campaign:** SKE3 under
[`THE_SOULKILLER_EXCITES_THE_RESIDENT_REALIZATION_AND_RETURNS_THE_RECEIVER_FAMILY_QUOTIENT_AS_CONE_RESTRICTED_ECOLOGIES.md`](../../blueprint/THE_SOULKILLER_EXCITES_THE_RESIDENT_REALIZATION_AND_RETURNS_THE_RECEIVER_FAMILY_QUOTIENT_AS_CONE_RESTRICTED_ECOLOGIES.md).  
**Receipts:** [`2026-09-03_SKE3_receipts/`](2026-09-03_SKE3_receipts/): one exact receipt per
exposure (face, exact digest, cone per population as a site bitmask) and the quotient.

## The instrument

[implemented-exact; source-inspected] A declared family is occurrences, receivers, and ordered
histories. On the resident operator the receiver is the selected face at the terminal position
and a history is a fixed generator word the application appends after the model's turn marker;
the occurrence driven through the history is one cycle on the occurrence's addresses followed by
the word, exactly `inferWord` over the presented state. The signature of an occurrence is its
face at every declared exposure; two occurrences are one class when their signatures agree
(`DeclaredFamily.Identified`), and one separating exposure reopens a class
(`separatingExposure_reopens`). Every exposure's cone is founded by the SKE2 joint intervention; a
class's cone is the union of its members' cones over every exposure; the extent is the union of
every cone (`DeclaredFamily.extent`) and the insufficiency its complement
(`DeclaredFamily.insufficiency`), reported as site populations. The owner is
`operative_identification.rs`, host arithmetic over faces and bitmasks the card returned, with
tests for the round trip and union of bitmasks, the identification and reopening law, and the
refusal of a family missing an exposure.

## The declared family and exposures

[definition] The five variants of one algebraic problem from SKE2, each through the
application's turn markers, exposed to three declared histories: the empty word, `The second
operand is `, and `The sum is `. The words ask the operator for what the occurrence carries or
for its own answer; no answer is named, and the faces are the operator's own.

## The deed

[established-bounded; implemented-exact; measured] `applications/athena-alpha/examples/signature_quotient_ske3.rs`,
one bounded process per exposure (54 to 56 s) and one host process for the quotient. Every
exposure's null withdrawal reproduced its face and exact row, and every cone was closed by the
complement withdrawn (unchanged) and the cone withdrawn (changed) over 21 or 22 monotone probes:

| occurrence | empty history | `The second operand is ` | `The sum is ` |
|---|---|---|---|
| `7 + 5 =` | `7` (cone 29,588) | `5` (162,238) | `1` (596,037) |
| `9 + 3 =` | `9` (71,755) | `3` (135,198) | `1` (133,174) |
| `7 + 6 =` | `7` (1,310,213) | `6` (173,487) | `1` (615,036) |
| `3 + 4 =` | `3` (345,940) | `4` (174,961) | `7` (640,445) |
| `8 + 8 =` | `8` (181,063) | `8` (302,355) | `1` (530,780) |

[established-bounded; measured] The quotient: under the empty history alone the family has four
classes, `7 + 5 =` and `7 + 6 =` being one (equal faces `7`); the declared history `The second
operand is ` separates them (`5` against `6`) and reopens that class into two; under all three
histories every occurrence is its own class, five in all. The class cones are the unions over
their exposures: 633,963, 252,459, 1,313,223, 732,894, and 652,654 sites. The extent of the
family's lift is 1,316,260 of the 1,595,392 sites and the insufficiency 279,132 sites, returned
per population as bitmasks in the quotient receipt; every undeclared receiver and history is
outside the family by construction.

[measured] The faces under `The sum is ` are the first digits of the operator's own sums
(`12`, `12`, `13`, `7`, `16`): the same face `1` for four occurrences, whose cones differ by up to
a factor of four. The face is the signature's coordinate; the cone is what carried it.

## Verification

[process-audit; measured] Host tests of the identification owner pass; the fifteen exposures and
the quotient were produced twice on the same binary and reproduced exactly; the engine library and
workspace type-check are recorded with SKE2's, no card owner having changed since.

## Grade

[established-bounded] **SKE3 PASSED.** Two occurrences with equal signatures are one class; a
declared separating history reopens that class into two; every class and its cone are returned
with their occurrence populations retained; the extent and insufficiency are returned as
populations.

[counterexample; source-inspected] What this does not claim: the declared histories are three
fixed words, and identification is relative to them (the all-history quotient of SKE0 is not
computed); the classes are singletons under the full exposure family, so the condensation of
SKE4 acts on five one-occurrence classes and one shared extent; the cones are the joint-withdrawal
cones of SKE2 with the same bounded soundness; no capability claim follows from the faces.
