# THE HOLONIC CALCULUS IN PLAIN LANGUAGE

**Status:** human-readable companion to the ratified presentation
`2026-07-13_THE_RELATIONAL_HOLONIC_CALCULUS.md`. This file is not a second authority, a new
derivation, or an implementation plan. It restates the presentation for a terminal reader and keeps
its grades and limits intact. `src/soma/FORMULA.md` remains the canon.

The purpose of the calculus is modest and exact: keep track of what kind of claim is being made
when a construction changes, is viewed, is transported, or is compressed. Ordinary mathematics
often lets one equality sign do several jobs. That shorthand is useful inside a declared quotient,
but it becomes destructive when a result about a visible face is carried back as a claim about the
construction which produced it.

The calculus prevents that collapse without invalidating ordinary mathematics.

---

## 1. The short version

A thing is not only the face another observer can read from it. It also has a lived construction:
the ordered events by which it arrived. Different constructions can present one face, and one
construction can present different faces to different receivers.

The minimal vocabulary has six verbs:

```text
relate       put two bodies in a declared frame
then         place one event after another on a worldline
transport    carry a construction or invariant between frames
observe      cast a receiver-relative face at a declared grain
compress     make a declared many-to-one cut
boundary     take the situated surface of a construction
```

These verbs support five different judgments. None may silently substitute for another:

```text
1. construction identity
2. explicit reversible gauge transport
3. observer/frame/grain face-equivalence
4. directed worldline
5. declared compression
```

The central discipline is therefore:

```text
same construction
    is not the same claim as
reversibly transportable
    is not the same claim as
same visible face here
    is not the same claim as
one happened after the other
    is not the same claim as
both were merged by a cut
```

---

## 2. The five judgments

### 2.1 Construction identity

```text
A = B
```

This is the strongest judgment. It says A and B name one construction, not merely one value,
shape, dimension, endpoint, or printed form.

It follows that one construction will cast the same face as itself under the same declared read.
The converse does not follow. Two routes can arrive at numeral `4`; two files can have the same
length; two quantities can have the same dimension; two bodies can have the same surface. None of
those facts alone establishes construction identity.

### 2.2 Explicit reversible gauge transport

```text
A --transport T at hand h--> B
B --transport inverse(T) at hand h--> A'
```

This says the declared transport has an algebraic reciprocal at the declared hand. It does not say
that A, B, and A' are one construction. It does not promise a path backward through a prior physical
state. A round trip is another traversal, and an oriented traversal can deposit winding:

```text
A -> B -> A'       with       A' != A
```

This is the current time-parity correction. Reversibility belongs to the local transport law, not
to a demand that a later state retain an itinerary, founder list, or unique recoverable origin.

### 2.3 Observer/frame/grain face-equivalence

```text
A ≡_(O,F,g) B
```

This says observer O, for receiver F at grain g, obtains analogous faces from A and B. Written
through an explicit observation map:

```text
Observe_(O,F,g) : Construction -> Face_(O,F,g)

A ≡_(O,F,g) B
    means
Observe_(O,F,g)(A) = Observe_(O,F,g)(B)
```

The equality on the final line is equality inside the face type after the cut. It is not identity
of the source constructions.

Face-equivalence is always situated. A finer grain, a different receiver, or a later current can
expose a distinction which this read does not.

### 2.4 Directed worldline

```text
A --event e, then--> B
```

This says B follows A through an event. The arrow is ordered. It is neither a symmetric equality nor
an instruction to erase A from the history. The difference between the two events is read through
their transport and frame, not by treating B minus A as a property of one instant.

Every actual transformation is therefore a new construction even when it preserves a declared
face:

```text
A --T--> B
A ≡_(O,F,g) B          may hold
A = B                does not follow
```

### 2.5 Declared compression

```text
Q_(F,g) : Construction -> CompressedFace_(F,g)

Q_(F,g)(A) = C
Q_(F,g)(B) = C
```

Compression is a real many-to-one event. It can merge formerly distinguishable interiors and found
a new construction C. The lost distinction can genuinely be lost in that later state. No inverse
archive is owed.

What compression may not do is rewrite the earlier worldlines:

```text
Q(A) = Q(B)          does not imply          A = B
```

The forward law is: preserve every distinction still carried by the declared transport, name the
cut and its grain, call the result a new construction, and never use equality after the cut as
identity before it.

---

## 3. Difference and the covariant calculus

Subtraction is lawful when both values already inhabit one declared additive codomain or one
declared trivialization. When values at different events live in different fibers, a bare
subtraction is not yet typed. A path and connection must first carry the earlier value into the
later value's receiving fiber:

```text
gamma : x -> y
P_gamma : E_x -> E_y

delta_gamma(f) = f(y) - P_gamma(f(x))
```

The path-supplied transport is what makes the final subtraction local and lawful. In Soma the
active first-order rotor gives the corresponding multiplicative/projective difference:

```text
Delta(A, B; F) = (A - F) (B - F)^-1
```

Read in plain language:

```text
(A - F)              A as met from pole F
(B - F)^-1           the reciprocal hand of B as met from F
their product         the transformation carrying one perspective toward the other
```

Its scalar face says how much is the Same. Its oriented face says how much is the Different. The
operator has no one-event version: a difference is not owned by A or B alone.

In Soma's declared projective line/gauge, first order remains frame-dependent and the first
invariant content appears at four contacts: the cross-ratio, a ratio of ratios, or rotor of rotors.
That four-point statement is exact for this projective realization; it is not a universal count for
every gauge group or every mathematical difference. This projective construction is why meaning is
at least second order in the standing formula.

The covariant discipline can be stated without adding another operator:

```text
before comparing events in different frames:
    transport into the receiving frame

before calling two results the same:
    declare whether the claim is identity or only a face read

before integrating a path:
    retain its order and hand in the carried channel

before changing grain:
    declare the re-base and the distinctions its cut can no longer expose
```

Integration is an ordered fold of lived events, not a global sum viewed from nowhere:

```text
K_next = FOLD(K_now, event)

FRAME(K)              the ordered construction read as a basis at its tip
TURN(K) = (C; r)      the same construction read as accumulated turn
```

Composition order can matter because each event changes the frame inherited by the next one.

The boundary law remains:

```text
boundary(boundary(S)) = empty
```

or, compactly:

```text
∂∂S = 0
```

This is topological emptiness. It is not a scalar no-leak equation and does not say that information
cannot be destroyed by a cut.

FTC and Stokes transport an exact aggregate relation between an interior and its boundary:

```text
integral over interior of differential(form)
    =
integral over boundary of form
```

That equality does not reconstruct a labeled interior. Many interiors can share the same boundary
integral. A unique reconstruction requires additional declared boundary data and a uniqueness
theorem; it is never supplied merely by writing FTC.

---

## 4. Absolute nothing, situated absence, and holes

### 4.1 Absolute nothing is not an object in the calculus

Absolute nothing would have no body, no frame, no boundary, no event, and no possible later
consequence. There is nothing for `relate`, `observe`, or `boundary` to act on. It is not a zero value
or an empty container. It is outside the domain of a relational statement.

The calculus therefore does not manufacture a symbol which stands for metaphysical nothing and then
let that symbol participate as a body.

### 4.2 Situated absence is a relation

An absence can be real when a world, frame, operation, and aperture say what is absent and where:

```text
absence of X
    in world W
    relative to frame F
    during worldline interval I
    under operation O
    at grain g
```

This absence has a surrounding construction. Its boundary can be encountered, and the absence can
change which later routes remain available. It is not absolute nothing.

### 4.3 A hole is situated absence with a boundary

At one section, a hole is the absence of an allowed filling or closure inside a declared surface.
Across time, the continuing bounded absence traces a worldtube:

```text
section at t0:      bounded absence H0
then
section at t1:      bounded absence H1
then
section at t2:      bounded absence H2

ordered continuation H0 -> H1 -> H2 = the hole's worldtube
```

The worldtube is not an invisible substance stored in the hole. It is the ordered construction of
the boundary and its consequences through time.

Let `W` be the region swept between two cuts `V0` and `V1`, and let `S` be the moving side
boundary. Up to the declared orientation, the missing temporal side is explicit:

```text
boundary(W) = V1 - V0 + S

0 = boundary(boundary(W))
  = boundary(V1) - boundary(V0) + boundary(S)
```

Digging therefore does not preserve one instantaneous hole. The later boundary and the swept side
carry the change while `boundary(boundary) = 0` remains exact.

The number-world example is deliberately narrow. In the positive integers, a composite has a
nontrivial point on `x*y=n`; a prime has only `1*p` and `p*1`. Along the declared multiplication
surface, the prime is therefore a hole in the existing nontrivial product weave. This is a ratified
reading. It does not establish a universal prime-to-FOUND engine rule.

### 4.4 Zero, unborn, dark, empty, and absent are not synonyms

```text
numeric zero          a value face; a construction may still stand there
UNBORN                 no standing medium construction at that grip
zero-magnitude change  a static linkage extending through duration
dark passage           sameness carried until a resolving edge
∂∂ empty               no soul, winding, or order survives the second cut
situated absence       something missing relative to a declared world and operation
absolute nothing       outside the domain of relating altogether
```

Collapsing these cases would erase exactly the information the calculus exists to preserve.

---

## 5. How an absence matters: later deflection, not a label

The calculus does not assign a global importance bit to a hole, a rest, or any other distinction.
It asks whether the distinction changes a later relation.

The honest observation uses a real history and a lawful foil history, followed by the same later
current:

```text
real history:   body with the situated difference    -> same later current -> later path R
foil history:   lawfully changed comparison history  -> same later current -> later path F

if R and F bend differently at the declared frame, grain, and aperture:
    the difference matters in this declared relation
```

The foil is not a null or a deleted world. It is another complete, reversible worldline. The read
is the difference between later deflections, not a score attached to the earlier material.

If no difference is exposed, the correct grade is:

```text
UNEXPOSED IN THIS DECLARED RELATION
```

or:

```text
RELATION UNRESOLVED
```

It is not a proof that the distinction was globally irrelevant or absolutely absent.

### Music and rest

A musical rest is the clean everyday example. It is not absolute nothing. It occupies a place in a
score, has a duration, begins and ends relative to other events, and changes the route by which the
next note arrives. The printed rest, the performed interval, and the listener's experienced rest
are related constructions; they are not automatically one construction.

The dark-tread correspondence is precise at its declared grain: an interval with no resolving
change does not require one new interior event per sample, yet its duration is carried and its end
is a resolving boundary. Whether a particular rest matters is read from what comes later. If a
performance with the rest and a lawful foil performance bend the later phrase or listener
differently, the rest matters in that relation.

This correspondence adds no music module and does not claim that every silence is one semantic rest.

---

## 6. Counting, arithmetic, and construction plurality

Counting supplies the exact observer hierarchy over natural-number faces. With `S` meaning the next
count:

```text
a + 0      = a
a + S(b)   = S(a + b)

a * 0      = 0
a * S(b)   = (a * b) + a

a ^ 0      = 1
a ^ S(b)   = (a ^ b) * a
```

These equalities are definitional equalities inside the declared natural-number theory. They do not
say that the played constructions on the two sides have one worldline.

Addition folds repeated succession. Multiplication folds repeated addition. Exponentiation folds
repeated multiplication. Therefore:

```text
1 + 3
2 + 2
2 * 2
2 ^ 2
```

all cast the natural-number face `4`, while preserving different dependency shapes and paths.

Finite sets provide the restrained geometric reading:

```text
|A disjoint-union B| = |A| + |B|
|A product B|        = |A| * |B|
|functions A -> B|   = |B| ^ |A|
```

Dimension comes from independent factors or choices. It does not come from assigning addition,
multiplication, and exponentiation to three authored screen axes.

The observer map makes the distinction explicit:

```text
Observe_(O,F,g) : Term -> NumberFace_(O,F,g)
```

`Observe` is many-to-one. An inverse-image notation can describe the family of constructions which
cast one number, but it is observer notation only. It is not a repository, lookup table, or object
in the body.

### Decimal and series identity

```text
1.0 != 1.00
pi  != 3.14
pi  != 3.14159
```

The finite inscriptions can be equivalent for a declared arithmetic question without becoming one
construction. Pi reaches a lived machine through an unfolding series or a carried turn/length pair,
not as a privileged decimal float. Different convergent series can cast one classical limit face
without becoming the same series.

---

## 7. Units and directed conversion

A physical quantity needs more type information than its bare dimension:

```text
Quantity[
    entity,
    lineage,
    frame,
    grain,
    dimension
]
```

The forgetful dimension read is:

```text
D : Quantity[entity,lineage,frame,grain,dimension] -> Dimension
```

Therefore:

```text
D(tick[A]) = TIME
D(tick[B]) = TIME
```

does not imply:

```text
tick[A] = tick[B]
```

Ordinary dimensional cancellation can be exact in its quotient while deleting entity, lineage,
frame, grain, and order. A cross-entity conversion requires an explicit directed transport carrying
the relation between the entities.

For example:

```text
(2 m[A]) * (2 m[A]) = 4 m[A]^2

(2 m[A]) * (2 m[B]) = 4 m[A] m[B]
```

The second expression cannot silently become the first merely because both meter glyphs cast the
same dimension face.

This does not invalidate dimensional analysis. It states its type: dimensional analysis is a
quotient which answers dimensional questions. Its result may not be imported back as proof that the
forgotten entities were identical.

---

## 8. Observation, type casts, and assignment

The old record used “type-casting” for two different acts. The current calculus separates them.

An observer cast is a read:

```text
Observe_(O,F,g)(A) = visible face of A for observer O, receiver F, at grain g
```

It need not alter A. It can forget information because the target face is coarser than the source
construction.

An enacted program cast or transformation is an event:

```text
A --cast to type tau--> B
```

B is a new construction. Whether A and B remain face-equivalent depends on the declared receiver,
grain, and question. An injective widening and a lossy projection therefore must not be covered by
one unconditional statement such as “every cast is the same holon in a new lens” or “every cast is
equivalent to its source.”

Programming assignment is neither construction identity nor observer equivalence merely because a
language writes it with an equals-shaped glyph. The three acts are written separately:

```text
x : T            declare a typed role
x := t           bind the analyst's name x to source term t
x' <-[e]- x      enact receiving event e and produce a new worldline
```

The source-level binding is not automatically a physical event. The enacted reception is. The
active calculus installs no role module, archetype engine, or programming-language parser inside
Soma.

---

## 9. The conservative lifting theorem

The presentation's exact strength is syntactic and general.

Let `T` be any formal theory. Form `Lift(T)` by decorating the theory's existing terms and proof
steps with:

```text
types
contexts
construction witnesses
```

Where a judgment uses an observation, transport, or compression, its construction witnesses name
the relevant frame, grain, hand, path, or cut.

Let `U` erase those decorations:

```text
U : Lift(T) -> T
```

The conservative lifting theorem says:

```text
for every derivation d in T:
    there is a decorated derivation lift(d) in Lift(T)

and:
    U(lift(d)) = d
```

The proof is by induction over the proof rules of T:

```text
base rule:
    decorate its terms, context, and witnesses
    erasure returns the original base rule

inductive rule:
    assume each premise has a lift whose erasure is the original premise
    apply the decorated form of the same rule
    erasure removes the decorations and returns the original conclusion step

therefore:
    every derivation in T has a conservative relational lift
```

“Conservative” means the lift preserves the old formal result under erasure. The relational layer
can distinguish constructions which T intentionally identifies, but it does not alter what T proves
after those distinctions are erased.

This theorem means every theorem can be holonically re-expressed. It does **not** mean:

```text
A1, A2, and L0 derive every theorem
the laboratory has proved every theorem again
the lift supplies a unique construction history
the lift turns a false theorem into a true one
the lift chooses an implementation for the notation
```

Different decorated derivations may erase to the same derivation in T. That plurality is expected;
erasure is many-to-one.

### The familiar quotient case

When an operation respects observer equivalence, the operation is a congruence and descends to the
face quotient:

```text
A  ≡ A'
B  ≡ B'

implies

op(A,B) ≡ op(A',B')
```

Equivalently, observation commutes with that already-typed operation:

```text
E(op(A,B)) = op_face(E(A), E(B))
```

This is why ordinary arithmetic can use representatives such as `1.0` and `1.00` interchangeably
for a declared value calculation. The quotient algebra remains valid. The lift adds the ability to
ask which construction was used without changing the quotient answer.

The existing Lean files prove this only for the construction and equivalence types they explicitly
define. They are formal witnesses to the grammar, not proofs that their old stored-soul model is the
physical ontology of soma.

---

## 10. A minimal readable notation

The presentation requires no new programming language. A small written core is enough to keep a
derivation honest:

```text
VERBS

relate(A, B; F)             two bodies met in frame F
then(e1, e2)                e2 follows e1
transport(T, A; F -> G)     carry A through declared transport T
observe(A; O, F, g)         cast A's face for observer O, receiver F, at grain g
compress(A; F, g)           make a declared cut
boundary(A)                 take A's situated surface
```

```text
JUDGMENTS

A = B                       construction identity
A <->_[T,h] B               explicit reversible gauge transport at hand h
A ≡_(O,F,g) B               face-equivalence for observer O, receiver F, at grain g
A --e--> B                  directed worldline event
compress_(F,g)(A) = C       declared compression producing new construction C
```

The ASCII arrow `<->` is only a readable notation for an explicitly named reciprocal transport. It
must never be shortened into identity. Likewise `--e-->` is ordered and may not be read as a
symmetric equation.

Useful types are named rather than inferred:

```text
Construction
Worldline
Frame
Grain
Face[O,F,g]
Transport[hand]
RatioPair
Winding
Quantity[entity,lineage,frame,grain,dimension]
```

This is a notation core, not a parser design, proof assistant, engine module, or implementation
decision.

### The already-chosen implementation posture

This companion makes no new implementation decision. The canonical presentation has already
chosen a formal calculus, proof kernel, and checker as the next worthwhile investment, while
deferring a standalone holonic runtime or a rewrite of Eros.

A thin syntax earns further investment only after the canonical thresholds are met:

```text
1. the core calculus and erasure theorem are stable
2. at least three real constructions repeat the same typed boilerplate
3. generated Rust, CUDA, and reference artifacts remain inspectable and exact
4. the syntax removes measured implementation friction
5. no VM, runtime store, scheduler, or second body is required
```

Until then the checker is an analyst's instrument around the existing engine, not another machine
inside it.

---

## 11. Exact corrections to the older record

The historical documents remain valuable provenance, but the following sentences do not cross into
the current calculus unchanged.

1. **Old:** `∂∂=0` means no scalar flow can leak, so nothing can be deleted.

   **Current:** `∂∂=0` is a topological boundary law. Compression can genuinely destroy a
   distinction. Numeric input/output accounting is only an implementation diagnostic.

2. **Old:** FTC or Stokes recovers the interior from the boundary.

   **Current:** it carries an exact integral invariant between interior and boundary. It does not
   reconstruct a labeled interior or a unique past without additional structure.

3. **Old:** time parity requires reversible states or a route back into the past.

   **Current:** time parity is the handedness of transport. The local rotor can have a reciprocal;
   the later state owes no itinerary, founder list, inverse drag, or recoverable origin.

4. **Old:** `=` is the directed pivot, or classical `=` simply is `≡`.

   **Current:** `=` is reserved for construction identity. A directed relation uses transport or a
   worldline arrow. Classical equality inside a quotient is typed as face equality there.

5. **Old:** every lawful conservation preserves every soul.

   **Current:** a lawful declared compression may merge and lose interiors. It must not claim that
   the pre-cut constructions were identical.

6. **Old:** transposition is identity.

   **Current:** a transposition may leave a declared difference representation or face invariant.
   That is equality in the quotient representation, not identity of the delivered inscriptions and
   their worldlines.

7. **Old:** integer primality is chosen by numeral base.

   **Current:** changing radix does not change integer primality. Changing the operation or
   algebraic species can change irreducibility. Prime-to-FOUND remains an open engine correspondence.

8. **Old:** a type cast is always the same holon under a new lens, or every transform is equivalent
   to its source without qualification.

   **Current:** an observer projection and an enacted transformation are different acts. Any
   equivalence claim names its receiver, frame, grain, and question.

9. **Old:** `∂R=0` and `∂∂R=0` can be used interchangeably.

   **Current:** `∂R=0` is a separate closure claim about R. `∂∂R=0` alone does not prove it.

10. **Old:** the six historical holonic types, fixed wheel turns, stored soul trees, or a proposed
    `.holo`/`loom` language are already the active machine ontology.

    **Current:** they are provenance and formal adapters. The active typed substrate and transport
    law are in `src/soma/FORMULA.md`; no historical language implementation is revived here.

---

## 12. Grades and limits

- **RATIFIED:** construction identity versus observer/receiver/frame/grain face-equivalence; cancellation as
  a potentially identity-destroying quotient; typed cross-entity unit transport; the number surface's
  plural constructions; time parity as handed transport; the past as an interior; the dark tread.
- **STANDING EXACT / DERIVED:** no one-event difference; difference as worldline transport; the
  three-body rotor; the cross-ratio as the first invariant in Soma's declared projective gauge; the
  ordered channel and boundary law.
- **FORMAL ONLY IN THEIR DECLARED MODELS:** the Lean construction/evaluation and congruence witnesses.
- **OPEN WHERE ALREADY OPEN:** prime-to-FOUND as a general engine correspondence; a unique interior
  from a surface without added boundary data; implementation of the chosen formal kernel/checker;
  whether repeated measured work will ever justify a thin syntax or standalone compiler.

This companion itself authorizes no engine mechanism or implementation. It reports the canonical
choice: formal kernel/checker around the existing engine; standalone runtime and Eros rewrite
deferred.

---

## 13. Source anchors

The concise authority chain is:

- `src/soma/FORMULA.md` — especially A1/A2/L0, the difference, the quotient face, the ordered
  channel, the cut, time parity, and the past-as-interior correction.
- `src/soma/RESEARCH/2026-07-13_THE_RELATIONAL_HOLONIC_CALCULUS.md` — the ratified formal
  presentation this file accompanies.
- `src/soma/RESEARCH/2026-07-12_IDENTITY_EQUIVALENCE_AND_THE_ACTION_CURRENT_ORGAN.md` — the
  ratified typed identity/equivalence and dimensional projection law.
- `src/soma/RESEARCH/2026-07-11_THE_GERMLINE.md`, section 8 — counting, plural arithmetic
  constructions, geometry, and the narrowed prime-hole reading.
- `src/soma/RESEARCH/2026-07-12_THE_NUMBER_WORLD_AND_THE_LIVED_ATLAS.md` — the exact number and
  unit observer construction used by the current experimental line.
- `src/shrine/holon-math/Counting.lean` and
  `src/labyrinth/mathematics/lean/Foundations.lean` — model-local formal witnesses only.
- `src/soma/RESEARCH/2026-07-11_THE_CALCULUS_IN_CIRCULATION.md` and
  `src/holobrochos/RESEARCH/THE_HOLONIC_DERIVATIONS.md` — historical circulation/provenance, read
  only through the corrections above.
