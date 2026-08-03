# Pure holonic engine

This is the normative, language- and hardware-agnostic engine contract. A realization may use any
language, runtime, device API, storage medium, or proof environment that preserves these types and
laws. Names such as text, image, Lean, repository, CPU, and GPU do not occur in the semantic core.

## 1. Minimal owners

### 1.1 Exact structure

Owns finite/local structural carriers, not domain meaning:

- stable occurrence and event identities;
- typed ports and oriented incidence;
- receiver-bounded, causally reachable sequences, sets, relations, queues, and sparse populations
  with an explicit support certificate plus admission, departure, traversal, capacity, and memory
  receipts;
- exact values or certified bounded values;
- persistent/shared immutable paths and branch-local differences.

It owns no scheduler, semantic registry, codec policy, device choice, world, or live morphology.

### 1.2 Continuing body

Owns exactly one live standing:

\[
H_v=(v,C_\bullet,\partial,m,s,J,\ell,\mathcal O).
\]

`v` is the exact head identity, `C/∂` caused incidence, `m` reusable morphology, `s` local
constitutive/resource state, `J` active sparse current, `ℓ` lineage, and `O` open obstruction.

The body is non-cloneable and carries one linear continuation capability `κ_v`. Opening transfers
`κ_v` into the pending deed; resume, commit, recovery, and rest consume that capability and return
exactly one capability for the unchanged or successor head. While a deed is pending, the body
cannot open another continuation. It can be moved, rested, remounted, observed through a
bounded non-resumable receipt, or shared only through immutable substructure plus local
differences. A rest image transfers `κ_v`; an observer/parity image never contains it.

### 1.3 Event law

For standing species `S`, input `I`, outbound deed `O`, pending deed `P`, returned occurrence `R`,
and staged difference `D`:

```text
EventLaw<S,I,O,P,R,D>
  validate_standing(&S) -> Valid | Refusal
  open(&S, ContinuationCapability, Occurrence<I>)
    -> (P<ContinuationCapability>, O) | Refusal<ContinuationCapability>
  resume(P<ContinuationCapability>, Occurrence<R>)
    -> D<ContinuationCapability>
     | (P<ContinuationCapability>, O)
     | Recoverable<ContinuationCapability, Obstruction>
  validate_delta(&S, &D<ContinuationCapability>) -> Valid | Refusal
  commit(S, D<ContinuationCapability>)
    -> (S', ContinuationCapability', Consequence)
     | Recoverable{S, D<ContinuationCapability>, obstruction}
```

`P` carries the unique continuation capability, predecessor and open-deed identities, outbound port, caused support, and the exact
continuation expected from the world. Each returned occurrence retains its own identity, port,
lineage, and caused support. `D` carries predecessor identity, input and return occurrences,
read/change support, morphology delta, successor current, boundary consequence, stress,
obstruction, and lineage. It contains no complete copy of `S`.

### 1.4 World membrane

Owns atomic change of the continuing body while exterior crossings remain typed continuation-port
events:

```text
receive(body, occurrence, exterior)
  1. validate body
  2. open one owner-native pending deed and outbound occurrence
  3. cross the named exterior port and retain each returned occurrence
  4. resume the pending deed until delta, further pending port, or obstruction
  5. validate and commit owned standing once, or recover body + capability + pending testimony
```

No partial body successor becomes visible. Cross-apparatus atomicity is claimed only when the
exterior supplies an explicit prepare/commit protocol. Otherwise, an irreversible or stale
exterior consequence and any required compensation remain an obstruction; it is never erased by
pretending the whole world rolled back. Exterior refusal cannot destroy the predecessor or mutate
an unreported hidden capacity.

### 1.5 Current propagation

Owns receiver-local advancement through caused incidence. It carries a sparse front until exact
rest, complete standing return, or a genuinely surviving cyclic boundary. Successive fronts are
ordered; members of one front are parallel only with an interchange certificate.

It must never expand a complete global forest, all-pairs population, or maximal antichain merely to
discover the next local crossing.

Here *local* means receiver-bounded causally reachable support accompanied by the certificate that
founded it. Quiescence is a compositional certificate of no local current and no in-flight owned
continuation across the declared boundary—not a global queue-emptiness scan or polling result.

### 1.6 Interaction/constitutive organs

Domain organs supply `M_(m,U)`. Each organ is mounted at typed local incidence/ports; the body owns
no global organ registry. Contact is a typed pullback/equalizer (or the domain's named universal
construction) yielding zero, one, or plural compatible local organs. Zero match and unresolved
plurality remain explicit obstructions. An application composes organs; it does not clone their
standing or introduce another universal interaction owner.

### 1.7 Codec organs

A codec is a typed relation between presentation charts, optionally stateful/conditionable. It
retains source occurrence and version lineage. Reflection can revise a codec only by returning a
lineaged revision to the same continuation.

### 1.8 Executors

An executor receives a reified causal program plus bounded structural/constitutive data and
returns an exact successor delta or explicit obstruction/resource receipt. Capability matching is
an exterior representation relation over program requirements and apparatus affordances; it does
not enumerate or select semantic organs. Executors do not rank semantic candidates, invent event
order, select receiver meaning, or own continuing standing.

### 1.9 Observers

Observers receive bounded testimony. They may materialize arrays, graphs, tables, images, logs,
statistics, hashes, or telemetry. Their products do not feed source standing unless returned
through an explicit caused event.

## 2. Essential types

The following algebra is conceptual; implementations may encode it differently while preserving
the laws.

```text
Occurrence<T> = { id, source, event_cut, port, payload:T, lineage }
Port<S>       = { identity, direction, boundary, carrier_schema:S }
Current       = sparse population of (lineage, site, phase, multiplicity, local_state)
Incidence     = the body's one live owner of oriented causal structure and local support
Morphology    = constitutive parameters + codecs + response spectra referring to owned Incidence
Obstruction   = typed open alternative with cause, support, and retry/remount conditions
Pending<κ>    = { continuation:κ, predecessor, deed, outbound_port, expected_return_ports, support, lineage }
Delta<κ>      = { continuation:κ, predecessor, input_event, return_events, reads, writes,
                  incidence_delta, morphology, current, return, stress,
                  obstruction, lineage, resource_obligation }
Continuation  = unique consumed capability authorizing one resume/commit/rest transition
Rest          = exact native standing + transferred Continuation; no developmental source
Receipt       = receiver/aperture-specific testimony, never standing by default
```

No live type implements unconstrained duplication. Identities are minted by their owner and never
reconstructed from path, array index, worker lane, or digest.

## 3. Laws every realization must satisfy

1. **Identity:** one event occurrence is applied at most once to one exact predecessor.
2. **Causality:** every standing difference has a caused path from admitted occurrence or inherited
   organ.
3. **Locality:** an event reads/writes only its declared support and owner-native logical resources.
4. **Boundary:** `∂²=0` where an oriented chain complex is declared; ports compose with typed
   lineage.
5. **Atomicity:** refusal reveals no partial successor.
6. **Obstruction preservation:** unresolved alternatives remain inspectable and cannot be converted
   to negative verdict or silent fallback.
7. **Rest:** native remount is exact and performs zero developmental-source replay.
8. **Projection non-creation:** a receiver quotient creates no source incidence.
9. **Stateful equivalence:** condensation is a coinductive bisimulation for a versioned receiver
   family: related bodies admit equal next-input languages and, after every admitted input, return
   equal receiver testimony or obstruction and related complete successor incidence, current,
   morphology, lineage, and deterministic resource state. The source fiber or an exact
   reconstruction capability is retained so enlargement can reopen it.
10. **Interchange:** an admitted `InterchangeCertificate` names one predecessor, two staged
   footprints, lawful rebasing in both orders, a canonical combined delta, exact identity/causal
   order equality, equivalence of all other successor standing/consequences/obstruction/logical
   resources, and required higher-coherence witnesses. Sequential proof execution adds no causal
   edge between independent occurrences. Without this certificate, the front remains ordered.
11. **Resource honesty:** physical/logical pressure changes the same body or remains open.
12. **Apparatus neutrality:** admitted realizations enact the same typed law; semantic identity does
    not depend on device, filesystem path, process order, or codec spelling.

## 4. What is intentionally absent

- global scheduler/phase machine;
- model/data/program trichotomy;
- universal graph store;
- application-owned candidate or association registry;
- semantic device selector;
- acceptance-count gate;
- compatibility decoder;
- hidden fallback executor;
- complete-body transactional clone;
- renderer-owned source geometry; and
- magic numerical thresholds that decide causality, recurrence, or interaction.

The engine is small because the domain law lives in domain organs and the plurality lives in local
currents, not because the machine lacks expressive power.
