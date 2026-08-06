# Phase 7 receipt — broad mounting

**Truth status:** `established-bounded` at the declared apertures below.

**Evidence:** `implemented-exact` for every law and refusal; `computational-witness` for every
measured figure. The returned artifacts are `receipts/PHASE_7_RESIDENT_MOUNT_DEED.txt` and
`receipts/PHASE_7_BROAD_MOUNT_DEED.txt`, both written by the deeds themselves.

Phase 7 was recut into three movements on 2026-08-06 because reading the Phase 6 port against its
source established that scale is not a parameter of it. All three returned.

---

## Movement 1 — the cost laws, refounded and measured

The three cost claims the Phase 6 regrade named are refounded against
`suffix_ecology.rs` at checkpoint `93834398`.

| | Superseded | Refounded | Source owner |
|---|---|---|---|
| transitions | one flat array scanned per lookup | **per-state fan-out chain**, held in canonical symbol order with a tail pointer | `SuffixState::transitions: RelationSpan` |
| incidence formation | fixpoint relaxation plus per-state subtree rescan | `first_child`/`next_sibling` in `O(states)`, then **one explicit-stack depth-first walk** | `from_suffix_tree`, `:338-395` |
| span query | rescan of the occurrence population | **a stored interval, read** | `state_spans` |

**The falsifier, demonstrated.** The aperture quadruples — 54 symbols to 216, 80 states to 358 —
and both implementations were instrumented with identical work counters:

```text
                 superseded            refounded
formation        28,108 -> 775,011     366 -> 1,622
                 x27.57                x4.43
lookup           15,854 -> 306,993     1,465 -> 6,526
                 x19.36                x4.46
```

The bound is eight. **Both superseded ratios fail it and both refounded ratios pass with margin.**
The state populations are identical under both — 80 and 358 — so the returned structure did not
change; only its cost did.

Two refinements the source owner does not have. The fan-out chain is held in a **canonical symbol
order**, so a germ lookup stops at the first symbol that follows the one sought and never walks
the separator population; and its **tail pointer** makes an ascending insertion constant, which
matters because separators are necessarily one per informant path and are therefore the only
fan-out that grows with the source population. Without the tail, root insertion is quadratic in
the source count.

---

## Movement 2 — the arena crossing

`structure::resident_span` carries a pointer and an extent and **allocates nothing, frees nothing,
and owns nothing**. The suffix ecology and the source incidence became `suffix_arena` and
`incidence_arena` — spans plus counters — with every law a free function over them. The
fixed-capacity classes remain as thin providers, so every Phase 6 assertion returns identically
and the two forms differ only in who holds the pages.

The evidence this was required is physical and was already returned in Phase 5: a three-kilobyte
standing surface overflowed the default one-kilobyte device stack, and the repair was a
reservation. **No reservation admits a corpus.**

**Returned at the declared aperture** — 4,000 informant paths of twelve germs:

```text
states                   26,031
transitions              74,030
caused occurrences       48,000
resident octets          23,968,000
frame octets                    224
device answered queries       1,024
parity failures                   0
host replay work                  0
standing unchanged              yes
```

**Twenty-four megabytes of ecology; two hundred and twenty-four octets crossing into the kernel
frame.** The query laws take their arena by **const reference**, so a hot device path that
founded, linked, or froze anything would not compile — the gate is a type error, not a runtime
check.

**The corpus scaling law, measured.** The germ alphabet is held fixed while the informant-path
population doubles. A fan-out cost growing with the corpus would quadruple the total; one set by
the declared alphabet does not:

```text
formation   120,122 -> 152,122   x1.27
lookup   10,041,087 -> 19,220,371   x1.91
```

Both inside the bound of three. **The remaining fan-out term is alphabet-set, not corpus-set.**
That is measured, not argued.

---

## Movement 3 — the mount

The corpus is this project's own record: every markdown container in the repository, gathered in a
stable order, split on blank runs. The apparatus owns the containers and the splitting entirely;
the interior receives octets, a container ordinal, and a section ordinal, and never a path or a
name.

```text
containers                                    734
occurrences                                37,278
surface octets                          8,913,746
duplicate witnesses                             1   (declared control)
version fibers                                  1   (declared control)
open causal fibers                         37,278

octet aperture                                 64
octets crossed                          2,024,079
states                                  2,430,094
transitions                             3,679,276
caused occurrences admitted             2,024,079
formation steps                        11,744,453
lookup steps                          779,347,367
resident octets                       636,445,538
frame octets                                  320

global pair population                          0
hot host replay work                            0
bounded delta equal                           yes

rest octets                            10,703,154
remount octets                         10,703,210
founded from octets alone                     yes
remount exact                                 yes

mount consumed host                           yes
consumed host refuses admission               yes
refusal returned predecessor                  yes

device answered queries                     1,024
parity failures                                 0
```

**The three admission gates the source owner states literally all return.**

- `global_pair_population == 0`. The conditioning is linear in crossed octets and never compares
  one occurrence against another, so the complete pair product has no place here to be formed.
- `hot_host_replay_work == 0`. Formation is the host's entirely; the card reads.
- `bounded_delta_equal == true`. Appending one emanated occurrence advanced the rest image by
  **fifty-six octets** — four of surface, one forty-eight-octet record, one four-octet causal
  edge — and every earlier payload region is an exact prefix of the later one. The card may
  therefore advance by appending those octets rather than re-forming the body.

**Three source laws, carried.**

- **The refusal returns its predecessor.** A refused crossing consumes nothing and the host still
  admits. Absent hardware must not destroy the only conditioned body merely because success would
  have consumed it. This is the same law as `training_proposal` returning intact on a stale
  generation and the ordinal atlas's recovering admission.
- **Equal native identity with a different surface stays plural** — and here it is decided by
  **exact octet comparison against the retained surface, not by a digest.** A digest answers the
  same question by collision-bounded proxy; the surface answers it exactly. The declared control
  returned one duplicate testimony as multiplicity and one version fiber with its predecessor
  still readable.
- **Corpus adjacency is not ancestry.** All 37,278 document occurrences leave their causal fiber
  OPEN, because no causing witness was supplied for any of them. Not one adopted its predecessor.
  The single emanated occurrence, which did supply its cause, is the contrast.

**A law that returns zero proves nothing about itself.** The corpus carries no repeated section
and no revised surface, so the plurality laws would have been implemented and never exercised.
The declared control exists for that reason and the grade requires it to return non-zero.

---

## Boundary

**This is a broad mount of documents. It is not the laboratory's conditioned rest.**

- The material is markdown containers. The rollout importers — `TextMaterialInput::CodexRollout`
  and `ClaudeCode` — are **not** ported, so role and phase carry `document` and `received`
  throughout and the human/assistant/emanated population is not present.
- The conditioning aperture is **sixty-four octets per occurrence**. The full 8.9 MB surface is
  retained, rested, and remounted exactly; only the first sixty-four octets of each occurrence
  cross into the suffix ecology. A whole-surface conditioning is a larger reservation and a longer
  formation, not a different law.
- The laboratory's 42,937 prose sections, 25,490 production relations, and 101 MB route rest
  belong to the Rust body. **37,278 sections over 734 containers is this body's own figure** and
  is the same order; the relation population and the route rest are not claimed.
- Nothing here generates readable surface or returns a proof. Those are Phases 8 and beyond.

## Registered as open

- **Per-state fan-out is a linear scan.** The remaining term is bounded by the declared germ
  alphabet and was measured to be corpus-independent, so it is a constant factor and not a wall.
  Reducing it further wants per-state contiguous sorted blocks with a bisection, which is a layout
  question and belongs with the arena rather than with the law. Registered, not scheduled.
- The **rollout importers** and the human/assistant/emanated population.
- **Whole-surface conditioning** at the full 8.9 MB.

## Gates

Architecture, no-float source, container-ownership, compatibility-route, derived-identity,
owner-DAG, file-size, PTX and SASS binary, and build-manifest audits pass on a clean tree.

Three audit catches during construction are worth recording, because all three were the audit
reading the source more literally than the author did: `half` as a variable name is a forbidden
carrier; `7.1` as a phase number matches the decimal-literal pattern; and the words `double` and
`float` in prose are carriers wherever they stand alone. The phase numbering became **movement**
numbering throughout the sources as a result.
