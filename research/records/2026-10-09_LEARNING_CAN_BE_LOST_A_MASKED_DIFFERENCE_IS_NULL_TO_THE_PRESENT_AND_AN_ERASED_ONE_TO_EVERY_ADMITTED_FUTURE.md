# Learning can be lost: a masked difference is null to the present, an erased one to every admitted future

**Date.** October 9 (the lens: October 7). **Issues.** #73, #62, #63. **Grade.** Lens record. Each
section carries its own grade. §2 joins formal-checked owners. §2.4's contraction is checked by
exact computation, and the lemmas of §2.2 and §2.5 are proved here. The joins in §4 are owed.

## 1. The lens

Brandon, October 7: learning can be lost, and the machine must be able to lose it. He has never
argued for an invulnerable intelligence. A model taught a broad capacity can be made to throw away
whole subjects, for example by teaching it one dismissive reply across many of them (ablation,
alignment, or fine-tuning in general). Large contemporary singularities can destroy structure and
behaviour outright. Sensitivity and honest physics matter more than protection. He distinguished
two losses: a **masked** one, where an association is suppressed but its structure persists, and
an **erased** one, where the circumstances leave the internal cycles themselves different.

The same message tied this to normalization across the whole machine and to a learner that learns
how to learn. Those belong to the directionality and tower readings and are not derived here.

## 2. The derivation in the objects

### 2.1 The three cases of a learned difference

[definition; agent-inferred] A teaching is a word of the field's steps (ingest, key location,
refinement, deposition: the generators of `HNN/Retention.fieldStanding`). It moves a constitution
`Θ_0` to `Θ_1`. Read it against a **reference** `Θ_ref`: the constitution the same passage leaves
without the subject's teaching. In a linear chart the learned difference is `δ = Θ − Θ_ref`. Let
`F_now` be the present receivers' face and `F_fut` the admitted future's: every admitted word of
steps, deposits and actions followed by every admitted receiver. Then:

- **held:** `δ ∉ ker F_now`, so the present receivers still read it;
- **masked:** `δ ∈ ker F_now` and `δ ∉ ker F_fut`. It is null now, and some admitted word (a probe
  or a re-teaching) followed by an admitted receiver separates it;
- **erased:** `δ ∈ ker F_fut`, so no admitted future separates `Θ` from `Θ_ref`. They are one
  retention class.

[proved-derived; formal-checked owners] The three cases partition the differences, because
`ker F_fut ⊆ ker F_now` (`Holarchy/Hearing.futureNull_le_ker_present`, the join of
`Foundation/CausalRelevance.futureCollapsed_le_presentCollapsed` and
`Foundation/Receiver.theCollapsedIsTheJointKernel`). Masking exists: a present-null difference
is reopened by a later navigator step (`CausalRelevance.NonLinear.swap_reopens_second_coordinate`).
In a nonlinear chart the difference is replaced by the pair `(Θ, Θ_ref)` and the kernels by
`futureAgreement`.

[definition; formal-checked owners] **Every loss is relative to an admitted family.** Extinction is
defined against a receiver family and a tolerance (`Foundation/Standing.Extinct`; atlas
`standing.extinct`). Its documentation says that a wave has no universal death and that a richer
family separates it again. Identification is antitone in the declared family: enlarging the
family can only separate (atlas `quotient.declared-family-antitone`). So a difference erased for
one family can be masked for a larger one. The HNN states this of its own collapse: a later
family that adds a receiver reads a released locus (`HNN/Retention.admitted_growth_reads_released`,
a formal-checked counterexample on the path `0 → 1 → 2`).

### 2.2 Masking is redistribution; erasure is a merge, paid for

[proved-derived] **Against a complete receiver family, erasure is a merge.** Let the family's joint
reading be injective on constitutions, and let a forgetting teaching `D` act on the taught
constitution `Θ_1` and its reference `Θ_ref,1`. The difference is erased exactly when
`D(Θ_1) = D(Θ_ref,1)` with `Θ_1 ≠ Θ_ref,1`: the identity word followed by the injective reading
already separates any two distinct constitutions. Against a smaller family a difference can also
leave every admitted reading without any merge, by moving into coordinates that no admitted word
returns to a receiver. A larger family separates it again, so for that family it is masked.

[formal-checked owners] An isometric transport never merges. On the exact rotation
`((3x − 4y)/5, (4x + 3y)/5)` the energy `x² + y²` is kept along every word, and a difference is moved
between coordinates, never removed, so nothing nonzero is ever extinct for the full receiver family
(atlas `standing.rotation-never-extinct`; Lean
`Foundation/Standing.the_difference_is_redistributed_not_removed`,
`nothing_nonzero_is_extinct_at_zero_tolerance`). In a lossless medium every lost learning is
masked for the full receiver family: the difference moves into coordinates the present receivers
do not read.

[proved-standard; owners] Physical erasure is a many-to-one step: a merge of classes, a contraction,
or a structural release. Landauer prices the merge, never transport or a lossless rebase: the erased
bits are `Σ_blocks ⌈log₂ m_b⌉` (zero exactly when every block is a singleton), and the heat is at
least `k_BT ln 2` per erased bit (atlas `floor.landauer-erasure`; the guide's
[emanation and resonance](../../docs/ELEMENTARY_OBJECTS.md#emanation-and-resonance) section, Landauer
for erasure only). Merging a taught and an untaught constitution into one class erases
`⌈log₂ 2⌉ = 1` bit. The HNN's structural release is an erasure no deposit undoes: a released locus
is the zero map, and every admitted deposit keeps it released (`HNN/Retention.release_structural`).

[agent-inferred] This is the honest physics the lens asks for. A masked loss can be free. An
erasure owes its dissipation, and its receipt should say what it erased. A destructive event is
lawful: the certified deposition law forbids an uncertified step
([lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md),
lesson 6), not a large one. A large change is admitted when its energy bound holds at the commit
and its erasure is receipted.

### 2.3 Ablation is a receiver test

[definition; agent-inferred] To ablate a locus set `U` is to set `Θ|_U` to its released value
`rel` (the zero map), exactly as the collapse releases a locus. The ablated difference is
`δ_U = Θ − Θ[U ← rel]`. The ablation loses no learning for the family exactly when
`δ_U ∈ ker F_fut`. The canon already treats behavioural ablation as the test of an attribution
claim, not as a condition of every learning occurrence
([conditioning and learning](../../docs/canon/03_CONDITIONING_AND_LEARNING.md), historical doctrine).
This section gives that test its receiver form.

[formal-checked owners] The HNN's collapse is the certified case. A locus outside every admitted
receiver's time-indexed causal diamond is released without changing any admitted reading
(`HNN/Retention.release_indistinguishable`). The diamond rule is tight: releasing a retained edge
changes a reading (`HNN/Retention.retained_edge_is_read`). Inside the diamond an ablation is an
experiment. Its receipt is the set of admitted (receiver, word) pairs whose faces changed, and each
such pair is a separator that refutes the merge (atlas `series.difference-separator`, Lean
`Foundation/HigherDifferenceTransport.separatingDifferenceWord_reopens_quotient`). A difference that
is heard but not listened to refutes the reached action as a retention
(`Holarchy/Hearing.heard_not_listened_refutes_standing`).

[formal-checked owner] An ablation that is lossless today can lose learning for a later receiver
(`admitted_growth_reads_released`). That is why the aeon's close refuses a growing family and every
pending ratio whose receiver still hears a released locus (Rust `hnn::retention::contained` and
`hnn::retention::separator`).

### 2.4 A teaching erases only what its comparisons reach

[proved-standard; checked by exact computation] Take a quadratic comparison read through a linear
face `F`, `½‖FΘ − y‖²`, descended by `Θ ← Θ − η Fᵀ(FΘ − y)`. Two constitutions taught the same
target (the forgetting teaching on `Θ` and on `Θ_ref`) move their difference by

```text
δ ← (I − η FᵀF) δ
```

The map is the identity on `ker F`. On the row space `range(Fᵀ)` it multiplies each singular
direction by `1 − ησ²`, which lies strictly inside `(−1, 1)` when `0 < ησ² < 2`. With `F = (1 0)`,
`η = ½` and `δ = (1, 1)`, the steps give `(1/2, 1)`, `(1/4, 1)`, … `(2^-k, 1)`: the present face
`Fδ = 2^-k` goes to zero and the second coordinate stays `1`. A later admitted step
`T(x, y) = (−y, x)` reads `F T δ = −1`. The teaching made the subject present-null and left it
masked.

[agent-inferred] The HNN's deposition law has this shape in general. A constitution changes only by
covectors that reached its locus (the guide's [deposition](../../docs/ELEMENTARY_OBJECTS.md#8-deposition);
Lean `Objects/Deposition.deposit_local_edges`, `deposit_local_region`, `unreached_edge_unchanged`;
`HNN/Retention.deposit_descends`). A forgetting teaching therefore contracts only the part of a
learned difference that its own comparisons reach. The part orthogonal to every reached covector is
untouched, and it is masked if some admitted future reads it. Erasing it needs comparisons that
reach it, or a release. Brandon's example of one
dismissive reply taught across many subjects is this case: it merges the subjects' present faces,
and whether it masked or erased them is decided by the reach of its comparisons and by the admitted
future, never by the present faces (`Context/Merge.equal_present_faces_do_not_merge`).

### 2.5 Re-acquisition affirms masking, never erasure

[proved-derived] **Lemma.** Let `Θ` and `Θ_ref` agree under every admitted teaching word followed
by every admitted receiver. Then for every target set `G` of faces, the least teaching length that
reaches `G` is the same from both.

*Proof.* For every word `w`, `F(T_w Θ) = F(T_w Θ_ref)`, so the words whose face lies in `G` are the
same set from both, and so are their least lengths. ∎

So a re-acquisition shorter from the forgetful constitution than from the reference is itself a
separating word: the loss was masking. The converse fails, since equal lengths need not mean that
no word separates. Masking is affirmed by one separating word. Erasure is affirmed only by a
certificate: the contraction certificate of
[affirming extinction](../../docs/ELEMENTARY_OBJECTS.md#affirming-extinction) (Lean owed in #62), or
`release_structural` for a released locus. A finite enumeration of words can only refute erasure,
because `Extinct` quantifies over every word.

[measured, laboratory; not rerun] The laboratory (private) measured this instrument as its
re-acquisition ratio, May to June. On one substrate combination a source re-acquired in 274 events
against the laboratory's approximate 5,000 for first acquisition, and it recorded that unmounting a
skill degraded its expression, not its comprehension. Its own ledger marks the reading as shown on one
substrate combination only.

## 3. What the repository already owns

- The kernels and their order: `Holarchy/Hearing` (`futureNull_le_ker_present`, `futureNull_null`,
  `act_is_standing_iff`, `heard_not_listened_refutes_standing`), `Foundation/CausalRelevance`
  (`futureCollapsed_le_presentCollapsed`, `NonLinear.swap_reopens_second_coordinate`).
- Retention as the future-sufficient quotient: `Foundation/Standing/Law.standingLaw_exists_iff_future_factors`,
  the [retention contract](../../docs/ELEMENTARY_OBJECTS.md#the-retention-contract), and the
  history witnesses `Foundation/Standing.two_histories_leave_one_standing` and
  `one_present_face_two_standings_separated_later` (atlas `compression.two-histories-one-standing`).
- Extinction and its receipts: `Foundation/Standing.Extinct`, `extinct_iff_release_width_inside_tolerance`
  (atlas `standing.extinct`, `standing.rotation-never-extinct`).
- The HNN's release: Lean `HNN/Retention` (`release_indistinguishable`, `release_structural`,
  `admitted_nonincreasing`, `admitted_growth_reads_released`, `retained_edge_is_read`); Rust
  `hnn::retention::{collapse, contained, separator}`.
- Equal present faces never license a merge: `Compression/Landmark/Context/Merge.equal_present_faces_do_not_merge`.
- Dormancy keeps a key while it is silent: `Compression/Landmark/Context/Dormancy` (a dormant
  layer's key is retained through the aeon it sleeps in; `layer_survivors` filters keys only where
  the layer sounds). The species collapse splits back exactly (`Context/Evolution.species_split`),
  which is masking at the population.
- The deposit receipt `hnn::constitution::DepositReading` already reports the residuals its lattice
  releases and their bits (`released`, `released_bits`). Whether such a release erases learning is
  what §2's classification decides; the bit count alone does not.

## 4. The joins owed

1. **The classification on the hearing owner** (Lean, #62). Definitions `Masked δ :⇔ δ ∈ ker F_now
   ∧ ¬ FutureNull δ` and `Erased δ :⇔ FutureNull δ` on `HearingLaw`, with the partition
   `held ⊔ masked ⊔ erased` from `futureNull_le_ker_present`. The step family must include the
   deposits, as `fieldStanding`'s generators do.
2. **The ablation receipt** (Rust, #73). Its consumer is `hnn::retention`. `ablate(U)` applies the
   collapse's existing release to a declared `U`; no new release law is written. Its receipt lists
   the admitted (receiver, word) pairs whose faces changed. The equation at the consumer:
   `receipt(ablate(U)) = ∅ ⟸ U ∩ diamond = ∅` (`release_indistinguishable`), and every member of a
   nonempty receipt is a separator.
3. **The reach lemma** (Lean, #62). Under deposits drawn from reached covectors, a teaching leaves
   unchanged every difference component orthogonal to all the covectors it reached. In the
   quadratic chart this is `(I − ηFᵀF)|_{ker F} = id`.
4. **The re-acquisition lemma** (Lean, #62): §2.5, a few lines on `StandingLaw`.
5. **The erasure receipt** (Rust and Lean; #73, #62). A deposition or release that merges retention
   classes reports its erased bits `Σ_blocks ⌈log₂ m_b⌉` beside `DepositReading`, so that its
   Landauer floor is readable. A masking teaching owes none.

**Acceptance for the first loop** (fixed before any build). A known-truth terrain of two source
families `A` and `B`, generated by exact routines, in any modality. Teach both; then teach one
shared reply across `A`'s contexts with certified steps. Read, exactly:
- `A`'s present faces;
- the least re-acquisition length of `A` from the forgetful constitution and from the reference
  never taught `A`, as two integers;
- `B`'s faces before and after (collateral loss);
- the ablation receipt of the loci the forgetting teaching reached.

Report each loss as held, masked (a separating word found) or unaffirmed. Erasure is reported only
with its certificate.

**Recorded failures checked.**
- An uncertified deposition step: the forgetting teaching runs on the certified step. Erasure is
  never forced by a larger step, which would also answer a refusal with a larger limit.
- An authored routine standing in for learning: the ablation is the collapse's own release read by
  the admitted receivers, not a routine that computes an answer.
- Bits read as progress: the classification is by separating words and exact counts, not by code
  length.
- Text run as the exception: the source families may be text, image, acoustic or motor.
- Seen graded as unseen: no transfer is claimed. The loop measures recovery of seen families, and
  says so.
