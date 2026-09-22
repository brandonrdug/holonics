# Retention is a quotient, not a tape, and the source enters as phase-carried moments

**Reviewed tree:** `1aa2d6d4`. **Request:** recover Brandon's direct messages from the Codex
and Claude Code logs, review Astra's campaign returns since `363a6483`, and audit how both
agents use "learning" and "retention". This audit changes documentation only; it names the
native and formal objects that the next campaign removes or replaces.

## What Brandon said

[established-bounded; process-audit] Direct-message coordinates, private logs retained
locally under the [agent protocol](../../docs/AGENT_PROTOCOL.md):

- Codex `01a0c617-e325-7ac0-99b2-08a7b9a65e76`, 2026-09-22 04:33 UTC: *"I am also getting
  alarmed by the way you keep saying 'preserves' and the way you keep talking about retention,
  you have a habit of injecting contaminating retainment of causal histories in a way that is
  not compression."* This answered Astra's report that the contract would *"retain coefficient
  error and amplitude history, and preserve old comparison cuts through restart."*
- Claude `2dffbb64-42e4-468b-8609-2ca1088308b7`, 2026-09-22 16:07 UTC: the contamination
  *"comes from how you needlessly write something along the lines of 'a current changes a later
  current's standing', like it's just a stupid quote you paraphrase and use to describe what
  learning is."*
- Claude `fbee86d2-…`, 2026-09-21 20:43 UTC and Codex `01a0bc5f-…`, 2026-09-21: the source
  passage is phase-carried context on a fixed machine (rotor/Bombe reading); the HNN site is
  the helical pair interaction; generator count is independent of source length.

## The word and its abuse

[definition] The framework already defines retention exactly, and the definition excludes the
archive. The [relational behaviours](2026-07-12_THE_RELATIONAL_BEHAVIORS.md) table: retention
is *"prior contact remains available after receiving and rest to bend later current"*, and what
is **not** required is *"a stored record, lookup, or permanently exposed flag"*.
[The continuous net](2026-07-14_THE_CONTINUOUS_NET_AND_THE_LOCAL_SOLVE.md): *"Retention is
factorhood. Nothing looks up an answer."* `Foundation/Standing.lean` and
`crates/holonic-engine/src/standing.rs`: standing is **any quotient sufficient for the admitted
future** (`standingLaw_exists_iff_future_factors`); *"causal origin does not prescribe an event
archive"*; nothing requires the passage history to be recoverable from the retained object.

[established-bounded; source-inspected] "A current changes the standing that a later current
meets" is a **consequence** of that law read backwards. Used as the definition of learning it
prescribes a sequential state chain, `z_(k+1)=T(z_k,u_k)`. The chain's adjoint then prescribes a
tape of every intermediate state; validity of old comparisons across later updates prescribes
frozen producing cuts; restart prescribes serializing the tape; and a formal counterpart
prescribes a fold over an update list. Each step is locally reasoned. Their sum is the event
archive the definition excludes. The rotor reading Brandon gave rules this out directly: after
`n` keypresses an Enigma's state is its rotor phases and fixed material, not the `n`-step
history, and the Bombe infers configuration from pairwise loop closure, not from a replayed
transcript.

## Where it landed in the campaign

[established-bounded; source-inspected] Per commit, from the plan iteration forward:

| Commit | Object | What it does | Status |
|---|---|---|---|
| `363a6483` plan iteration | [Ordered source and its statistic](../../docs/plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md#situated-generator-and-receiving-composition) | Makes the streaming recurrence `z_(k+1)=T_(u_k,δτ_k;Θ)(z_k)` primary and demotes the confirmed moment `m_g=Σ_k Ĝ_g(τ_g(k))⁻¹E_g(u_k)` to "candidate statistics" that "certify only linear/bilinear subreceivers"; defers the descent to packet 6 with a "retained remainder" | **Corrected in place** by this audit |
| `dc9e518d` | `incident/machine_episode.rs::evaluate_generator_episode` | Runs the full nonlinear incident word `F_Θ` (up to `solve_steps`=128 iterates) once **per source occurrence**; `previous = word.output` feeds the next occurrence; `GeneratorEpisodeTape.prefix` retains every occurrence's `IncidentWord`, including its `steps: Vec<IncidentStep>`, until observe or release; `pull_back` walks that tape in reverse; rest tag `HNA-INCIDENT-FIELD\x02` serializes and reconstructs it. Its record states: *"No nonlinear source-history descent or constant pending-tape size is claimed."* | **Removal is the next campaign's first return** |
| `dc9e518d` | `machine_source.rs::MachineSourceMaps` | `q_k⁺ = U_step(q_k) + I E(u_k)`: advance by the generator's declared action, inject the encoded increment | **Correct**: this is the per-step form of the moment; unrolled without the interposed `F_Θ` it *is* `m_g` |
| `ea758131` | amplitude contract | "retain coefficient error and amplitude history, and preserve old comparison cuts through restart" | Amplitude history removed in `1aa2d6d4`; frozen cuts remain |
| `1aa2d6d4` | `operative/factor_return.rs` | Omits `returns.push` on the source-only, rank-0, no-append path | **Correct but partial**: the journal remains on every other path; `NativeConstitutiveField.history: Vec<HeldField>` and `OperativeState.recent_producers` remain |
| `1aa2d6d4` | `operative/source/action/contact_amplitude.rs`, `Transport/ContactFactorScale.lean` | Positive `rho` from one fixed template, `D_a=rho_a B_a`; no ledger | **Correct**: the retained object is the current parameter |
| `1aa2d6d4` | `Transport/ContactAmplitudeState.lean` | `Machine.run := List.foldl step`; `completedStanding : StandingLaw Update Generator (List Update) State Face` instantiates the standing law with the **update history as the source type**; every theorem discharges by `rw [h]` | **Do not cite as the standing counterpart of pair material.** It proves that a fold's result suffices for the fold's future; it contains no pair, phase, receiver or Holonic operand. The obligation it stands in for is the standing binding of #17, still owed |
| `1aa2d6d4` guides | `CLAUDE.md`, `AGENTS.md`, `THE_MACHINE.md`, `HNN_FORMULA.md`, `HNN_COMPOSITION.md` | Describe the tape, cohort statistics and frozen producing cuts as the contract ("Live comparison tapes remain temporary…", "frozen producing cuts remain attached through delayed returns", "rest preserve old producing cuts") | **Corrected** in the two guides and the state by this audit |

[established-bounded; measured] Cost of the tape as implemented: a pending comparison on a
source of `N` cells over `S` sites retains `N` incident words, each with up to `solve_steps`
site-step sections, plus `N` injections, until the comparison is observed or released, and
serializes all of it at rest. The 6-cycle control in the
[material return](2026-09-22_PAIR_MATERIAL_LEARNS_WITHOUT_A_COMPLETED_UPDATE_ARCHIVE.md)
reports the field rest at 6,830 bytes; the pending tape is not in that number. Its joint
radius grew from zero to about 0.0612 across six cycles and the output was 0/6 target strings.

## What the machine's law says instead

[definition] The source passage enters as **phase-carried helical moments** on a fixed
machine ([HOLON](../../docs/HOLON.md#the-helical-pair-interaction-unit),
[formula](../../docs/HNN_FORMULA.md), confirmed by Brandon on September 21):

```text
m_g(n)   = Σ_(k<n) Ĝ_g(τ_g(k))⁻¹ E_g(u_k)          phase carries order; state is O(generators)
m_g(n+1) = m_g(n) + Ĝ_g(τ_g(n))⁻¹ E_g(u_n)          one accumulation per occurrence, no interposed word
C_gh(δ)  = Σ_k v_g(k) ⊗ v_h(k+δ)*,  v_g(k)=Ĝ_g(τ_g(k))E_g(u_k)     oriented pair moments at admitted offsets
(q,b)    = F_Θ(q₀ + I m, b₀; c)                     the nonlinear word acts once on the joint field
y_j      = ρ_R(Ĝ_R(τ_R(j)) q)                       a response position is a receiving phase
```

The adjoint of the accumulation is `E_g* Ĝ_g(τ_g(k))⁻*` applied to **one** covector for each
`k`: no intermediate state is needed, so no tape exists to retain. The source's contribution to
the paired adjoint is the moment and the phase, both already resident. "Resident state and cost
independent of source length" (packet 6) is then a property of the construction, not a deferred
economy task. Reading `n` cells still costs `n` cell accesses and `n` phase transports; that is
ingestion, not retention.

[definition] Directed source contacts (`machine_source_contacts.rs`) are a linear map from the
encoded rows to condition ports; they compose with the same accumulation and need no tape.
Contact multiplicity and orientation are carried by the map, not by a replay.

[definition] An outstanding comparison owns its **producing operands**: the moment `m`, the
phases at which the source and response were read, the receiving covector and the current
material at which the paired adjoint is evaluated. It does not own a replayable cut of every
earlier material version. A comparison that arrives after a material update is read through
the **contemporary** standing, with its residual returned at the receiver; that is what
`Foundation/Standing.lean::the_unretained_receiver_is_reconstructed_confidently_and_wrongly`
already allows for and what `contact_amplitude.rs` already does for `rho` ("an older comparison
supplies `G_old`; its relative gradient is evaluated against the contemporary basis"). The same
rule applies to E/M/R and stop material. Frozen producing cuts are the "stored record" the
canon excludes.

[definition] Where a nonlinear receiving operation does not factor through the moment, the
law is to **retain the separating direction or the source-qualified remainder**
(`D E=ρ`, `E_next T=U E`, otherwise the defect) — a direction in the moment fibre, not a
transcript. The plural fibre `[a,b]`/`[b,a]` under identity phases is resolved by the oriented
cross moment `C_gh(1)`, which the plan already names; it is not a reason to keep the tape.

## Consequence for the next campaign

[project-postulate; agent-inferred] The next completed return on the generator machine is the
**removal** of the per-occurrence nonlinear recurrence, not an addition beside it:

1. `machine_episode.rs`: accumulate `m_g` and the declared oriented offsets through
   `MachineSourceMaps` alone; run the incident word once on `(q₀ + I m, b₀; c)`; `pull_back`
   returns the source covector by the transposed accumulation. `GeneratorEpisodeTape.prefix`
   and `steps` retention for pending comparisons go away; rest stores the moment, phases and
   binding. The existing episode tests keep their directional-return and restart checks with
   the tape replaced by the moment.
2. Pending comparisons hold `(m, phases, covector, material cut id)`; a comparison observed
   after an update evaluates against the contemporary material and returns its residual, as the
   amplitude path already does. `recent_producers` and the frozen-cut replay in
   `incident/rest.rs` are retired with it.
3. `operative/factor_return.rs`: the `returns` journal is omitted on every current-only path,
   not only the rank-0 source-only one; `NativeConstitutiveField.history` is bounded to the
   pending set.
4. `Transport/ContactAmplitudeState.lean` is not the formal counterpart of #17's standing
   binding; the counterpart is a `StandingLaw` whose source type is the machine's
   `(phase, winding, m, q, b)` chart and whose `retain` is the declared quotient, with the
   source-fibre separator as its defect. That obligation is recorded in #62.
5. Cost is measured as resident state versus source length before and after; the packet 6 claim
   becomes a measurement, not a promise.

Geometry/clock inference, compatible closure, dormant-mode standing and the inspected episode
criteria keep their existing owners and issues (#17/#18/#49/#61/#62/#16).

## What was not wrong

[established-bounded; source-inspected] `Foundation/Standing.lean`, `standing.rs`,
`receiver_release.rs` and the July canon state retention correctly; `holonics-hna` does not
consume them yet. The pair-contact and serial owners (`1e0c2375`), the fixed machine with its
affine current charts (`6cd41cdd`), the per-step advance/inject maps, the positive fixed-template
amplitude law, the omitted amplitude ledger, the joint-ball enclosure laws and the tagged phase
receiver are consistent with the machine and are kept.

## Verification

[established-bounded; process-audit] No runtime source changed. Guides, plan section and state
were edited in place; local Markdown targets and `git diff --check` were run. Existing native
and Framework receipts at `3068758e` are reused unchanged.
