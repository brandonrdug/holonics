# F4: the development-family split and the release gate

**Date:** 2026-09-27. **Scope:** F4 in [THE_REBUILD](../../docs/plans/THE_REBUILD.md#f4-release-campaign-5-into-step-8), #73 and #148. This is the pin **before F4 validation**. The existing curated tail, standing cut and wide cut are development receipts, not this validation.

## The pinned families

The dataset's already declared development partition is divided at its undivided occurrence-family key `(provider, record_group)`. The exterior codec [script](../notebook/hnn_design/development_families.py) canonicalizes that pair as sorted-key compact UTF-8 JSON and reads `SHA-256(seed || NUL || canonical family)` as a big-endian integer. Residue zero modulo five is **validation**; the other four residues are **choosing**. `seed = holonics-f4-development-families-2026-09-27-v1`. The source SHA-256 is `e1001a7ed0dd03c583ab4ef097f3e243b12680daad05911374b8765107f2f8b2`. Of 22,449 development families, 17,984 choose and 4,465 validate. The SHA-256 of the canonical sorted private membership entries is `7693d4ca3220ed492fbacb1ffd635f43f6a46c6d27dbce3645e1a40ce05600be`.

The membership file remains owner-only in `.local/cuts/development-families-f4.json` (directory `0700`, file `0600`). Neither family keys nor source text enter this record. The script inspects only partition labels for nondevelopment records. The evaluation partition is reserved for F5 and remains unread.

**Agent-inferred from the protocol:** a request and a response can be different occurrence families. A validation response's bytes must never deposit into choosing standing. Its declared earlier request may condition the release; a relation to an absent request is unheld. The comparison is chronological at that request's own section, before the recorded response is read. Family membership, rather than a suffix of one mixed stream, fixes the new validation unit.

## F4's pinned consumer and acceptance

The consumer is `receiver::population` conditioned through the declared request→response relation in `receiver::population::admitted`, using `receiver::release` at the stopping section. It must satisfy `P_release(y | request, Θ) = P_scored(y | request, Θ)` including termination. Every emitted face carries its decoder, the producing egg and keys, the causal provenance, its grain and plural fibre; otherwise a typed refusal. The checked square is `D E = ρ` and `E_next T = U E`, or its separator. The helical pair is the request's port meeting the response port; of the winding guide's six objects, F4 touches faces and placement, the tube, and the tower thread, with helix, pair and cell holonomy attached through the egg.

The **charges** are the chosen family's prior/declaration, its request pointer where the relation arrives, every emitted byte and the stopping letter. The **baselines** are the same population's scored conditional face (identity check), the unconditioned byte population, the flat stream, and a request-aware retrieval control that returns the most similar *earlier choosing* request's recorded response. A control with no eligible earlier request refuses. No validation response is available to the releaser or control.

**Acceptance, pinned before validation:**

1. On known-truth deterministic moiré and arithmetic terrain, after locating a future-equivalent key, every released continuation through its declared stopping section equals the terrain's continuation. If a key or decoder cannot be located, the response is a typed refusal.
2. On known-truth stochastic tree terrain, the release's conditional face equals the source's conditional face wherever the source is identified; a sampled stream's code is not judged against its entropy.
3. The release/score equality, the decoder and both squares hold at every emitted face, or the exact separating difference is returned. All emitted text is valid UTF-8. A refusal has its declared cause, not an invented answer.
4. Exactly one passage over validation families is run after choosing is frozen. Thirty-two eligible validation requests, selected by the lowest `SHA-256(seed || NUL || "F4 inspection" || canonical request coordinate)` values before their recorded responses are read, are inspected alongside the request-aware retrieval control. The comparison and every refusal are recorded without revising the release from validation. If fewer than 32 are eligible, inspect all and report the count.
5. A warm response returns within 60 seconds on the declared host (20 GB RAM, one 16 GiB card available). Each full passage is projected against ten minutes, 20 GB RAM and 16 GiB card before running; a failed projection permits only a bounded probe, and cannot satisfy the full-passage gate.

If any condition fails, F4 is a predictor and cannot be called a releasing product. F5's retrospective and restart gates and Brandon's blind evaluation remain separate. This pin does not spend that evaluation partition.
