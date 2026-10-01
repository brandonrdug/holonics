# The forced release: every decision along the right trajectory, the best agreement, and a cost that was the derivative, not the covectors

**Date.** October 1. **Issues.** #73, #76, #63 (THE_REBUILD U6, step 1). **Grade.** [definition;
agent-inferred] for §1; [measured] for §2 and §3. Receipts in
[`2026-10-01_THE_COMPARISONS_AGREEMENT_receipts/`](2026-10-01_THE_COMPARISONS_AGREEMENT_receipts/).

## 1. The reading

The release decides in a cascade. A changed early lock moves every later decision's context, so no
comparison read in the release's actual contexts tracks its decisions between neighbouring states
([agreement](2026-10-01_THE_COMPARISONS_AGREEMENT_WITH_THE_DECISIONS.md), §4).

**The forced release** (`prediction::bank_release_forced`) runs the release's own lock iteration
under its own law: which stations lock comes from their own readings and the largest gap. Each lock
is placed at its target class instead of its top, so its refinements are the contexts the release
would read had every earlier lock been right.
- **`Reading::Forced`** reads every open station of every forced refinement. With the order term
  (`order-forced`) it covers every decision along the right trajectory, so if every term is solved
  the section is whole, lock by lock. It never reads a context with a wrong placed cell.
- **`Reading::ForcedDecisions`** reads each station once, at the forced refinement that locks it,
  with the order at the first refinement.

A placed target is a reading context, not a commit, so its Floquet certificate is not read. The
release itself, its sections and receipts, stays the release's own. Tests:
`the_forced_release_reads_every_decision_along_the_right_trajectory`, plus the forced arms in the
guard test (hnn 245 passed).

## 2. Agreement with the decisions (12 saved states)

| Comparison | All pairs, agree to disagree | Neighbouring moves, agree to disagree |
|---|---|---|
| `order-forced` | **43 to 15** | 5 to 3 |
| `order-fdec` | 40 to 18 | 4 to 4 |
| (for reference) `order-dec`, `lock-all`, `lock-tf` | 40 to 18, 40 to 18, 38 to 20 | 4 to 4, 5 to 3, 5 to 3 |

The forced release has the best agreement over all pairs, but between neighbours no comparison
separates from the others on 8 changing moves.

At the founded opening the forced comparison's slope in `ρ` is positive (`γ_ρ ∈ [2384414/4096, …)`):
it asks for the lower transport, toward the refit's `ρ*`. Under the lock face at the decisions the
same slope is negative there. This is the first comparison read whose `ρ` direction at the opening
agrees with the refit (`forced-incumbent-cost/`).

## 3. ~~Its move does not fit the host~~ Its cost was the exact derivative in `ρ`

One read of the forced comparison with every covector took 649,026 ms at the opening, and two guarded
witness moves under `order-forced` were incomplete: the first at 984 s, the second at 1,141 s. Neither
was relaunched with a larger limit.

~~The blocker is the covector cost on the host's exact arithmetic; the bank's turn covector needs its
device realization (#76).~~ **Corrected the same day, by measurement.** The read split as follows:
- the incumbent with every covector: **28,739 ms**;
- the proposal: 1,212 ms;
- the modulus's slope split: **603,039 ms**. These are the exact storage derivatives in `ρ`
  (`BankPlacement::modulus_derivative`), each entry carrying the transported mass's denominators,
  read anew by every consumer.

Two repairs followed:
- the sections' derivatives are read once a proposal and shared (`section_derivatives`), which gave
  579,754 ms;
- the derivative is held at 192 significant bits toward zero (`DERIVATIVE_BITS`, above every
  consumer's own grain), which gave **39,388 ms**, with `γ_ρ` unchanged at its printed grain.

The 15-fold speedup applies to every arm's moves, not only the forced one. The covectors were never
the blocker, so no device port is needed for this objective.
