# The governance law holds on the three-mod-eight stratum, and the certificates are infinite

**Date:** 2026-08-22
**Kind:** component one of the ratified mod-two Birch–Swinnerton-Dyer goal — the
governance matrix with its corank law, **proved family-wise**.  Solo orchestrator work,
one Lean file; the symbolic coset structure (four torsion classes, sixteen cosets, seven
canonical refusals), the seven refusal cascades, and the mod-eight kernel were all
derived and verified exactly (empty solution searches at `p = 3, 11, 19`, zero primitive
mod-eight solutions for the seventh system) before encoding.  **It schedules nothing.**
[`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction
authorities.
**Position under the active plan.** Exterior mathematical material for the mathematics
codec arm of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The Lean line does not couple to the engine, per Brandon's standing ruling.
**Truth grades:** `proved-derived` with `formal-checked` evidence for the five headline
Lean theorems (`#print axioms` → `[propext, Classical.choice, Quot.sound]`, zero
`sorryAx`); `interpretation` for the Selmer/Ш/rank vocabulary, marked.

---

## 1. What was proved

Owner: `ElementaryHolonics/Millennium/StratumDescent.lean` (1,946 lines).  The library
builds at **3,398 jobs**.

**`theGovernanceCorankLawOnTheStratum`** — for **every** prime `p ≡ 3 (mod 8)`:

1. the governance matrix — the diagonal 𝔽₂ matrix of the two governing characters,
   the quarter-turn bit and the two bit — **is the identity** (both characters refuse:
   `−1` and `2` are non-squares mod `p`, by `Congruum.lean`'s invisibility theorems);
2. **and** the descent face of `y² = x³ − p²x` has image exactly the four torsion
   classes `(1,1)`, `(−1,−p)`, `(p,2)`, `(−p,−2p)`
   (`theStratumDescentIsComplete` and `theRealizedFourAreInTheImageOnTheStratum`).

Corank zero, family-wise, with the completed descent as the corank law's content
rather than a declaration — **infinitely many Ш[2]-vanishing certificates in one
theorem**.  Read classically (through exterior Mordell–Weil): every twist on the
stratum has rank zero and trivial `Ш[2]` — the curve-rank sibling of `Congruum.lean`'s
triangle theorem, and the family-wise sibling of the completed descents at five and
thirty-four.

## 2. The mechanism, and why the matrix is not a declaration

The upper bound runs the instanced architecture at a symbolic prime: the support law
(distant primes see even valuations, so slot classes live on `±{1, 2, p, 2p}`), the
sign law, and **seven** canonical coset refusals covering the sixteen-coset quotient —

- **six by `p`-adic infinite descent**: each cleared system (`aC² − pN² = bE²`,
  `aC² + pN² = c₃F²`) cascades to `p ∣ C, E, F, N` through exactly the two character
  lemmas the matrix's entries encode — sums of squares descend (`−1` invisible) and
  doubled squares descend (`2` invisible) — then divides and recurses on `|N|`;
- **one by a family-wise mod-eight refusal**: `p ≡ 3 (mod 8)` fixes the coefficients,
  so a single `ZMod 8` kernel `decide` covers the entire class, closed under the
  halving descent.

The remaining twenty-eight refused classes translate onto the seven canonicals through
the family homomorphism by adding torsion points.  The matrix's two bits are therefore
**the exact inputs the refusals consume**: the corank law is proved by the descent the
characters drive, which is what makes the matrix an instrument rather than a table.
The per-instance completed descents (five, thirty-four) remain its adjudication
fixtures on other strata, where the matrix is singular and the image grows.

## 3. The goal ledger after this deed

| component | state |
|---|---|
| governance linear algebra, family-wise | **proved on the `3 (mod 8)` stratum** — matrix identity ∧ image = torsion, every prime at once |
| Ш[2]-vanishing certificates | **infinite family** (this deed) + two rank-positive instances (five: image 8; thirty-four: image 16) |
| parity | one complete instance (five, both sides), one agreement (one); the stratum adds the even-parity descent side for every `p ≡ 3 (mod 8)` — the analytic side there is the theta census at three, instanced |

## 4. What is owed, with falsifiers

**None scheduled; the roadmap alone schedules.**

| owed | falsifier |
|---|---|
| the sibling stratum `p ≡ 5 (mod 8)`: the minus-two character replaces the two character; the same architecture with one changed refusal pattern | a stratum prime whose descent disagrees with its matrix |
| strata where the matrix is singular (`p ≡ 1 (mod 8)`, composite `n`): the corank law must then produce the *positive*-corank reading, adjudicated by the completed descents | an instance where corank and completed image disagree |
| the general interlocking-primes matrix (composite twists), toward the full Rédei/Monsky object | — |
| the family-wise theta/root-number side for the parity component | a parity disagreement |

## 5. Boundaries

The stratum is `p ≡ 3 (mod 8)` and nothing else is claimed; "Selmer", "Ш" and "rank"
are classical readings carried as `interpretation`; the matrix is defined for
odd-prime twists and its law is proved on this stratum only; nothing about the
Birch–Swinnerton-Dyer conjecture.
