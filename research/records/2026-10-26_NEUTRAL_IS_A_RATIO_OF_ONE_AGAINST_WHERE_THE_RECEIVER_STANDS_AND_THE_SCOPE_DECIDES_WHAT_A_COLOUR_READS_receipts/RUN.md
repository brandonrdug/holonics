# Receipt: neutral is a ratio of one, and the scope decides what a colour reads

The record is
[neutral is a ratio of one against where the receiver stands](../2026-10-26_NEUTRAL_IS_A_RATIO_OF_ONE_AGAINST_WHERE_THE_RECEIVER_STANDS_AND_THE_SCOPE_DECIDES_WHAT_A_COLOUR_READS.md).

## What runs

`neutral_scope.py` is self-contained. It uses only Python's standard library and integers: elements
of `ℚ(ζ_n)` are integer polynomials reduced modulo `Φ_n`, which is built by exact division of
`xⁿ − 1`. It reads no data, private or public, and builds no float.

Parts and what each checks:
- **S.** Every subgroup `H` of `(ℤ/n)ˣ` for `3 ≤ n ≤ 200`, built as products of cyclic subgroups
  (3,866 pairs `(n, H)`). For each:
  - the reading `Tr_H(ζ_n) = Σ_(h∈H) ζ_n^h`, and that every `h ∈ H` fixes it;
  - compression in stages: for `H ⊆ H′`, `Tr_(H′)` against the sum over coset representatives of
    `H′/H` of the conjugates of `Tr_H`;
  - the reading to `ℚ` against `μ(n)`;
  - that the reading is `0` exactly when `H` contains the kernel of `(ℤ/n)ˣ → (ℤ/(n/p))ˣ` for some
    `p` with `p² ∣ n`;
  - the kind of each reading: neutral, real (fixed by conjugation) or with a turning part.

  The twelfth-turn table: `ζ + ζ⁵ = ζ³ = i`, `(ζ + ζ¹¹)² = 3` with `ζ + ζ¹¹` real, `ζ + ζ⁷ = 0`,
  and the sum of all four colours `0`.
- **F.** For `n ≤ 400`, every prime `p ∣ n` and every primitive colour `j`, the fibre
  `{j + k·n/p : k < p}`: when `p² ∣ n` every member is a unit and the fibre's colours cancel exactly
  (16,224 fibres); when `p` divides `n` once the fibre holds exactly one non-unit.
- **M.** `μ(p n) = −μ(n)` for every `n ≤ 5000` and prime `p ≤ 100` with `p ∤ n` (115,996 pairs).

The last line is `all 300536 checks hold`.

## Command, projection and measured run

```bash
cd research/records/2026-10-26_NEUTRAL_IS_A_RATIO_OF_ONE_AGAINST_WHERE_THE_RECEIVER_STANDS_AND_THE_SCOPE_DECIDES_WHAT_A_COLOUR_READS_receipts
timeout 60 python3 -I neutral_scope.py > neutral_scope.txt
```

- **Projection.** About 14 s, from a development run of 13,084 ms at the committed bounds (earlier
  development runs: 2,082 ms at `n ≤ 40`, 2,395 ms at `n ≤ 80`, 3,618 ms at `n ≤ 120`). The deadline
  is 60 s, fixed by an outer `timeout`.
- **Measured.** The committed output came from that command, run through a `runpy` wrapper that reads
  `resource.getrusage`. Wall time was 12,778 ms, with a peak resident set of 12,052 KiB on one
  thread; the script's own clock read 12,769 ms. Measured over the deadline: 12,778/60,000.

| File | SHA-256 |
|---|---|
| `neutral_scope.py` | `309fc975c26371d1a122f0d3d759fd9ff9882df9546a42429d4c39b558bd3301` |
| `neutral_scope.txt` | `c0186b3d34a1fb28ecd577deff0e439d9947fcc8d677f0b1c6e283c6ead247ff` |

The output's hash changes with the elapsed time printed on its last line; every other line is
deterministic.

## Development notes

- The neutral criterion was a guess before the first run, from the fibre cancellation; the first run
  at `n ≤ 40` found it exact on all 277 pairs, and it was kept as a check at the committed bound.
- A first version listed the primes for part M with a floating square root; it now uses `isqrt`.
