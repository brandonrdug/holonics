# The mirrored chart is bounded by its residual, and counting its norm raises the held-out code

October 2. Refs #73, #62. Lean `HNN/LatticeWord` §8; the campaign-1 read is on #215.

## 1. The law

The constitution's solved chart forms only the upper triangle and mirrors it. The mirror carries
the transpose of the residual's rounding, and `XH ≈ 1` no longer absorbs that transpose, so the
rounding term grows with the chart's own norm:

```text
‖1 − X″H‖∞ ≤ δ² + n 2^(−L−1)(1 + 2‖X‖∞)‖H‖∞                          (solved_refinement_certificate)
```

The Gram's margin bounds that norm by the residual, with no inverse formed. Column `j` of a
symmetric chart solves `Hx = ((XH)ᵀ)_j`, whose ℓ1 is at most `1 + ‖1 − XH‖∞`. The margin bounds
`|x|`, and `‖x‖₁ ≤ √n|x|`:

```text
c₀|v|² ≤ vᵀHv ∀v ,  n(1 + ‖1 − XH‖∞)² ≤ c₀²ρ²   ⇒   ‖X‖∞ ≤ ρ          (chart_rowNorm_le_of_margin)
```

At the carried Gram's margin `c₀ ≥ 1/2` and a residual of at most `1/2`, `‖X‖∞ ≤ 3√n`. Hence the
lattice

```text
L = D + ⌈log₂ n⌉ + ⌈log₂ ‖H‖∞⌉ + k_n ,   k_n least with 36n ≤ (2^k − 1)²
```

keeps every certificate at most `2^(−D)` through the executed refinement
(`solved_chart_lattice_stays`). The bound holds at every iterate, not only at the solve.

## 2. Campaign 1 with the executed chart rule counting `k_n` (#215)

#215 made `ChartRule` count `k_n`. Campaign 1 was read on that branch and on main, both with the
exact host reference over all 3,074 windows. Readings are a carry plus `k/16` plus `ε`.

| | main | #215 | #215 − main |
|---|---|---|---|
| held-out model − PPM-2 (1,190 targets) | `−560 + 15/16 + ε` | `−559 + 2/16 + ε` | model code in `(3/16, 13/64)` bits |
| training (4,958 targets) | | | model code in `(−7/32, −27/128)` bits |
| Newton–Schulz steps | 11,400 | 11,395 | |
| wall time (exterior) | 1,350,803 ms | 1,358,566 ms | |
| peak resident set | 235,503,616 bytes | 246,562,816 bytes | |

The two runs differ only in the chart and remainder readings. Counting `k_n` lowers the training
code length and raises the held-out one. [agent-inferred] That is a fit to the training targets,
not a law that carries, so the executed chart rule does not count `k_n`. #215's Rust change is
left unmerged.

## 3. What stands

The law in §1 stands without the behaviour change. Without `k_n`, the executed lattice no longer
guarantees the certificate in advance; the chart still reads its residual at each deposit
(`ChartReading`). A width or Gram at which that read rises above `2^(−D)` is the measurement that
would make the count needed.
