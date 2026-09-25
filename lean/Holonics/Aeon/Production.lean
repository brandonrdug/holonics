import Holonics.Aeon.Production.HodgeTime
import Holonics.Aeon.Production.Kac
import Holonics.Aeon.Production.PathReversal
import Holonics.Aeon.Production.Zeta
import Holonics.Aeon.Production.FirstLaw

/-!
# Production: the kinds of time an aeon carries, its arrow, its cycles and the first law

[definition] Aeon record
`research/records/2026-09-24_THE_AEON_EPOCH_AND_CYCLE_STANDARDIZE_THE_PASSAGE_OF_TIME.md`,
sections A2 and A4–A8, Lean obligations 3–6. An aeon is a stretch of motion between two
occurrences; a receiver's clock reads it; an epoch is a division of it at a receiver's section;
a cycle is an aeon that closes. This root gathers the finite, exact owners of what those readings
split into and what they conserve or produce.

* `HodgeTime` (A2, obligation 3). A time form splits into state time (exact, read by the bounding
  occurrences), winding time (harmonic, a cycle invariant) and production time (coexact, the
  curvature `d₁ω`): `boundary_determined_iff_exact`, `winding_reading_homology_invariant`,
  `production_is_curvature`. On a matching parametric complex the groupoid's aeons and clocks are
  read here, and a clock is exactly a time form with no production time
  (`wordReading_eq_timeReading`, `clock_production_zero`, `isClosed_iff_production_zero`).
* `Kac` (A4, obligation 4). Kac's ledger at every truncation, Kac's lemma for observables and for
  one state, the grain ratio as the undivided pair `(π(S) : π(A))`, existence under
  irreducibility, `Σ_n P_x(τ_x > n) = 1/π x`, and Abramov's formula for the induced chain: the
  entropy of the coarse epoch's word by the chain rule, the exact ledger at every truncation, and
  `h(T_A) = h(T)/μ(A)` in the limit (`kac_ledger`, `kac_observable`, `kac_hasSum`,
  `wordEntropy_succ`, `abramov_ledger`, `abramov`); a reducible counterexample.
* `PathReversal` (A5, A6, A9, obligation 4). Over exact rational chains, logarithms read in `ℝ`:
  `σₙ = D(P_γ‖P_(Rγ)) ≥ 0`, `σₙ = n σ`, `σ = (ln 2/2) Σ edgeCodeProduction`,
  `σₙ = 0 ⇔ detailed balance`, the state plus heat split of the path log-ratio as a reading of the
  affinity clock along the path aeon, detailed balance ⇔ self-adjoint in `ℓ²(π)` ⇒ real spectrum,
  and Kac's coarse ticks as the reading of a section's arrival clock; the biased rotation as
  counterexample.
* `Zeta` (A8, obligation 5). Jacobi's formula,
  `d/dT det(1−TM) = −det(1−TM) Σ_k tr(Mᵏ⁺¹)Tᵏ`, `exp(Σ tr(Mⁿ)Tⁿ/n) · det(1−TM) = 1`, the
  machine's transfer determinant as its reciprocal zeta, the Perron growth bound, and the cycle
  count of a map as its number of periodic points (`trace_pow_mapMatrix`).
* `FirstLaw` (A7, obligation 6). `ΔC = exchange + deposition` per epoch and along an aeon, the
  cycle balance, path dependence, the continuous and integral forms, heat and work in the
  canonical chart, and the deposition between the canonical receivers of a constitution and its
  deposit as work on the reached edges plus the log-partition shift.

[open] Owed in #62: `h = log ρ(M)` as an equality, the radius of convergence of `ζ` and its first
pole at `e^(−h)` (these need Perron–Frobenius); Abramov's formula for general ergodic maps, and the
identification of the induced shift's Kolmogorov–Sinai entropy with the per-word entropy proved
here; the converse of Kolmogorov's criterion (zero cycle affinities ⇒ detailed balance); the
continuum Hodge theorem; the record's agent-inferred reading of relative completeness as exact
reading. `PositiveCellHodge` lives only
in `HolonicsResearch` (`Physics/HolonicDiscreteMaxwellOperator`) and is not joined here.
-/
