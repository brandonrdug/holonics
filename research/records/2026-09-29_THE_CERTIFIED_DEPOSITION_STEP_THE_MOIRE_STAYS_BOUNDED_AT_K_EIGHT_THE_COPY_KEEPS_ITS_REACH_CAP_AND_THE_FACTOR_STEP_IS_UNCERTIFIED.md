# The certified deposition step: the moiré stays bounded at K = 8, the copy keeps its reach cap, and the factor step is uncertified

**Date.** September 29. **Issues.** #73, #63 (THE_REBUILD U6). **Grade.** [measured] for the runs
(§4), each run once under the [pins](2026-09-29_THE_CERTIFIED_DEPOSITION_STEP_PINNED_BEFORE_ITS_RUNS.md)
(`14ba69f5`); [proved-derived; formal-checked] for the Lean statements (§2); [agent-inferred] for
the choices named as such.

## 1. The lessons it answers, and what was retired

The [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **Failure 5, the uncertified deposition gain.** Every linear locus's step is now certified from
  its own covector, curvature and reach. The factor families' step is still declared, and on text it
  carried the standing past the pinned bound (§4). The failure is answered for the linear loci and
  **open for the factor families**.
- **Failure 8, the prox step's reach cap.** Measured on the copy and **not removed**. Its cause is
  named in §5 and is not tuned around.
- **Failure 9, a refusal answered with a larger limit.** No run was repeated and no bound was
  raised. The pinned entry bound failed on text, and it is reported as failed. The storage search
  and the certificate's bounds were fixed before any run.

**Retired** (`2dcbd5e2`: 2,459 lines deleted, 250 written):
- the count-priced founding and the founded machine (`hnn::encoding` −886, its tests −499,
  `hnn::field` −331);
- the priced birth in `receiver::population::merge` (−83, tests −38);
- the founded `E_0`: `E_0` is the declared sign sequence again;
- the keyed latent's pseudo-random signs (`hnn::prediction` −91);
- the harnesses' founding paths (−194 and −108).

The record-only contact growth is replaced by the enforced storage certificate (§3). Kept: the
Encoding/Closure algebra on declared transports, the passage chart's Lean, the window-free moment
and its tape-free covector, the continuing word and its exact adjoint, release at width zero, and
`hnn::keys`.

## 2. The step's certificate

A linear locus (`E_g`, `R`, `W_c`) prepares its unit step through the solved chart of its carried
Gram (`NormalLaw::prepare`):

```text
D = Σ_t w g_t (X̂ f_t)ᵀ,   a = Σ_t w⟨g_t, D f_t⟩ (checked; a < 0 refused),   b = Σ_t w|D f_t|²,   c = max_t |w g_t|_∞
C = B · ½ · κ² · b        B the linear loci stepping together, κ² the reach gain
η = the largest 2^k with ηC ≤ a and ηc ≤ 1, halved until every certificate holds at every ray's end
```

`κ²` is read from the deposit's reach and the medium's energy law:
- `R`: `κ² = 1`;
- `E_g`: `κ² = d‖R‖²(Y_g/Y_R)Σ_j(Σ_(T_n ≤ T_j)(1+ω)^(T_j−T_n))²`;
- `W_c,r`: `κ² = ‖R‖²(Y_r/Y_R)Σ_jΣ_(τ<T_j)(1+ω)^(2(T_j−τ−1))`.

Here `‖R‖²` is the Schur bound at the ray's end and `ω` is the contrast ports' certified bound. The
step reads no codec, alphabet, chart or terrain, so the same `Constitution::deposited` ran on the
moiré, the copy, text and the standing cut (§4).

The Lean statements, with their `#print axioms` in the framework audits:
- `Holon/Deposition` §6:
  - `quadratic_upper_model`: slope `−a`, curvature `≤ C` on `[0, η]` gives
    `φ(η) ≤ φ(0) − ηa + ½η²C`;
  - `certified_step_descends`: the joint model with `η_ℓC_ℓ ≤ a_ℓ` gives
    `φ ≤ φ₀ − ½Ση_ℓa_ℓ`;
  - `joint_cauchy_schwarz` and `gauss_newton_curvature`: `s‖ΣA_ℓu_ℓ‖² ≤ |B|sκ²Σ‖u_ℓ‖²`;
  - `active_element_growth`: `‖s′‖ ≤ ‖b‖ + ωc`;
  - `active_energy_growth`: `‖s′‖² ≤ (1+ω)²r²` and `‖s′‖² − ‖b‖² ≤ (2ω+ω²)r²`.
- `HNN/Normal` §7, `certified_normal_step`: the deposit at `η` is `W + ηD` with
  `D = (Σ w g fᵀ)H′⁻¹`, and `a` is the solved chart's quadratic form on the rows of the window
  covector (`window_alignment_eq`, `frobenius_chart`). So `a ≥ 0` at a positive semidefinite
  invertible carried Gram (`inv_psd`).

## 3. The energy enforcement

- **Storage.** At every deposit the storage it changes is certified `Q_(k+1) ⪯ (1 + ε_k)Q_k` by
  exact inertia before anything is published. That covers every contact's `C_a, K_a` and every
  unpumped resonator's `C, K`. The growth `ε_k` is searched over `{0} ∪ {2^k : −20 ≤ k ≤ 40}`, fixed
  before the runs. A deposit that no `ε_k` certifies is refused (`UncertifiedStorage`) and every
  published state is kept.
- **The contrast port.** It is active whenever `W_c ≠ 0` (Lean `HNN/Word.contrastPort_active`), so
  it is not projected. It enters as the per-tick growth `(1+ω)²`.
- **`E` and `R`.** `E` scales the injection and `R` does no work on the field; both gains enter
  `κ²`.
- **Pumped resonators.** A pumped resonator has no certified growth, so a linear step through it is
  refused (`UncertifiedGain`). The GPU suite's pumped test now reads that every published deposit
  there stepped no linear locus.
- **The check.** Each refinement's committed energy is checked at its commit against
  `(1+ε_k)(Σ_n g^(Kw−nw)√P_inj + g^(Kw)√((Kw+1)r))²`, with `g = 1 + ω`.

[measured] **The bound holds, but it is loose.** The storage certificate refuses only growth beyond
`2⁴⁰` in one deposit, or growth that is not relatively finite. It does not bound the rate. The factor families' declared step `η_x`
moves the rank-deficient `C = c cᵀ` and `K = b bᵀ` by large relative amounts in their weak
directions: one text deposit certified `ε_k = 2²⁸`. The product `∏(1+ε_k)` reached:
- between `2²⁷⁴` and `2²⁷⁵` over text's 25 deposits;
- between `2¹⁵⁴` and `2¹⁵⁵` over the exposure's 3,072.

## 4. The runs

Each process ran once, on the host, in release, bounded at 600,000 ms, with training bounded at
540,000 ms. The GPU was idle.

**The moiré at `K = 4` and `K = 8` (acceptance 1): passes.** The pinned moiré had 512 training
windows, batch 16, and 6 evaluated windows. Those windows are its training windows, so the
evaluation reads stability, not transfer.

| `K` | Checks (balances, pairings, commits / unreached) | Energy bound | Largest entry | Exact | `k` at `E` / `R` / elements | `∏(1+ε_k)` | Training, peak |
|---|---|---|---|---|---|---|---|
| 4 | 512 of 512 each / 32 of 32 (64 loci) | 512 of 512 | `R` 565/256 | 6 of 6 (48 of 48 stations) | −16..−15 / −1..2 / −12..−10 | `3²⁰·5⁵·11²·17¹¹/2⁸³` (4672 rem …) | 207,863 ms, 515,977,216 bytes |
| 8 | 512 of 512 each / 32 of 32 (0 loci: the diamond covers the field) | 512 of 512 | `R` 2975/2048 | 6 of 6 (48 of 48) | −16..−15 / −2..1 / −13..−10 | `2¹³·3¹¹·5` | 375,801 ms, 623,980,544 bytes |

`E`'s largest entry stayed within `[1/2, 1/2 + 1/1024)` at both depths (`K = 4`: 262417/524288;
`K = 8`: 1049503/2097152). Under `γ_U = 1` it grew 1, 6, 26, 316. The development configuration
that diverged (`d = 16`, `K = 4`, batch 8, 128 windows, development seeds) read again:
- every check held, and the energy bound held 128 of 128;
- `E` stayed in `[1/2, 1/2 + 1/1024)` over the first eight deposits, and `R` reached 2071/1024;
- 6 of 6 exact, in 18,446 ms.

**The copy (acceptance 2): 237 of 256 exact, against 234 under `γ_U = 1`.**
- Stations: 2,020 of 2,048, against 2,026.
- Every check held, and the energy bound held 1,536 of 1,536.
- Largest entry: `R` 1571/512.
- Certified steps: `R` `2⁰..2¹`, `E` `2⁻¹⁴..2⁻¹²`, the element `2⁻¹¹..2⁻⁹`.
- `∏(1+ε_k) = 3⁹³·5¹⁴·11²·17²⁴/2²⁵⁸` (127549086 rem …).
- 449,009 ms training, peak 376,311,808 bytes.

The cap is not removed.

**The standing cut's exposure (acceptance 3): not parity; the named change is the step.** The run
read the residue chart on the host, 3,074 windows (sha256 `39621d52…7fbc`):

| Reading | `γ_U = 1` (the attribution run) | The certified step |
|---|---|---|
| held out, the field's face | `5459 + 13/16 + ε` | `5462 + 4/16 + ε` |
| held out, the tree alone | `5476 + 3/16 + ε` | `5476 + 3/16 + ε` |
| held out, the field's part | `−17 + 10/16 + ε` | `−14 + 1/16 + ε` |
| development, the field's face | `13069 + 5/16 + ε` | `13068 + 7/16 + ε` |
| `Kt` | `19992 + 3/16 + ε` | `19991 + 12/16 + ε` |

- The held-out code is longer by more than `2 + 6/16` and less than `2 + 8/16` bits.
- The development code is shorter by more than `13/16` and less than `15/16` bits.
- The one change on this path is the step. The retirements touched only the founded chart's
  readers.
- The certified steps rose above the retired `2⁰` where the covector reaching a locus was small,
  and fell far below it elsewhere:
  - the source port `2⁻¹⁰..2⁴`;
  - the four contrast ports `2⁻⁸..2⁹` and `2⁻⁸..2¹⁰`;
  - `R` `2⁰..2²`.
- 9,222 tick balances and 3,074 word balances closed. There were 6 aeon boundaries and 4 key
  locations.
- `ε_k` ranged over `0..1/2`.
- 525,991 ms, peak 413,290,496 bytes.

**Text, training only (acceptance 4): fails the pinned entry bound.** The run read the choosing
role's 385 pairs in one pass (sha256 `c6e51a35…0816`), 25 deposits:
- every check held (385 of 385 each; 25 of 25 unreached, 175 loci), and the energy bound held
  385 of 385;
- the standing `q₁` reached `8709/1024 = 8 + 517/1024`, above the pinned `8`;
- one deposit certified `ε_k = 2²⁸`;
- the training sections coded `97342 + 10/16 + ε` bits over 12,320 stations;
- certified steps: `E` `2⁻¹⁸..2⁻¹³`, `R` `2⁰`, the element `2⁻¹⁵..2⁻¹⁰`;
- 214,060 ms, peak 706,969,600 bytes.

No text was generated. The same deposit code ran on all four fields, so the step itself is
modality-general. The failure is the factor families' uncertified step.

**Time.** Every run finished within its pinned bound but above its projection:
- the moiré by factors in `[4/3, 3/2]`;
- the copy by `[6/5, 5/4]`;
- text by a factor just above `2`;
- the exposure above its upper projection of 430,000 ms.

The development reads were too short to show the cost growth over a run.

**Gates.**
- `cargo check --workspace --all-targets` is clean.
- `cargo test -p holonics --lib`: 919 passed.
- The GPU suite: 32 passed, alone on the idle card under the lock, after one test's assertion was
  corrected to the law (a published deposit through the pumped resonator steps no linear locus).
- `bash tools/lean_check.sh Holonics HolonicsResearch`: built, no `sorry`.

## 5. Verdict

- **Failure 5 is answered for the linear loci.** The step that diverged at `K = 4` is bounded at
  `K = 4` and `K = 8`. Every balance, pairing, commit, unreached locus and energy check holds.
- **It is not answered for the factor families.** Their declared `η_x/h_x` step moved the standing
  past the pinned bound on text. It certified storage growth up to `2²⁸` in one deposit, which
  makes the enforced energy bound loose. The next loop's subject is the factor families' certified
  step, by the same law: first-order decrease, curvature through the word and the lattice's scale,
  with `ε_k` then bounded by the step.
- **The reach cap (failure 8) stays.** Its cause, by measurement: the receiving map's certified
  step never exceeded `2¹` on the copy, because `ηc ≤ 1` caps it where a station's weighted
  covector reaches `½`. The source port and the element stepped at most `2⁻¹²` and `2⁻⁹`. So no
  locus moved more than twice the retired `γ_U = 1`. The prox step's total reach is bounded by the
  growing Gram's `ln det H_T` (September 25 §3), times `η`. A certified `η` bounded by the lattice's
  covector scale cannot lift it. The cap belongs to the Gram's retention (a Gram that only grows),
  not to the step. Lifting it by relaxing `ηc ≤ 1` would raise a limit (failure 9), so it is not
  done.
- **The exposure is not at parity.** The certified step fits the development cells slightly better
  and codes the held-out cells about `2 + 7/16` bits worse.

## 6. Owed in #62

"The certified deposition step" (September 29):
1. The model's second-order terms when the logits are not linear in the step: the bilinear coupling
   of the receiving map with a source port, and a contrast port acting on its own downstream
   contrast.
2. The station score's curvature bound `s = ½`: the base-two softmax's `ln 2(diag p − ppᵀ) ⪯ ½I`
   and the phase part's `q/4 ≤ ¼`.
3. The composition of `active_element_growth` over a word's stations and re-entries into the
   gains `κ²` of `hnn::constitution`.
4. The Floquet growth bound of a pumped resonator. Until it exists, a linear step through one is
   refused.
5. The factor families' certified step (`c_a`, `b_a`, `F_a`, `f`, the slices, `q`).
6. The executed word's deviation from the exact law, which is the lattice word's certificate.
