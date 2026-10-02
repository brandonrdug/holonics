# The code length reads storage growth, and its temperature is the periods it reads

**Date:** 2026-10-02. **Refs:** #62, #73, #63.
**Grade:** [proved-derived] for §1–§4 from existing owners; the many-period bound and its limit
are formal-checked (`HNN/ExecutedComparison.lockFace_periods_hinge`,
`lockFace_per_period_tendsto`); the composed storage law of §2 is [proved-standard] in prose and
its Lean statement is owed in #62.

## 0. The question

Astra's review (October 2) found that the released jump in code length was being called an energy
without a map from the cross-entropy over the requests to the Holons' storage and work. At fixed
temperature Astra supplied one special case: the change in code length is the force less its
average. Brandon asked why the temperature is fixed. This record derives the map from the chain's
own owners, states what it cannot be, and answers what fixes the temperature.

## 1. What the code length reads

The release decides each station by its candidates' executed growths
(`hnn::executed::lock_face`, `hnn::ring::ReceivingBank::read_turn`). Candidate `x` reads
`a_x = max_m ρ(M_(x,m))`, the spectral radius of member `m`'s monodromy over one turn of the
passage: the product of the executed tick maps over `schedule.period()` crossings, each the
member's material with its stiffness pumped by the passing carrier, `K_t = K − 2pR(a² s^t z_t)`
(atlas `parametron.passage-monodromy`). The lock face of a station with target `t` is

```text
ℓ = log(Π/a_t),   Π = 1 + Σ_x a_x,   θ_x = a_x/Π,
```

the resting sheet (the lossless ring's return, multiplier 1) holding weight 1. The released code
length is the sum of the stations' `ℓ` over the requests (atlas `hnn.lock-face-comparison`).

## 2. The map to storage and work

**Per period.** One tick changes the member's stored energy by the pump's work less the
dissipation (`HNN/Word.word_tick_balance`; for the loaded resonator
`HNN/Ring.loaded_tick_port_balance`). The pump is a periodic change of the stiffness at fixed
displacement, and a change of constitution at a fixed state changes the storage by exactly
`½⟨x, ΔΘ x⟩` (`HNN/Word.field_commit_deposition`): that is the pump's work per tick. Chained over
`n` turns from a state `x`, with `P` the member's stored energy read at the turn's opening in the
unpumped material (positive definite, `C, K ≻ 0`) and the pump's work counting every stiffness step
of the turn,

```text
P(Mⁿx) − P(x) = W_n(x) − D_n(x),
```

the pump work less the dissipation over the `n` turns.

**The multiplier is the growth rate of that storage.** Gelfand's formula on the member's energy
norm gives `ρ(M) = lim_n ‖Mⁿ‖_P^(1/n)`, and `‖Mⁿ‖_P² = max_x P(Mⁿx)/P(x)`. With
`w_n = max_x (W_n − D_n)/P(x)`, the net work per stored energy over `n` turns on the most-amplified
state,

```text
a_x² = lim_n (1 + w_n)^(1/n),   κ_x := log a_x = ½ · (the storage's growth exponent per turn).
```

The turn's certificate states the same per turn in its own metric: `G ≻ 0` with `MᵀGM ⪯ ρ²G`
(atlas `parametron.floquet-decision`) bounds every state's storage gain per turn in `G` by `a²`,
attained on the dominant mode when it is semisimple. So `a < 1` is a turn in which dissipation
outweighs the pump's work, `a > 1` one in which the pump's work outpaces it (past the
bifurcation), and `a = 1` the lossless return the resting sheet carries.

**The code length as a function of the growth exponents.** Hence

```text
ℓ = log(1 + Σ_x e^(κ_x)) − κ_t,     dℓ = Σ_x θ_x dκ_x − dκ_t = −(dκ_t − ⟨dκ⟩_θ),
```

where the average includes the resting sheet with `dκ = 0` (`HNN/ExecutedComparison.lockFace_covector`).
This is Astra's special case: the force on the target is `dκ_t`, half the change of its storage
growth exponent per turn, and the code length moves by its excess over the shares' average.

## 3. The temperature is the number of periods the comparison reads

Read over `n` repetitions of the same passage, a member's monodromy is `Mⁿ`, whose spectral radius
is `ρ(M)ⁿ` (spectral mapping); every candidate reads `a_xⁿ` and the resting sheet still `1`. The
shares become

```text
θ_x(n) = a_xⁿ / (1 + Σ_y a_yⁿ) = e^(n κ_x) / (1 + Σ_y e^(n κ_y)),
```

a Gibbs state at inverse temperature `n` over the levels `−κ_x`. **The temperature is the
reciprocal of the number of turns the lock is read over.** The release reads one turn
(`read_turn` multiplies exactly `schedule.period()` crossings), so the lock face's class shares are
at inverse temperature `1`. This is the class shares' temperature only: the order in which the
release commits its stations is read at zero temperature (#225, Lean `HNN/OrderTemperature`).
Nothing declares it as a constant and no bath sets it: it is fixed by the receiver's clock, one
decision per passage. In storage exponents (`2κ`) the inverse temperature is `½` per turn, the
same `½` as the amplitude face of a ratio of Holons, `log(ψ_T/ψ_H) = ½ log(q/p)`: the lock reads
amplitudes, whose squares are the storage.

**What would move it.** Only a change of the receiver's clock: reading the lock over more turns of
the passage lowers the temperature and sharpens the commitment; nothing in the chain does this
today. It matches the ratio chart's own law, temperature as a root (`ratio::exponentiated`,
`softmax(x/T)` sends `r` to `r^(1/T)`), with `1/T = n` an integer.

**The zero-temperature face is the hinge.** For every `n`, with `f` the hinge term of the same
readings (`hingeTerm`: `max(max_(x≠t) log(a_x/a_t), −log a_t)`),

```text
n (f)_+ ≤ ℓ_n ≤ n (f)_+ + log(2 + |s|),      ℓ_n / n → (f)_+,
```

(`lockFace_periods_hinge`, `lockFace_per_period_tendsto`; `|s|` the rivals). Step 1a's hinge is
step 1b's lock face read over infinitely many turns per period, and at one turn the lock face
exceeds the hinge's positive part by at most the log of the sheet count: the entropy of the shares
at unit temperature.

## 4. What the code length is not

1. **Not a function of the member's stored energy.** The monodromy is linear in the member's
   state, so `a_x`, and with it `ℓ`, is the same at every stored amplitude of the member. In
   Hearing's terms (`Holarchy/Hearing`), every rescaling of the member's own state is null to the
   lock face; what it hears is the growth exponents, and among their changes only those with
   `dκ_t ≠ ⟨dκ⟩_θ`. It does depend on the passing carrier's storage, which sets the pump's depth
   (`a² s^t` in `K_t`), so the source's stored amplitude reaches `ℓ` through the pump's work.
2. **Not a work or an energy at the bank.** Its levels `κ_x` are logarithms of storage gain per
   turn: rates, without units of energy. `ℓ` is a log-sum-exp of rates.
3. **A free energy only through a thermal port.** Give a thermal port at thermal scale
   `θ = k_B T` the levels `E_x = −θ κ_x` (the resting sheet at `0`). Its canonical state is then
   exactly the lock's shares (`Physics/Information/PortWork.canonicalState`, `log Z = log Π`), and
   for any positive population `p` the free-energy excess is `F(p) − F(θ) = θ D(p‖θ)`
   (`Physics/InformationDifference.freeEnergy_difference_eq_thermalScale_mul_kl`); the work a
   protocol extracts never exceeds it (`PortWork.extracted_work_le`). Since `ℓ = −log θ_t =
   D(δ_t‖θ)`, `k_B T · ℓ` would be the least work to commit the lock to its target sheet through
   that port (the point mass as the limit of positive populations; the port's owner admits only
   positive ones). The bank has no such port: nothing exchanges heat at `T`, and `θ` would be a
   free unit that the readings do not fix. The identification is a definition there, not a law.

## 5. Where "energy" applies

- **Energy** (with units): the member's stored energy `P`, the pump's work and the dissipation per
  turn (`word_tick_balance`), and the storage gain per turn `a²`.
- **Growth exponent** (a rate per turn): `κ_x = log a_x`, half the storage's.
- **Code length** (bits or nats, no energy): `ℓ`, the released code length summed over requests,
  the released jump in code length at a crossing, the flip cost and the repayment condition of the
  run of moves, and their covectors. These say "code length" in the records; "energy" is used for
  them only where a thermal port is built and the levels are its energies.

## 6. Owed (#62)

- The composed storage law of §2 in Lean: Gelfand's formula on the member's power form chained with
  the tick balance, `a² = lim_n (1 + w_n)^(1/n)`.
- The point-mass limit `D(p‖θ) → ℓ` as `p → δ_t` at the port, which `PortWork` states only for
  positive populations.

## 7. Receipts

- `lake env lean Holonics/HNN/ExecutedComparison.lean` on the branch: exit 0, no warnings in the new
  theorems; both appear in the module's axiom list.
- Owners read: `hnn::executed::{lock_face, LockFace}`, `hnn::ring::ReceivingBank::{read_turn,
  turn_monodromy}`, `HNN/Word.{word_tick_balance, field_commit_deposition}`,
  `HNN/Ring.loaded_tick_port_balance`, `Physics/Information/PortWork`,
  `Physics/InformationDifference`, `Holarchy/Hearing`, `ratio::exponentiated`.
