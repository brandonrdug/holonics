# The readings locate the receiving prior by the prequential certificate

October 2. Refs #73, #62, #63. Lean `HNN/ReceivingPrior` (§4 of its header); the exterior replay
`research/notebook/hnn_design/receiver_prior_scale.py`;
[receipts](2026-10-02_THE_READINGS_LOCATE_THE_RECEIVING_PRIOR_receipts/).

[The receiving-prior record](2026-10-02_THE_RECEIVING_PRIOR_IS_THE_ANCHORS_UNIT_AND_THE_CAP_IS_THE_SAME_CONSTANT.md)
derived the prior Gram's shape `I`, proved that its scale is the anchors' amplitude unit, and
located `H₀ = I` by replaying the receiving map's law on campaign 1's first 2,192 readings. It
left two things open: the campaign's third aeon, and the law that would locate the scale on a
medium whose anchors have other amplitudes (#62). This record reads the whole campaign (§1–§2),
reads the storage form's coefficient as a scale (§3), and derives the locating law (§4–§5).

## 1. The whole campaign: the Gram's trace passes the prior, no direction does

Same host reference as before (`hnn_exposure ablation 1700 samples`, main at `193fc9b6`, cloud,
four cores), run to the end: 3,400 readings
([run](2026-10-02_THE_READINGS_LOCATE_THE_RECEIVING_PRIOR_receipts/samples_run.txt), its per-window
lines dropped). Projection `1800` s from the first run's aeon closes, deadline `2400` s; measured
`1868087` ms wall, peak resident set `301776` KiB.

| Reading (3,400 readings, `n = 22` anchor coordinates) | Value |
|---|---|
| largest anchor energy `\|z\|²` | `68693/2^24` (below `2^(−7)`) |
| mean anchor energy | `11179037/2^35` |
| accumulated `tr F = Σ \|z\|²` | `9279474/2^23` (above `1`) |
| first reading at which `tr F ≥ 1` | `3109` |
| largest eigenvalue of `F` | `8599329/2^24` (below `1`) |

The receiving-prior record §4 projected the trace to reach `1` at 3,239 readings from the first
two aeons' mean; the third aeon's anchors are larger, and it reaches `1` at reading 3,109. So
"the readings' Gram never outweighs the prior" fails for the trace over the whole campaign. It
holds along every direction: the largest eigenvalue stays below `1 = s`, so the prior keeps more
than `2^24/(2^24 + 8599329)` of the step along each direction (`opening_outweighs_iff` read on
each eigenvalue), more than half. The eigenvalue is a float read at 24 bits.

## 2. The whole campaign's code

The replay is the receiving-prior record's (§5), now over every integer `k` from `−6` to `6`, the
even `k` from `−14` to `−8`, and the unit-information prior: eighteen members, whose charge is
`log₂ 18`, in `(4 + 2/16, 4 + 3/16)`
([output](2026-10-02_THE_READINGS_LOCATE_THE_RECEIVING_PRIOR_receipts/prior_scale.txt); the same
read at 2,192 readings is
[beside it](2026-10-02_THE_READINGS_LOCATE_THE_RECEIVING_PRIOR_receipts/prior_scale_2192.txt)).
The tree alone codes `12562819/2^10` bits. Differences are exact between the output's dyadic
totals.

| Prior `H₀` | code − tree, 3,400 readings (bits) | above the best member (bits) |
|---|---|---|
| unit information | `9146793/2^15` | `307022/1024` |
| `2^(−6) I` | `12841939/2^16` | `221840/1024` |
| `2^(−2) I` | `10374735/2^18` | `61711/1024` |
| `2^(−1) I` | `10863860/2^22` | `23837/1024` |
| `I` | `−8894305/2^19` | `3813/1024` |
| `2 I` | `−10846561/2^19` | `0` |
| `2^2 I` | `−8530273/2^19` | `4524/1024` |
| `2^3 I` | `−10745538/2^20` | `10691/1024` |
| `2^4 I` | `−12111237/2^21` | `15271/1024` |

The best member is `2 I`. Every scale below `I` codes worse than the tree alone. At 2,192 readings
the best member over the same family is also `2 I` (`8704939/2^10` bits, with `I` `3482/1024`
above it and `2^2 I` `978/1024` above it).

**The charge belongs to the grid, not to the readings.** Under a uniform code over a replayed
family, naming its best member costs `log₂` of the family's size. The reading count enters
nothing. #251's family had eleven members (the even scales from `2^(−14)` to `2^4` and unit
information), so its charge was `log₂ 11`. This family has eighteen (the odd scales from `2^(−5)`
to `2^5` and `2^6` added), so its charge is `log₂ 18`. "Inside the charge" therefore judged the
grid that was replayed: `3813/1024` lies inside `log₂ 18` and outside `log₂ 11`.

The grid-free question is whether a code over the scales `2^k I` can prefer `I` to `2 I` against
the readings. That needs `ℓ(1) − ℓ(0) > 3813/1024` bits, so `I` must carry more than `2^3` times
`2 I`'s prior weight (`3813 > 3 · 1024`).
- Nothing derives such a weight. By the unit theorem every scale is the same law in other anchor
  units (the receiving-prior record §3), so no scale is favoured beyond how the integers `k` are
  indexed.
- An ordinary index of the integers gives far less. Elias's gamma code over `0, 1, −1, 2, …`
  charges `ℓ(0) = 1` and `ℓ(1) = 3`, a difference of `2` bits.

The readings separate `2 I` from `I` by more than that index charges: by `3813/1024` bits over the
campaign, and `3482/1024` at 2,192 readings. `2^2 I` is `4524/1024` above `2 I`.

## 3. The storage form's coefficient is not the scale

The receiving-prior record §2 takes the prior's shape from the receiving ring's storage form
`(h/4)Y_R|v|²`. The receiving map's feature is the ring's anchor itself, rotated by the ratio's
lift (`Resident::receiving_inputs`; weight `1`), so `z` is measured in anchor units. Campaign 1
declares `h = 1` and `Y_R = 2` (`FieldDeclaration::campaign_one`), so the coefficient is
`(h/4)Y_R = 1/2`.

Read as the prior's scale, `s = 1/2` codes `23837/1024` bits above the best member over the
whole campaign (`16265/1024` at 2,192 readings), more than the readings' separation of `I` from
`2 I`. The coefficient is refused.
The units say why: `s` is an anchor energy, `|z|²`, while `(h/4)Y_R` is power per anchor energy.
A scale needs a declared power `P₀`, and the anchor energy that carries it is
`|v_R|² = (4/h)P₀/Y_R` (the bound in `hnn::constitution`'s module header). The medium declares no
power for `R`. At `P₀ = 1` that energy is `4/(hY_R) = 2`, the best member. [agent-inferred] The
shape argument fixes the scale only given a declared power, which campaign 1 does not declare.

## 4. The law: the prequential certificate

Each reading `t` meets the map `W_t` built from the readings before it, and is scored before its
window's deposit. The map moves its logits by `δ_t = W_t z_t`. Where the map is `1/s` times its
unit (the readings' Gram small against the prior and `η = 1`, §1 and the step medians), raising
the prior to `s/φ` scales every `W_t` by `φ`. Then the readings' prequential code, the evidence
for the prior, changes to second order by

```text
L(φ) − L(1) = −(φ − 1) a + ½ (φ − 1)² V,     a = Σ_t ⟨g_t, δ_t⟩ ,  V = ln 2 Σ_t Var_p_t(δ_t)
```

with `g_t = q_t − p_t` the combined face's descent covector at the reading and `p_t` its masses
(the code's Hessian in base-2 exponents is `ln 2 (diag p − p pᵀ)`). Its Newton point is
`φ = 1 + a/V` (`newton_point`), so the readings locate the prior at

```text
s ↦ s/(1 + a/V);      the code is stationary in the prior where a = 0.
```

`a` and `V` are the receiving certificate's alignment and curvature (`receiving_fisher_face`)
read on readings before their deposit rather than on the window's own. They are two running sums
of quantities each reading already presents to the map, so the law needs no tape. The window's
own certificate cannot locate the prior: its alignment includes each reading's pairing with its
own deposit, which is positive whatever the readings share.

At the opening (`s` above every reading), `W_t = M_t/s` with `M_t = Σ_(u<t) κ_u g_u z_uᵀ` read at
the tree face, and the law gives `s_open = V₀/a₀` with `a₀ = Σ_t ⟨g_t, M_t z_t⟩`,
`V₀ = ln 2 Σ_t Var_p_t(M_t z_t)`. Its parts:

- **Signal less self-energy** (`prequential_pairs`). At one `κ`,
  `a₀ = (κ/2)(‖Σ_t g_t z_tᵀ‖² − Σ_t |g_t|²|z_t|²)`: the covectors' summed energy less each
  reading's own.
- **The self-energy's chance level** (`fisher_trace`). Under the face's own masses,
  `E|q − p|² = 1 − Σ p²`, the class Fisher trace. If the tree's masses were the readings' law and
  the readings independent, `a₀` would vanish in expectation: the map gains only what the face
  misses. `a₀ > 0` is the receiving-prior record's ratio `‖G‖²/tr A > 1`, read on ordered pairs.
  When `a₀ ≤ 0` the law locates no finite prior: the readings give the map nothing to keep.
- **The anchors' unit** (`variance_smul`). Anchors `c z` give `M ↦ c M`, so `a₀ ↦ c² a₀`,
  `V₀ ↦ c⁴ V₀` and `s_open ↦ c² s_open`, as `unit_step_read_prior_scale` requires. A medium with
  other amplitudes carries its located prior with it.

## 5. Campaign 1 read by the law

| Readings | `a` changes sign | Newton point from `I` | from `2 I` | `s_open` | best member |
|---|---|---|---|---|---|
| 2,192 | between `2 I` (`−11305578/2^23`) and `2^2 I` (`13054527/2^22`) | `14350156/2^23` | `9137823/2^22` | `13773580/2^22` | `2 I` |
| 3,400 | between `I` (`−13616686/2^19`) and `2 I` (`13282991/2^23`) | `12055433/2^23` | `16109515/2^23` | `14757253/2^22` | `2 I` |

Over the whole campaign the law locates the prior between `I` and `2 I`: `a < 0` at `I` (the map
overreaches readings it has not met) and `a > 0` at `2 I`, and the Newton points from both sides
fall inside that interval. The Newton point read at `2 I` is `16109515/2^23`, below `2` by
`667701/2^23` (less than `2^(−3)`). The best replayed member is `2 I` at both lengths. Below `I` the law
pushes up from every member: from `2^(−14) I` its Newton point is `15392687/2^35`, more than
`2^2` times the prior it is read at, and the replayed code falls monotonically up to `2 I`. The
opening's `s_open`, read before the map has moved, lies between `2 I` and `2^2 I`, above the
stationary interval; it is the law's first step, and the at-map read refines it.

## 6. Decision

[agent-inferred] `H₀ = I` is released, and campaign 1's receiving prior is `2 I`.
- The prior is held on the powers of two, so that its founding chart `s⁻¹ I` is exact on the
  dyadic lattice (`SolvedChart::identity` is founded exact).
- Among the powers of two, the law and the code select the same member.
  - The prequential alignment changes sign in `(I, 2 I)`.
  - The Newton point read at `2 I` lies within `2^(−3)` below `2`.
  - `2 I` is the best replayed member at 2,192 readings and at 3,400.
- `I` has no derivation as the lower end of the interval. The law's stationary point lies near
  `2 I`, and the readings separate the two members by more than an ordinary index of the scales
  charges (§2).

The scale is a field's own quantity: §4 locates it per field and carries it with the anchors'
energy. Campaign 1's located value is therefore declared with its field, not fixed in the
receiving map's law. Opening the receiving map at `2 I` changes the HNN's behaviour, so that
change is its own pull request and merges after the main line measures it on campaign 1 and its
held-out read.

Carrying `a` and `V` natively beside the Gram, and moving `s` by the Newton point as readings
arrive, is the per-field law's native form. It is not built here. The second-order expansion of
the prequential code along a scaled map, the step from which `newton_point` is applied, is owed
in #62; its algebraic parts are proved here.
