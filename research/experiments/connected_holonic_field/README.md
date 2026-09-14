# Connected attention, learning and geometric generation

[established-bounded; implemented-exact] This is the reference computation consumed by
`research/papers/source/papers/elementary-holon-generation/main.typ`. Fifteen complex field
channels pass through two normalized heads, two shared layers, a phase-sensitive contact,
one observed material update and a whole-field implicit solve. Its computed coefficients
feed the existing toroidal-basis decoder. The new figures are generated from this result;
no previously rendered Information Chemistry scene is imported.

## Operands and exact operation

[definition] `prepare.py` recovers 67 witnessed toroidal-support contacts from the existing
`receiver_engraving/woven_ecology.py` geometry and mounts states 0 and 1 from its recorded
constituted evolution as input V and observed Y. Original overlap strengths remain in
`input.json`; the supplied kernel chart measures each strength at the nearest multiple of
1/16, with coordinate error at most 1/32. This is a declared exterior coefficient chart.
All subsequent kernel arithmetic is rational, not a claim of an unrounded continuum kernel.

[definition] Head A has diagonal kernel 2 and off-diagonal `1+sampled_overlap` on admitted
contacts. Head B has diagonal 1 and `1+sampled_overlap²` on the same support. Missing contacts
remain zero. For positive entries `s=log K`, so `a=K/row_sum(K)` is exact softmax in the
log-rational chart. These supplied scores are not generic `exp(Q Kᵀ)` or learned query/key
projections. The formula document specifies the more general tensor block separately.

[definition] The reusable `NormalizedKernel` owner computes the current, its complete
potential/value differential, their pullback and a declared Euclidean material step:

```text
Y=a V,
dY=a dV + a (ds-E_a ds) V,
∂ℓ/∂s_ij = a_ij <Y_i-Yobs_i, V_j-Y_i>,
K' = K-(1/64)(∂ℓ/∂s)/K,     ℓ=1/2 ||aV-Yobs||².
```

[definition] Let A be the changed head and B the second normalized head. The layer is
`L=C[(1-g)I + g(A+B)/2 ⊗ I₂]`, with `g=sigmoid(log(1/3))=1/4`. C is the contact 5↔10 with
phase `u=-i`, `α=1/4` and the complete energy balance displayed in the formula. Two shared
layers act as `L²`. With λ=1/2 and mounted field h, generation integrates
`x_next=λL²x+(1-λ)h`, and the exact implicit result solves
`(I-λL²)x*=(1-λ)h`. A fixed-point solve describes the complete field simultaneously.

[proved-derived] Every head and residual mixture is nonexpansive in the maximum complex
channel norm, and the phase contact is a convex combination with unit phase. The forced
map is therefore a contraction of factor at most 1/2. This establishes this finite
reference's unique fixed point and convergence. It does not establish a learned diffusion
score, general semantic quality, changing incidence or the complete native HNN model.

## Returned evidence

[established-bounded; implemented-exact] `result.json` retains exact fractions for all
operands, both layers, gradients, snapshots, implicit solution and sensitivity. Its assertions
check the complete implicit residual, the derivative equation, positive-support update,
strict reduction of the declared observed loss, and the contact energy identity.

| Receiver | Value (decimal presentation of exact result) |
|---|---:|
| Observed loss before / after material step | 14.018085413379481 / 14.012743213908482 |
| Loss reduction | 0.005342199470997848 |
| Largest absolute real/imaginary change in integrated output | 0.00009660599076337706 |
| Deposited quadratic contact energy | 0.6678396061697263 |
| Euclidean implicit residual at refinement 8 | 0.00017563774538368191 |
| Exact implicit-solve and sensitivity residuals | 0 / 0 |
| Largest final numerator / denominator bit lengths | 1835 / 1834 |

[definition] The sensitivity passes through the **shared** two-layer operator:
`dB=(dL)L+L(dL)` and `dx*=(I-λB)^-1 λ(dB)x*`. This is checked as an exact linear identity.
The local learning objective and the later integration are distinct operations; the changed
material is consumed by the latter. No local driver implements another learner.

[definition] `render.py` reconstructs the coherent amplitude in the existing toroidal basis,
then its piecewise affine nodal intensity and level 1/3. It first rounds each exact complex
coefficient to 24 fractional bits, with real/imaginary error at most 2^-25; `geometry.json`
retains both coefficients, bounds, incidence and source edges. The resulting polyhedral
surface is exact for that declared receiver. We do not infer topological equivalence to the
unrounded field from the small coordinate error. Matplotlib floats only draw observer plots.

[established-bounded; computational-witness] The input, two-layer and integrated decoder
surfaces have respectively 1886/3840, 1820/3704 and 1846/3760 vertices/triangles. Every generated
mesh is closed with coherent face orientation under the decoder checks. These changes
concern this polyhedral intensity receiver; a triangle count alone does not classify topology.

[definition] `schematics.py` produces the leader/return coupled-law diagram and a recursive
four-map arrangement of the **new integrated field**. Those are explicitly supplied
constructions. The four-copy similarity dimension follows from separated ratio-1/3 maps;
the reference learner does not infer that fractal morphology or simulate a plasma leader.

## Reproduce

```bash
python3 research/experiments/connected_holonic_field/prepare.py
cargo run -p holonic-engine --no-default-features --example connected_holonic_field -- \
  research/experiments/connected_holonic_field/input.json \
  research/experiments/connected_holonic_field/result.json
python3 research/experiments/connected_holonic_field/render.py geometry
python3 research/experiments/connected_holonic_field/render.py
python3 research/experiments/connected_holonic_field/schematics.py
typst compile --root . \
  research/papers/source/papers/elementary-holon-generation/main.typ \
  research/papers/rendered/elementary-holon-generation.pdf
```

[definition] The plot environment needs NumPy and Matplotlib. Geometry uses the repository's
standard-library Fraction decoder. Computation uses public `NormalizedKernel` and
`ExactRatMatrix` operations. Their CPU execution is exterior reference work; no host
semantic loop was added to native HNN cultivation or generation. The dated research record
holds verification and measured execution costs, including the withdrawn rational-inverse trial.

[established-bounded; process-audit] The recorded existing-solver run returned in 368320 ms
(including its comparisons and exact sensitivity); its first implicit inverse/solve took
209833 ms. These are Rust debug CPU wall clocks, excluding Cargo build and rendering, on
the Ryzen 9 7900X workstation. Other verification/rendering ran concurrently, so they are
not isolated performance benchmarks. A per-row denominator-clearing/Bareiss candidate
passed 41 exact-linear tests and completed the same consuming run in 421385 ms, with every nonclock result exactly
identical. The slower candidate was withdrawn; `rational_inverse_trial.patch` preserves
the candidate for evidence. The active solver is unchanged. No speedup is claimed.
