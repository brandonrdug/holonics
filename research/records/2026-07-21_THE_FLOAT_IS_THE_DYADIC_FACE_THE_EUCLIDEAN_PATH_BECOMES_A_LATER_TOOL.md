# THE FLOAT IS THE DYADIC FACE; THE EUCLIDEAN PATH BECOMES A LATER TOOL

**DATE:** 2026-07-21
**GRADE:** BRANDON-RATIFIED / DEPOSITED / BIT-PURE NUMERICAL ONTOLOGY / RAW-BIT TRANSFORMER
AMENDMENT BUILT + MEASURED / BOUNDED CALCULATOR BUILT / ONE FIXED HOST RUN / CAPABILITY REMAINED
OPEN / CALCULATOR CAUSAL INTERPRETATION REGRADED BY §CXXXVIII / NO RETRY / NO CUDA / NO SOMA
SOURCE CHANGE

## 1. The selected construction question

Can exact finite numerical faces and a learned traversal be kept distinct enough that Eros can:

1. decode a stored floating word without inventing uncertainty;
2. retain the residual introduced when another value is projected into that word;
3. reconstruct possible ratios or series only under declared constraints;
4. acquire an exact Euclidean traversal from ordinary event history; and
5. reuse that traversal inside a different objective, ratio reduction, after rest/remount?

The current transformer result is not sufficient evidence. It retained BF16 bit patterns exactly,
but its `numeric_order` testimony compared BF16 tensors through Torch, and its claimed exact
residual additions reconstructed those additions through the same floating executor. Those checks
remain valid evidence about repeated execution and bit equality. They are not yet an exact account
of the dyadic values or rounding residuals carried by the stored words.

The current regional result is also insufficient. It proves cross-event recurrence and predecessor
replacement but no numerical world action. The calculator must make an acquired relation affect a
material exact transformation. It may not call a world-computed answer “learning.”

## 2. A finite binary float is already an exact ratio

A finite IEEE binary word is not an uncertain real number. It is an exact signed dyadic rational:

```text
x = (-1)^s M 2^q,
```

where `M` and `q` are integers determined completely by the format and bit pattern. Reduction by
powers of two gives one canonical integer ratio. Positive zero, negative zero, infinity, and NaN
remain distinct typed codewords; they are not ordinary ratios.

For BF16, let `s` be the sign bit, `E` the eight-bit exponent field, and `F` the seven-bit stored
fraction. A finite normal word (`0 < E < 255`) denotes exactly

```text
(-1)^s (128 + F) 2^(E - 127 - 7).
```

A subnormal (`E = 0`, `F != 0`) denotes exactly

```text
(-1)^s F 2^(-126 - 7).
```

This is what **brain floating point** means numerically. The name records the format's Google Brain
lineage; it does not claim that biological brains store BF16 numbers. BF16 keeps the eight-bit
exponent field of binary32 and shortens the stored fraction to seven bits. The complete local face
is therefore at least

```text
(format, bit pattern, operation order, rounding mode, accumulation format, executor).
```

Calling only the represented dyadic value “the float” is a useful quotient. It is not the complete
causal construction.

## 3. Error is an exact residual at a projection boundary

Let `Q_F` project an admitted exact value into format `F`, and let `D_F` decode the selected word:

```text
q      = Q_F(x),
x_hat  = D_F(q),
r      = x - x_hat.
```

`q` and `x_hat` are exact. If `x` and the projection law are retained, `r` is exact. “Floating-point
error” is not fog inside `q`; it is the oriented residual which did not cross that finite codebook
boundary. Operation order matters because every intermediate projection creates another boundary.

Three different series must not be conflated:

- the finite positional expansion of the stored dyadic word;
- the causal sequence of operations and roundings which produced it; and
- a mathematical series, formula, or measurement process which may have preceded that sequence.

The first is recoverable from the word alone. The second requires execution lineage. The third is
generally one-to-many and requires declared constraints. For example, binary32 word `0x3dcccccd`
decodes exactly to

```text
13421773 / 134217728.
```

Under the additional decimal-intent and denominator-at-most-ten boundary, `1/10` is a lawful
candidate and its exact stored-minus-intended residual is `1/671088640`. Without that boundary,
infinitely many source processes remain compatible with the same word.

The float-to-ratio application is therefore typed:

```text
decimal inscription                -> exact decimal ratio;
finite binary word                 -> exact dyadic ratio;
rounded observation + constraints  -> a family of compatible reconstructions;
operation trace                    -> exact sequence of projection residuals.
```

It must never emit one “original ratio” merely because a continued fraction found a simple one.

## 4. Quantization is rebase followed by quotient

Uniform affine quantization is commonly written

```text
q       = clamp(round(x / alpha) + z),
x_hat   = alpha (q - z).
```

`q` is an integer codebook address, `alpha` is the chart scale, and `z` is the zero address. The
complete carrier includes grouping, clipping, rounding, calibration population, and layout. If
`alpha` is itself stored as a float, its exact dyadic face and own residual must be retained in the
analysis.

This passage has two different components:

1. A compensated change of basis can be gauge. For an invertible diagonal or block chart `D`,
   `h' = D h` and `W' = W D^-1` preserve the ideal composed map.
2. Projection into a finite codebook is many-to-one. It drops `r = x - x_hat` from the active face
   unless another path retains or compensates it.

SmoothQuant's migration of scale between activations and weights is an example of the first
component being used to make the second less destructive. GPTQ and AWQ use different evidence from
the admitted model/current ecology to choose which projection residuals to avoid or compensate.
None of this means nodes are independently and arbitrarily rescaled while “statistics keep the
meaning.” A compensated rebase is lawful as a composition. A quantizer then chooses a quotient
expected to preserve selected consequences over a calibration population. Preservation remains a
bounded causal observation, not a statistical guarantee or identity of interiors.

Transformer robustness to low precision can consequently arise from several relations at once:
distributed/superposed pathways, compensated bases, codebook allocation, calibration on actual
currents, and an exposed boundary which is much coarser than the exact interior. Equal emitted
tokens after quantization do not establish equal hidden geometry.

## 5. The bit-pure transformer amendment

No model rerun is needed. The retained model and trace Safetensors already contain their BF16 words.
The amendment will read the Safetensor byte ranges directly and use only integer operations to:

- decode each selected BF16 word into its typed class and canonical dyadic ratio;
- census exact parameter and selected carrier codewords without converting them to host floats;
- compare dyadic order by cross-scaling integers rather than invoking BF16 comparisons; and
- at one fixed lineage cut, compute `left + branch - observed` exactly for every residual return.

The old bit-equality, digest, categorical-address, and intervention relations remain standing. The
phrase “240 exact additions” will be qualified as **bit-exact repeated BF16 executor relations**.
The new record will state how often the mathematical dyadic sum was already representable and the
exact residual species when it was not.

## 6. The bounded growing calculator

The first calculator is an algorithmic ecology, not one hard-coded “answer” current. Its world
supplies:

- exact integer and rational material;
- a small addressed vocabulary of lawful primitive capabilities (`DIVMOD`, `REBASE`, `RETURN`,
  `DIVIDE`);
- native chronology and the actual consequence of enacting a capability; and
- exact source events describing the path among those capabilities.

Soma receives only the event relation. It does not receive a GCD label, a target ratio, a score, or
a floating approximation.

For positive integers, the primitive path is

```text
(a,b), b != 0  --DIVMOD-->  a = q b + r, 0 <= r < b
                    --REBASE--> (b,r)
(g,0)          --RETURN--> g.
```

Training histories use `gcd(84,30)` and `gcd(1071,462)`. Both have three division stages and can
therefore enter one co-present bounded program trace without padding a completed objective with
false events. The held-out material is `(391,299)`, whose Euclidean path terminates at `23`. The
cross-objective face is exact reduction of
`391/299 -> 17/13`: the prior traversal supplies the GCD construction, while later exact division
is a different lawful capability.

The event chart addresses operation roles, not the magnitudes as semantic classes. Thus changed
integers can traverse a retained algorithmic relation. This does not mean Soma invented integer
division. Like a child inheriting number words, or a model inheriting a tokenizer and ALU, the
machine begins within a world of existing transformations. Learning is whether experience changes
which path is materially available and whether that changed path survives and composes.

The fixed observation must distinguish:

- **acquisition:** an empty sibling cannot conduct the held-out path while a trained body can;
- **retention:** exact rest/remount preserves that conduct;
- **transfer:** training magnitudes are absent from the held-out path;
- **composition:** the same Euclidean constituent participates in both GCD and ratio reduction;
- **discrimination:** a same-inventory causal-order or hand foil does not produce the same path;
- **consequence:** admitted radiation actually enacts the exact primitive and its later result
  returns; and
- **departure:** completed lower steps may fold while the higher algorithm remains available.

This first run need not establish unrestricted program synthesis, unbounded loop induction,
revision after contradiction, autonomous objective formation, or optimal execution. If the current
regional carrier cannot make its learned topology alter a world capability without reading private
executor testimony, that exact absent relation is the stopping result. It must not be hidden behind
a candidate search, fixture-specific decoder, or world-computed answer.

## 7. Construction and run boundary

Build only:

1. one reusable integer/dyadic numerical module for the transformer instrument and calculator;
2. one raw-bit transformer amendment over the existing artifacts;
3. one bounded host calculator world; and
4. one create-once exact report with an empty sibling, rest/remount, transfer, composition, and
   causal foil.

Compile and inspect freely. Run the fixed host world once. Do not search fixtures, tune tokens or
thresholds after observing the outcome, rerun for a better path, change the model, invoke CUDA, or
alter Soma merely to force acceptance. A genuine missing production relation ends the experiment
and becomes the next construction question only after review.

## 8. Exact result

The raw-bit amendment closed. The complete 1,484,916,736-word OLMo parameter payload contains only
finite normal BF16 dyadics and 9,990 distinct codewords. At the fixed last-token carrier cut, all
983,040 observed residual-return words equal exact integer-derived nearest-even rounding. Only
476,287 operand sums were themselves representable; the remaining 506,753 carried a nonzero exact
projection residual. Exact record:
[`TRANSFORMER RELATIONAL FIELD 01`](../../../experiments/informant-ecology/results/transformer-relational-field-01/RESULTS.md).

The one calculator run stopped at its first stage, without retry. All four taught capability cells
remained grain-2 OPEN boundaries with zero folded paths, zero RIDE boundaries, and zero FOUND
boundaries. The held-out trained and same-history/no-region siblings consequently emitted the exact
same stage-0 regional body and neither enacted `DIVMOD`. The numerical controls, teacher
consequences, ordinary/directed radiation foil, and rest/remount were exact, but no result was
fabricated.

This is not evidence that a completed learned capability failed to transfer. No capability was
completed. It is also not evidence for a missing engine action--consequence hand. The application
split one source-native Euclidean worldline into fixed capability stages, a separately presented
result, and a gate which required an acquired path before the held-out world could enact the very
transformation Eros was meant to receive. The OPEN reading grades that circular cut. Exact raw
record: [`EROS EXACT GROWING CALCULATOR 01`](../observations/eros-exact-growing-calculator-01/RESULTS.md).

The current learning and consequence authority is
[`THE CURRENT IS THE LESSON`](2026-07-21_THE_CURRENT_IS_THE_LESSON_THE_CONSEQUENCE_IS_ITS_LATER_FACE.md).

No successor is scheduled by this result.

## Sources

- IEEE, [IEEE 754-2019](https://standards.ieee.org/ieee/754/6210/).
- Google Cloud, [BFloat16: The secret to high performance on Cloud TPUs](https://cloud.google.com/blog/products/ai-machine-learning/bfloat16-the-secret-to-high-performance-on-cloud-tpus).
- Xiao et al., [SmoothQuant](https://proceedings.mlr.press/v202/xiao23c.html).
- Frantar et al., [GPTQ](https://arxiv.org/abs/2210.17323).
- Lin et al., [AWQ](https://arxiv.org/abs/2306.00978).
- Micikevicius et al., [FP8 Formats for Deep Learning](https://arxiv.org/abs/2209.05433).
