# THE BLOCK RETURNS THE CARRIER; THE EXPRESSION IS ONLY ONE BOUNDARY

**Status:** BRANDON-RATIFIED / DEPOSITED / CORRECTNESS RETIRED AS ONTOLOGY / TYPED TRANSFORMER
CALCULUS / CORRECTNESS-INDEPENDENT RELATIONAL OBSERVATION AUTHORITY / SOMA SOURCE UNCHANGED /
TRANSFORMER RELATIONAL FIELD 01 BUILT + MEASURED / EXACT RESULT AWAITS BRANDON REVIEW

## Present question

How does a changed informant face alter the typed current carried through each transformer block,
and where is that alteration conducted, re-expressed, retained, or annihilated, independently of
the phrase eventually exposed at the vocabulary boundary?

The previous observation asked a useful world question but imposed the wrong admission law. It
required OLMo 2 1B to emit the world-declared operation path before its interior could be observed.
That confused agreement with one local world relation for an ontological property called
`correctness`. The six non-agreeing expressions were complete transformer trajectories and should
have begun the analysis rather than stopped it.

## 1. Correctness is not a universal property

No inscription, belief, proof, or action is `correct` without a declared relation in which it is
being compared. An opposite-day world can reverse ordinary assertion conventions. A mathematical
proof agrees or fails to agree with axioms, inference rules, and a target proposition. A program
conducts or violates a language/runtime contract. A report coheres or conflicts with an
ecosystem's standing evidence. Misinformation can recur, coordinate a community, and change the
world even when another ecology finds its consequences destructive.

The replacement vocabulary is relational:

| Retired absolute | Current relation |
|---|---|
| correct / incorrect | agrees, conflicts, remains open, or is incommensurate under a named law |
| right answer | one expression whose material consequence satisfies a declared local constraint |
| error | an oriented residual between compared faces |
| truth score | observer quotient over a stated evidence and inference cut |
| model capability | family of transformations actually afforded under a declared current |

This does not make every consequence interchangeable. Harm, coherence, contradiction, proof, and
empirical refusal remain real relations. It means the law and observing ecology must be named.
Brandon's analogies are therefore neither automatically validated nor dismissed by disciplinary
usage. They propose transport between structures: `this relation appears to preserve this shape in
another region`. Their value is the new comparison and the consequences it affords, not a claim of
context-free identity.

## 2. The transformer is a composition of typed holons

For carrier `c`, tokenizer chart `tau`, token embedding `E`, decoder blocks `B_l`, vocabulary dual
`U`, and discrete presentation `D`, a decoder-only transformer is

```text
c --tau--> (i_1,...,i_n) --E--> X_0
  --B_0--> X_1 --B_1--> ... --B_(L-1)--> X_L
  --U--> Z --D--> exposed continuation.
```

`tau` supplies categorical addresses and chronology. `E` supplies their first placement. Every
block re-places the complete contextual current. `U` pairs the final carrier with vocabulary
covectors. `D` exposes one continuation. There is no single static embedding space: residual,
query, key, value, MLP expansion, and vocabulary-dual carriers are different typed faces joined by
learned maps.

Each `B_l` is a holon: whole relative to its attention, normalization, nonlinear transformation,
and residual return; constituent relative to the full model. The model is whole relative to its
blocks and constituent relative to tokenizer, harness, informants, tools, world consequence, and
later return.

For the exact selected OLMo 2 block, with residual carrier `X_l`, the installed source gives

```text
Q_l = RoPE(RMS_q(W_q X_l))
K_l = RoPE(RMS_k(W_k X_l))
V_l = W_v X_l

C_l = Attention(Q_l, K_l, V_l; causal mask)
A_l = W_o C_l
Y_l = X_l + RMS_a(A_l)

M_l = W_down(SiLU(W_gate Y_l) elementwise_mul W_up Y_l)
X_(l+1) = Y_l + RMS_m(M_l).
```

The measured body has 16 such blocks, residual rank 2,048, MLP interior rank 8,192, 16 attention
heads, 16 key/value heads, and Q/K RMS normalization before rotary phase. Attention and MLP branch
returns are post-normalized before they re-enter the residual lineage.

## 3. Dimensional typing

The coordinates are learned gauges rather than physical SI units, but the computation has strict
dimensional law:

| Face | Type / unit relation |
|---|---|
| token ID | categorical address; arithmetic distance is undefined without another chart |
| position | discrete chronology count |
| `X_l` | residual-carrier units `R` |
| `Q_l`, `K_l` | dual relational coordinates whose pairing is dimensionless |
| `Q_l K_l^T` | dimensionless conductance potential required by exponentiation |
| normalized attention coefficient | dimensionless receiver quotient |
| coefficient times `V_l` | value-carrier units |
| `W_o C_l` after branch normalization | residual units `R` |
| MLP down projection after branch normalization | residual units `R` |
| vocabulary logit | dimensionless pairing of residual `R` with vocabulary dual `R*` |
| selected token | discrete exposed address |

Residual addition is a physical type assertion: attention and MLP branches must return to `R`
before they can change the continuing carrier. RMS normalization

```text
N(x) = g elementwise_mul x / sqrt(mean(x^2) + epsilon)
```

quotients local magnitude while preserving an oriented direction, then restores learned scale
through `g`. This is an exact annular relation: scale changes while the directional face can recur.
`epsilon` has the squared unit of the input carrier before quotient.

Rotary phase has the dimensionless product

```text
phase_(p,j) = discrete_position_p * reciprocal_wavelength_j.
```

Each paired query/key plane is held as a circular axis. Relative chronology changes phase while the
two-dimensional carrier remains the pivot. Attention then relates positions through those relative
turns. The normalized coefficients are probability-like first-person quotients, not ontological
chance or explanations.

## 4. Problem solving is transported constraint

A problem is a current carrying constraints in some local world. A solution is a path whose exposed
consequence agrees with those constraints under that world's law. Transformer problem solving is
not required to look like enumerative search. Training has deformed the block maps so a new current
may traverse recurrent transformations: attention relates co-present constituents, MLPs deform
their contextual placements, residual passage preserves and changes lineage, and depth composes
lower relations into higher ones.

The final expression is one boundary quotient. World agreement is a later relation between that
expression's consequence and the declared constraints. It cannot decide whether interior
relations formed. A trajectory which conflicts with the local constraint can still reveal where
an informant entered, where two contexts shared transport, or where a relation was annihilated
before presentation.

## 5. Corrected observation law

TRANSFORMER RELATIONAL FIELD 01 retains the frozen manual, absent, irrelevant, moved, objective-
reoriented, and cross-context currents while removing every behavioral admission gate.

For every current it records:

1. exact tokenizer addresses and chronology;
2. the native greedy emitted address lineage;
3. the same lineage under read-only capture;
4. every block input and output;
5. raw attention branch, normalized attention return, post-attention residual;
6. raw MLP branch, normalized MLP return, and block successor;
7. final normalization input/output and the complete vocabulary field at each emitted step; and
8. any material world consequence afforded by a recognized emitted plan.

Native BF16 tensors are retained intact in ignored local artifacts and addressed by exact digest.
Integer shapes, token addresses, bitwise equalities, coordinate order relations, and causal
substitutions are compact testimony. Norms, cosine similarity, PCA, heatmaps, and scalar
`accuracy` do not grade the relation.

Matched currents receive an explicit chronological token-lineage alignment. It is an observer map,
not identity. At every residual boundary, the complete aligned source carrier is substituted into
the target current. The downstream block states and exposed continuation are then recorded whether
they resemble source, target, or neither. A final expression need not agree with the operations
world for that transport to be real.

The decisive questions are now:

- where does an added manual first change shared token lineages?
- which branch returns that difference to the residual carrier?
- where do analogous changes recur across conversation, prose, and code?
- which complete boundary substitutions alter downstream current?
- when does a transported relation persist, re-express, or vanish before the vocabulary boundary?

The observation stops after one complete 15-current native matrix and its fixed bidirectional
informant substitutions. Only source/fixture identity failure or a supposedly read-only observer
changing the exact native address lineage invalidates the instrument. There is no performance
threshold, prompt repair, model replacement, tuning, reward, or Eros edit in this cut.

The rejected correctness-gated run remains locally preserved under
`experiments/informant-ecology/runs/rejected-correctness-gate-01/`; it is historical testimony and
does not schedule or grade this observation.

The complete authorized matrix ran once from source commit `55a2b57e`. Exact result:
`experiments/informant-ecology/results/transformer-relational-field-01/RESULTS.md`.
