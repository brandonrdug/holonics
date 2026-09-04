# HTP5 silent finite extension founded the infinite Copson--de Bruijn boundary

**Date:** 2026-09-02
**Scope:** HTP5 under
[`../../blueprint/THE_HOLON_IS_CAUSAL_NATURAL_AND_TENSOR_LENSES_RETURN_TENSOR_FACES.md`](../../archive/plans/THE_HOLON_IS_CAUSAL_NATURAL_AND_TENSOR_LENSES_RETURN_TENSOR_FACES.md).
**Truth status:** per claim under [`../../canon/EPISTEMIC_GRADES.md`](../../docs/canon/EPISTEMIC_GRADES.md).

## 1. Return

[proved-derived; formal-checked] HTP5 passed. The new owner
`Mathematics/CopsonDeBruijnInfiniteBoundary.lean` returns exact silent final extension, monotone
finite sharp coefficients, the direct extended-nonnegative infinite receiver, control by the
supremum of finite coefficients, exact finite-support reflection, and the least-coefficient
equivalence.

[definition] HTP6 is the next deed. It must prove the finite minimizer's coordinate positivity,
derive its Euler/KKT equations and finite de Bruijn recurrence, then identify the infinite boundary
with the dependent admissible-recurrence threshold and prove the declared asymptotic and rational
enclosure results.

## 2. Silent extension

[proved-derived; formal-checked] For a finite section of length `N + 1`, `zeroExtend` appends one
literal zero to obtain length `N + 2`. It proves:

- every old suffix energy is unchanged;
- the new final suffix energy is zero;
- every old suffix radius is unchanged;
- the new final radius is zero;
- mass is unchanged;
- tail surface is unchanged; and
- `finiteSharpCoefficient N <= finiteSharpCoefficient (N + 1)`.

[interpretation] A larger aperture cannot acquire a better sharp grade merely by adding silent
capacity. A later HNN application must still prove that its added sites or scales carry zero new
current; nominal padding alone is not this theorem.

## 3. Direct infinite receiver

[definition; formal-checked] Inputs remain `a : Nat -> NNReal`. The owner defines directly in
`ENNReal`:

```text
infiniteMass(a)         = tsum_n a_n
infiniteTailEnergy(a,n) = tsum_k if n <= k then a_k^2 else 0
infiniteTailRadius(a,n) = infiniteTailEnergy(a,n)^(1/2)
infiniteTailSurface(a)  = tsum_n (n+1)^(-1/2) infiniteTailRadius(a,n)
infiniteSharpBoundary   = iSup_N finiteSharpCoefficient(N).
```


[proved-derived; formal-checked] Every finite prefix satisfies the finite sharp inequality. Its
mass and surface embed monotonically into the direct infinite receiver, so taking the supremum of
partial masses proves

```text
infiniteMass a <= infiniteSharpBoundary * infiniteTailSurface a.
```

[definition] No finiteness of `infiniteSharpBoundary` is claimed by HTP5. The direct carrier keeps
divergent mass, energy, or surface at `top` rather than using the zero-valued nonsummable real
`tsum` convention.

## 4. Finite-support reflection and optimality

[proved-derived; formal-checked] `finiteSupportExtension` embeds a finite section into an infinite
one and returns exact equality for:

- mass;
- every old suffix energy;
- every old suffix radius;
- the complete tail surface; and
- zero energy/radius beyond the finite support.

[proved-derived; formal-checked] Consequently, any `ENNReal` coefficient controlling every direct
infinite section bounds every attained finite coefficient. Taking the supremum returns

```text
infiniteSharpBoundary <= coefficient
  iff
forall a, infiniteMass a <= coefficient * infiniteTailSurface a.
```

This identifies `infiniteSharpBoundary` as the least universal coefficient at the exact
extended-nonnegative scope.

## 5. Athena/HNN interpretation boundary

[interpretation] The theorem supplies receiver mathematics for increasing site populations, causal
depths, histories, or morphology sections. It says when finite aperture testimony coheres and when
unbounded unresolved activity remains visible.

[counterexample] HTP5 does not define a native Athena loss, optimizer, stability governor,
termination rule, emission selector, or cultivation law. Applying it to an HNN requires the
post-HTP `CausalTailLens`, including a signed/complex source preimage behind the nonnegative energy
face.

## 6. Validation

[established-bounded; formal-checked; measured] On 2026-09-02:

- `bash tools/lean_check.sh ElementaryHolonics.Mathematics.CopsonDeBruijnInfiniteBoundary`
  completed 3,018 jobs;
- `timeout 180s lake build ElementaryHolonics` completed 9,772 jobs;
- `bash tools/lean_check.sh` completed the 3,772-job live engine-oriented umbrella;
- formal, source-shape, epistemic-tags, claim-index, and document-law gates returned five passed and
  zero failed;
- every audited terminal theorem used only `propext`, `Classical.choice`, and `Quot.sound`;
- no `sorry`, `admit`, or new axiom entered; and
- `git diff --check` passed.
