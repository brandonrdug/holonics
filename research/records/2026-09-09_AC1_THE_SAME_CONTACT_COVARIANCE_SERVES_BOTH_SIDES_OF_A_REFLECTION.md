# AC1: the same contact covariance serves both sides of a reflection

[definition] This continues the existing-owner reuse work from `1fed5a09`. A paired reflection
first admits any actual contact birth, then solves for the potential and advances internal
current. Its contact map does not change between that solve and the return of the new aggregate.
The change reuses that particular standing; it introduces no new current or learning law.

## The retained relation

[proved-derived] Write the numerical contact map as D and the entering internal current as b.
The existing moment receivers are `C = D D†` and `h = D b`. After the reflection, the new
internal current is `b_next = D† v - b`. The covariance remains C, while the returning aggregate
is `h_next = D b_next`. This holds whether or not the occurrence admitted a new contact before
the first moment preparation. A later contact deposit changes D and requires its own preparation.

[established-bounded; source-inspected] `field_operative_reflection.cuh` previously called the
complete moment preparation twice: once before solving and again after advancing b. Between
these calls it changes b and its error bound, but neither D nor the contact-map error bound.
Both calls therefore evaluated the same covariance entries, covariance error and map norm.

[proved-derived] The declared numerical covariance is the same ordered integer dot product
followed by the same dyadic projection on both sides. Its bound depends on the unchanged map,
map radius and those same projection residuals. Reusing it is exact at the numerical and bound
receivers. By contrast, the aggregate error includes

```
||D_hat|| * e_b + ||b_hat|| * e_D + e_D * e_b + aggregate_rounding.
```

Both the internal-current norm and e_b may change in the reflection. That whole expression,
the new aggregate and its ordered dot-product rounding must be recomputed. Keeping C does not
make the interior inactive or license discarding its contribution.

## Native construction and checks

[established-bounded; source-inspected] `operative_moments_prepare` now has a compile-time
specialization. Its complete preparation remains the default for mounting, contact updates,
historical producing-map recovery and the first half of each reflection. Only the second call
within `field_operative_reflection_prepare` uses the specialization that retains covariance.
It recomputes h, the norm of b and the complete aggregate bound, retaining the original grain,
contact population and chronology. No host API, file format or model parameter changes.

[established-bounded; measured] The existing changed-contact/reflection control now additionally
recomputes all moments through the complete native preparation after each tested occurrence.
Covariance, aggregate and their full bound buffers agree bit for bit, across non-dyadic complex
currents, actual later contact births and recharts. The control retains its independent exact
paired-current comparison and source/persistence assertions. It passes in 105.44 seconds,
including initial CUDA module load.

[established-bounded; measured] All 111 field tests pass in 126.44 seconds. The text example
build passes. The [portable receipt and logs](2026-09-09_covariance_reuse/return.json) retain the
commands and comparisons. No Lean, SDK interface or serialization owner changed.

[established-bounded; implemented-exact; measured] The matched first-family development returns
75 occurrences with no numerical development readouts. Its complete recorded body and
11,680,724-byte checkpoint are identical to the previous zero-extension run. Development takes
7.486 seconds versus 7.628 seconds previously; the small timing difference is not a general
throughput claim.

[established-bounded; implemented-exact; measured] A fresh process mounts the existing
5,064-occurrence compact model and runs the same prompt and continuation. Its complete recorded
body, emission-current history and generation agree exactly with the preceding run. Prompt plus
generation takes 26.312 seconds versus 36.032 seconds, about 27% less elapsed time in this
single matched comparison. Whole-process time is 62.176 seconds. No claim of measured power,
statistical benchmark confidence or useful language follows from this timing observation.

[definition] This is AC1 dependency reuse in the existing reflection. The last model's `I’mn`
response remains unusable. AC1's nonzero factor representation and path/relation development,
AC2's useful contextual output, and the broader AC3–AC5 product work remain unfinished.


## Next learning comparison

[definition] The next AC1–AC2 action examines finite learning effectiveness, following the
parallel changing-constitution result that a correct local derivative and exact representation
do not guarantee improvement after a finite step. The current contact response uses a unit
Frobenius constitutive functional. Compare its actual source-conditioned response before and
after the finite deposit, keeping the producing and current morphologies explicit and retaining
complete oriented material differences. This is a diagnostic over the existing native return,
not a universal acceptance gate or a replacement world-verdict learner. Use its returned evidence
to derive any needed correction rather than inferring improvement from a changed coefficient.
