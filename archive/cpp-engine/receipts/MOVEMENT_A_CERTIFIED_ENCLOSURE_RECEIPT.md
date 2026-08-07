# Movement A certified exact enclosure carrier receipt

**Truth status:** `established-bounded`.

**Evidence:** `implemented-exact` for the enclosure carrier, the separation certificate and its
revalidation, the commitment law, the declared occurrence family, the certificate ablation, and the
aperture refusal; `computational-witness` for the actual GPU deed, the exact device/host parity, and
the independent host oracle. The reciprocal Cauchy root bound has the separate `proved-standard`
grade. The claim that this organ suffices for any later analytic construction is `open` and is not
asserted here.

## Construction tuple

| Field | Standing |
|---|---|
| Source owners | the `exact` value library — limb words, unsigned integers, signed magnitudes, status and checked-result receipts — plus the apparatus executor contract and the pinned device profile |
| New consequence | an exact enclosure set, a separation certificate derived from integer source data, and a sign-commitment law that refuses rather than guesses |
| Port types | `dyadic` (`numerator / 2^exponent`); `integer_polynomial` as declared algebraic source; `enclosure` as a closed dyadic interval; `separation_certificate`; `commitment` with its ground; `enclosure_deed_input`/`enclosure_deed_output` across the device port |
| Event occurrence | bracket the declared source across the start enclosure; bisect exactly within the declared aperture; derive and independently revalidate the certificate; commit the sign with and without it |
| Predecessor identity | the admitted body at head `14001056`, continuation `15001056`; this movement adds a value-library organ and does not change the continuing body's morphology |
| Local constitutive law | exact dyadic promotion, order, and midpoint; homogeneous integer Horner sign evaluation; reciprocal Cauchy separation; certified zero commitment |
| Receiver question | can a commitment that depends on a quantity no owned carrier represents exactly be made exactly, and what precisely is refused when it cannot? |
| Returned consequence | ten inspected occurrences, exact device/host parity, an independently verified enclosure of an irrational algebraic quantity, a certified zero commitment, its ablation, and four typed refusals |
| Open alternatives | wider limb carriers in place of the 62-bit product aperture; Mahler or Landau separation in place of Cauchy; sign-of-sum certificates for composite algebraic expressions |

## Returned artifacts

**Truth status:** `established-bounded`.

The deed ran on the resident card at compute capability `8.9`, crossing `1120` bytes to the device
and `640` bytes back across `64` launched threads over ten declared occurrences.

- `device_host_parity_failures=0` — every returned structure is bit-identical between the device
  kernel and the host path running the same law.
- `independent_oracle_failures=0` — a separately written host oracle, summing explicit terms rather
  than transporting a Horner accumulator, confirmed every returned enclosure, certificate, and
  commitment consequence. The oracle declares its own aperture and refuses rather than wrapping;
  a refusal is counted as a failure, never as agreement.

### The certified enclosure

The positive root of `x^2 - 2` is not representable in any owned exact carrier. Twelve exact
bisections returned

```text
[181/2^7, 5793/2^12]
```

whose endpoints bracket that root, verified independently. Sixty-four requested bisections returned
`aperture-refused` at exponent `29` while retaining the last admitted enclosure
`[189812531/2^27, 759250125/2^29]`. **The aperture refusal is a returned artifact, not a failure:**
the organ names the exponent it could not prove and keeps the standing it did establish.

### The certificate

**Truth status:** `proved-standard` for the bound; `implemented-exact` for its derivation.

For an integer source with nonzero constant coefficient `b_0` and remaining height
`M = max_(i>=1) |b_i|`, every root satisfies

```text
|root| >= |b_0| / (|b_0| + M),
```

because the reversed source bounds `1/root` above by `1 + M/|b_0|` under Cauchy's bound. When the
constant coefficient vanishes, zero is a root of the declared source and the bound is taken on the
exactly deflated source. The certificate is therefore the statement:

> every root of the declared source is either zero — and only when `admits_zero` — or has magnitude
> at least `numerator / denominator`.

It is derived from integer coefficients alone. It is not a tolerance, not an error estimate, and
not a bound on an approximation. Every returned certificate was independently revalidated against
its source; a certificate with a single incremented numerator is refused as `certificate-underived`.

### The commitment carried by the certificate

`x^3 - 2x` has roots `-sqrt(2)`, `0`, and `+sqrt(2)`. Bisecting from `[-1/2, 1]` produces an
enclosure that straddles zero at every depth and will do so forever: at eight passes it is
`[-1/2^9, 1/2^8]`, and refinement alone can never decide the sign. The derived certificate carries
`separation = 2/3` with `admits_zero = 1`. Because the enclosure lies strictly inside `(-2/3, 2/3)`
and the only root of magnitude below `2/3` is zero, the commitment is **exactly zero**, on the
ground `certified-zero`.

### The ablation

**This is the movement's declared falsifier and it holds.**

The same source, the same start enclosure, and the same eight passes, with the certificate
withheld, return the **identical enclosure** `[-1/2^9, 1/2^8]` and the commitment `refused` on the
ground `separation-absent`, with `certificate_consulted = 0`. No refinement depth reaches a zero
commitment through the uncertified law. The certificate is doing the work, and its removal removes
exactly the claimed consequence.

### The typed refusals

| Occurrence | Return |
|---|---|
| `separation-insufficient` | the enclosure `[-1, 1]` is not yet inside the separation; refused with the ground naming what is missing |
| `source-contradiction` | `x^2 - 2` on `[-1/4, 1/4]`: no bracket, and the certificate proves the source has **no** root of that magnitude — a stronger return than an absent sign change |
| `certificate-underived` | an empty source yields no bound; the commitment is refused rather than defaulted |
| `enclosure-disordered` | a pair whose lower endpoint exceeds its upper is not a set, and nothing may be committed about what it would have enclosed |
| `exact-dyadic-root-collapse` | `2x - 1` collapses exactly to `[1/2, 1/2]`; an exact root is returned as an exact point, not as a tight interval |

## Apparatus finding

**Truth status:** `established-bounded`. **Evidence:** `computational-witness`.

Sixty-four-bit integer division is float-reachable on this architecture. NVCC lowers `/` on
`int64`/`uint64` through `__cuda_sm20_div_u64`, whose Newton iteration begins with
`I2F.U64.RP` / `MUFU.RCP` / `F2I.U64.TRUNC`. The binary SASS audit correctly refused the first
compiled cubin for this reason.

**No integer division may appear in the device-reachable cone.** Overflow admission in this organ
is therefore division-free, by bit-length: a product is admitted when the summed bit lengths of its
operands do not exceed `62`. The test is conservative by construction — a rejected borderline
product is a declared aperture, never a wrapped value. After the correction the cubin disassembles
to zero forbidden instructions.

This generalizes to every later movement and is the reason the existing `small_rational` carrier
implements division by shifting rather than by `/`.

## Gates

**Truth status:** `established-bounded`.

- Architecture, no-float source, public-container ownership, compatibility-route, derived-identity,
  owner-classification, owner-dependency-DAG, and file-size audits: passed over the complete
  production scan.
- PTX no-float audit: passed. SASS no-float audit: passed, zero forbidden instructions.
- Host conformance under `-std=c++23 -Wall -Wextra -Wpedantic -Werror -Wconversion
  -Wsign-conversion -Wshadow` with address and undefined-behaviour sanitizers: passed with no
  diagnostic.
- Determinism: every occurrence re-executed returns a bit-identical artifact.
- Device profile: `release 13.2, V13.2.78; C++20; sm_89`, unchanged from the pinned build receipt.

## Boundary

This organ owns the enclosure of **one root of one declared integer source**. It does not own
arithmetic on enclosures, algebraic-number arithmetic with resultant-propagated sources, composite
sign-of-sum certificates, Mahler or Landau separation, or any analytic quantity. The certificate's
hypothesis — that the enclosed quantity is a root of the declared source — is supplied with the
value and is not verified by this organ; the commitment is exact **given** that hypothesis, and the
hypothesis is part of the returned testimony.

Nothing here establishes a positive form, a signature, a condensation, or a remainder for a far
population. Those are Movement B and remain `open`.

## Owned files

- `include/holonics/exact/dyadic.hpp`
- `include/holonics/exact/integer_polynomial.hpp`
- `include/holonics/exact/enclosure.hpp`
- `include/holonics/exact/separation.hpp`
- `include/holonics/exact/commitment.hpp`
- `include/holonics/exact/enclosure_deed.hpp`
- `include/holonics/apparatus/enclosure_executor.hpp`
- `cuda/executor/enclosure_executor.cu`
- `apparatus/host/enclosure_deed.cpp`
- `tests/model/enclosure_cases.{hpp,cpp}`
- `tests/conformance/enclosure_host_conformance.cpp`
- `cmake/MovementAEnclosure.cmake`

The returned deed artifact is `receipts/MOVEMENT_A_ENCLOSURE_DEED.txt` in the build tree.
