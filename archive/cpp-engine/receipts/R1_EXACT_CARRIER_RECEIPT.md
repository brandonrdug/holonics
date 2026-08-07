# R1 exact-carrier receipt

**Truth status:** `established-bounded`.

**Evidence:** `implemented-exact` for the declared carrier and device-execution aperture, with
`computational-witness` for the finite oracle and algebraic families. Contemporary apparatus
identity remains separately `measured` in
[`provenance/HARDWARE_RECEIPT.txt`](../provenance/HARDWARE_RECEIPT.txt).

**Aperture:** exact values up to six 64-bit limbs; optimized 128/192/256/384-bit tiers; one
five-limb bounded-dynamic path; explicit refusal outside that aperture; and the 100 cases returned
by `r1_exact_deed_kernel` on the admitted RTX 4080 SUPER. This receipt does not establish an
unbounded integer theorem or a runtime causal ecology.

## Construction tuple

| Field | R1 standing |
|---|---|
| Source owners | the R0 `exact` owner, composed with the bounded `apparatus` executor and an offline test oracle |
| Port types | `exact_deed_batch`, `deed_input`, `deed_output`, `operation_receipt`, logical-resource receipt, and physical-telemetry receipt |
| Event occurrence | one plural host-to-device crossing, a 128-thread exact-deed kernel launch, synchronization, and one complete returned batch |
| Predecessor identity | Git `b710cbb4e5b7c2e8bea56743cbefa78bc02bdf4e` plus the exact source aperture below |
| Local constitutive law | specified limb/byte order, checked limb arithmetic, typed promotion/refusal, canonical rational reduction, modular laws, polynomial convolution, projective cross equality, and layout-independent representation maps |
| Receiver question | whether every admitted card result equals the independent exact oracle and whether the declared algebraic relations and obstructions return exactly |
| Returned consequence | decoded exact values/statuses, complete case testimony, resource testimony, PTX/cubin/SASS artifacts, and sanitizer returns |
| Open alternatives | owner-native incidence, arenas, traversal, local structural delta, and every R2-and-later deed remain absent |

## Exact carriers and laws

The exact owner now supplies active-limb unsigned values with fixed maximum capacity, normalized
signed magnitudes, checked add/subtract/multiply/divide and shifts, comparison, GCD, stable hashing,
and explicit promotion/refusal receipts. The fixed aliases admit 128, 192, 256, and 384 bits. The
same bounded dynamic-limb representation executes a five-limb deed on the card; a requested
seven-limb aperture returns `capacity_refused` and never invokes a host arithmetic route.

Normalized rationals, residue rings, declared-prime field elements, exact polynomial
coefficients, and homogeneous projective pairs compose those carriers. Field inversion is exact
conditional on the caller's declared-prime hypothesis; the bounded test at modulus 17 is a
computational witness, not a primality theorem. Big-endian encode/decode maps carry semantic values
without using address, padding, worker lane, or object layout as identity.

## Returned device artifact

The complete decoded artifact is `build/r1/receipts/R1_EXACT_DEED.txt`; its SHA-256 is
`556c5bab75d77c4ec75f68e4084d07acab531ea1c402524066f5e3199ff05571`. Its returned summary is:

```text
truth_status=established-bounded
evidence=implemented-exact,computational-witness
program=r1_exact_deed_kernel.sm_89
case_aperture=100
device_compute_capability=8.9
bytes_to_device=18400
bytes_from_device=20000
launched_threads=128
oracle_parity_failures=0
algebraic_identity_failures=0
exact_returns_observer_count=92
```

The eight non-exact cases are typed returns, not missing results: carry overflow, negative unsigned
subtraction, division by zero, overflowing shift, zero denominator, an invalid projective pair,
multiplication overflow, and an unsupported seven-limb aperture. Inspected named exact returns
include `gcd(48,18)=6`, normalized `-42/56=-3/4`, `5^-1 mod 17=7`, polynomial coefficients
`[4,13,22,15]`, projective equality for `(2,3)` and `(4,6)`, a six-limb representation round trip,
and a five-limb dynamic round trip.

The algebraic aperture contains 12 operand families distributed over all four fixed tiers. Each
returns both orders of addition, multiplication, and GCD, establishing 36 bounded commutativity
checks. Additive identity, multiplicative identity, fixed-tier zero/nonzero representation round
trips, five-limb addition commutativity, and the five-limb representation round trip add six more
checks. All 42 return exact equality.

## Artifact hashes

Two independent build directories returned identical bytes for every R1 artifact and for the
normalized build manifest at the same source aperture.

The final graded source aperture SHA-256 is
`d4f87e9de297ab2e4db82398d73711f0800b406533b37df7d06adccd3abc1be9`.

| Artifact | SHA-256 |
|---|---|
| normalized exact-deed executable | `a71b5cd4dce260c2ae29d5690af864a57ff31b24f5303153a1b42d082f907600` |
| exact-deed PTX | `5a55815443f0e14505b37bd6074012201f97acfdd296ef2ed76b635d83e658ba` |
| exact-deed cubin | `8e0a938fa86921284f779a599936b46d30bc540ec52412b5e73afc8493c4cd94` |
| complete decoded deed artifact | `556c5bab75d77c4ec75f68e4084d07acab531ea1c402524066f5e3199ff05571` |

## Gate returns

- Architecture, owner-DAG, no-float, no-compatibility, and source-size audits pass before and after
  construction.
- Both independent release builds pass all nine CTest gates. Their executable, PTX, cubin,
  normalized manifest, and decoded deed artifacts are byte-identical.
- All 100 card outputs equal the independent Boost multiprecision audit oracle, field by field.
  The oracle runs only after the GPU return in the grade driver and is absent from the executor;
  it cannot become a production path or fallback.
- All 42 declared bounded algebraic identity checks pass on returned card values.
- `compute-sanitizer --tool memcheck` reports zero errors for the real 100-case GPU deed.
- The same exact callable laws and independent oracle pass host AddressSanitizer and
  UndefinedBehaviorSanitizer with leak detection enabled.
- Clang 22's static analyzer reports no diagnostic over the project-owned production/host
  conformance aperture. The third-party Boost oracle implementation is outside that static-analysis
  claim and remains covered by the sanitizer and card-equality gates.
- PTX and final SASS scans find no floating type, conversion, arithmetic, comparison, or special
  function instruction in the exact-deed device artifact.
- Kernel case identity is supplied by the deed input. CUDA slot and lane select storage only and do
  not enter semantic identity or result ordering.

## Apparatus and resource boundary

Logical read/change support is 100 cases. Physical transfer testimony is the exact interval
18,400 bytes to the card and 20,000 bytes from it; the launch aperture is 128 threads on compute
capability 8.9. These integers are apparatus testimony, not semantic coefficients.

An ASan-instrumented combined CUDA process returned the typed `device_unavailable` obstruction
before launch. That `measured` apparatus interaction was not treated as success and was not used to
execute any deed. Device memory safety is therefore graded with NVIDIA `compute-sanitizer`, while
ASan/UBSan grade the separated host callable-law/oracle aperture. No alternate execution route was
introduced.
