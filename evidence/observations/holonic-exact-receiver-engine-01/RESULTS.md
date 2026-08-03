# HOLONIC EXACT RECEIVER ENGINE 01

**2026-07-26 · ACCEPTED EXACT CPU REFERENCE / NO FLOAT / NO BEVY / NO VULKAN**

## Question

Can one caused relational complex determine the complete ordered crossings in a
finite participating receiver face without an absolute camera, manually injected
screen shapes, or a floating-point graphics pipeline?

## Physical cut

The world contains two triangle faces in two distinct source frames. Each source
supplies an exact declared translation into the receiver's frame. One central
receiver has:

```text
aperture: 5 × 3
exact face span: 2 × 2
ray family: central
receiver-local forward: (0,0,1)
```

The near source enters at receiver depth `2`; the far source enters at depth `3`.

Command:

```text
cargo run -q -p holonic-engine --example exact_receiver
```

## Exact output

```text
schema=holonic-engine.visibility-receipt.v1
aperture=5x3 exact-span=2x2
work rays=15 triangle-tests=30 crossings=9
near-visible-pixels=4 far-visible-pixels=5
pixel=(2,0), face=(0,2/3) t=2:[1] t=3:[2]
pixel=(1,1), face=(-2/5,0) t=2:[1]
pixel=(2,1), face=(0,0) t=2:[1] t=3:[2]
pixel=(3,1), face=(2/5,0) t=2:[1]
pixel=(1,2), face=(-2/5,-2/3) t=3:[2]
pixel=(2,2), face=(0,-2/3) t=3:[2]
pixel=(3,2), face=(2/5,-2/3) t=3:[2]
representative-fiber work=4 causal-span=3 exposed-width=2
```

The center and upper-center aperture members retain both crossings in correct
order. Empty members remain empty. No nearest-face or color rule is smuggled into
the geometry.

The representative fiber is:

```text
receiver ray
    -> {near incidence test, far incidence test}
    -> ordered crossing fiber
```

The two incidence tests are logically co-present even if a CPU physically executes
them serially.

## Verification

```text
cargo test -p holonic-engine
13 passed / 0 failed / 0 ignored
```

The tests cover categorical boundary composition and refusal, causal antichains and
cycle refusal, atomic world-event refusal, exact energy evaluation and incomplete
model refusal, exact pixel-center/aspect ratios, declared frame transport, receiver
orientation, exact barycentric crossings, plural same-depth crossings, and ordered
multiple-depth layers.
An additional display-membrane test establishes that RGB packing occurs only after
an explicit pixel transducer receives the complete fiber.

## Grade

The exact CPU reference is **accepted** for this bounded cut. It establishes a
causal visibility receipt, not yet a complete display engine or physical world
law. No host/card claim is made.
