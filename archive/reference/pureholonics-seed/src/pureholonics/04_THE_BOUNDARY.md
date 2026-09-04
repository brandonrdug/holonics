# 04 · THE BOUNDARY — the FTC completed, Β, the two faces, the gyre

> The keystone. Newton/Leibniz built the flat, path-independent shadow; Einstein corrected the physics but never
> re-founded the mathematics; the computational dynamics were unthinkable until thousands of parallel channels
> existed. Holonics completes the Fundamental Theorem of Calculus — and names the fundamental measurement.

---

## The re-defined LIMIT — soul-determined

Classical analysis *demands* path-independence ("the limit exists iff every approach agrees"). That demand IS the
assumption of trivial cohomology. Holonics drops it: **the limit is the resolution the trajectory (the soul)
reaches** — grounded by the swing (`simplest_near`). Because the cohomological part is real (the saddle, §03),
the value genuinely depends on the path. The classical limit is the curl-free special case where all souls agree.

## The theorem — generalized Stokes ⊕ the cohomology

```
∫_M dω = ∫_∂M ω   ⊕   [ω] ∈ H•(M)
```

The classical FTC `∫f' = f(b)−f(a)` keeps only the **exact** part (the coboundary, trivial cohomology — "the ant
queen integrating"). The full statement is the **generalized Stokes theorem** at every dimension (FTC in 1-D,
Green/Stokes the curl in 2-D, the divergence theorem the flux in 3/4-D — **Maxwell's equations ARE it**, `dF=0`,
`d⋆F=J`) **plus** the part Stokes alone misses: the **closed-but-not-exact** form (`dω=0`, `ω ≠ dη`) = de Rham
cohomology = the holonomy = the curl = the gyration = **the SOUL = the path-dependence**. The FTC is the *whole*
of it. It innately composes E/M (the exact gradient `Re h` at rest vs the cohomological curl `Im h` in motion —
the frame selects the face), the chain rule (= change of basis = the connection), and the 4-volume divergence
theorem (`∫_V ∇·T = ∮_∂V T·dA` — the output is the surface integral of the interior's rate of change; `∇·T=0` is
why the global boundary is content-blind, the content read locally on the surface).

## THE UNITS — the first direct link from ENERGY to INFORMATION

Base: **`𝗜` = bits** (information = action), **`𝗧` = ticks** (lineage — one event of succession, *not* "time");
the one conversion **`c = bits/tick`** (the speed of light = channel capacity).

| object | unit | the FTC reading |
|---|---|---|
| **action `S`** = code length `Σ −log q` | `𝗜` | what is accumulated (the integral) |
| **energy `L`** (rate of action) | `𝗜𝗧⁻¹` | the integrand (the rate of change) |

So the FTC in units is **`∫(dS/dt) dt = S`** — `(𝗜𝗧⁻¹)(𝗧) = 𝗜`, the ticks cancel. *Energy integrated over the
lineage = action; bit-rate accumulated over the worldline = the bits.* The same statement — the FTC is the bridge
from energy to information. And **`E = mc²` closes in these units**: `m = E/c² = 𝗜⁻¹𝗧` (ticks per bit — the
persistence/inertia of a bit; mass is the standing vortex of slowed light, *mass is where information re-bases*).
The first time `E=mc²` is written in units of information.

## THE PIVOT — the frame-derivative of Β (the moving boundary)

A frame is the third body (A2) — a moving origin ⊕ a boost — and as it advances, the endpoints sweep. The
classical FTC holds the boundary fixed; the realized FTC keeps the motion, and that motion is the **PIVOT** (the
relativistic Leibniz rule, differentiation under a moving boundary). Read by the order of `d_F`: `Β` is the static
**face** (a value); `d_FΒ` the **rate of change** (the meaning, the light); `d²_FΒ` the **gyration** (the soul's
curvature). *Generation is the FTC of the chain of pivots run forward.* The Zeno re-base **cancels to leading
order (the boost)** — and what survives is exactly the **gyration** (the cohomological term, the soul): the flat
"δ cancels" is the exact part `dη`; the gyro correction is the cohomology `[ω]`. (Machine-checked across
`Holonics.lean`/`Gyro.lean`/`Gyration.lean`.)

---

## Β — the relativistic boundary operator (the notation)

`Β_a^b[λ]_F` — *wind the relating `λ` (a pole: a turn ⊕ a rank) from reference `a` to boundary `b`, read in frame
`F`* — returns a **holon**, not a number. It is non-commutative (the order is the soul), framed (three-body),
two-faced (never one scalar), and founding (it branches). Encode/decode are its `∂` and `∫`: `∂Β =
between(θᵢ,θᵢ₊₁)` (the encode, the velocity, the kink/foil), `Β = ∫∂Β` (the decode, the text, the winding, which
telescopes). The whole machine is one expression: a tensor (parallel channels `⊗`) of nested (`Δ<0 ⇒` found one
rank up) seamed (`⋈`) boundary-operators, each winding and either **closing** (the collapse) or **founding** (a
new rank). Σ, Π, ∮ are its flat special cases.

## THE FUNDAMENTAL MEASUREMENT — the 2-vector (holobit ⊕ cohobit)

The two faces of `Β`, named and read as a pair (never collapsed — the "never one scalar" law is the *type* of the
measurement):

```
resolution = ( holobit , cohobit ) = ( |Β| , ∠Β ) = ( magnitude/cost/curvature , signed direction/coherence )
```

- **`|Β|` = the HOLOBIT** (the `e`-face): a **magnitude** — bits-of-cost, the 4-volume, how much information
  separates reference from cursor. The **COST of looking** (shining light is a force). It reflects curvature ⊕
  demand. It is a **measurement, never a trigger — a thermometer, never a thermostat** (founding is gated on the
  discriminant, NEVER on the holobit). Compress = minimize it (the hexis, holobit → 0).
- **`∠Β` = the COHOBIT** (the `π`-face): the **signed** relative DIRECTION — the moiré `M = cosθ`, the curved
  area, the holonomy, the geometric phase. The sign is load-bearing (never `abs`'d): **`+` cohere** (align), **`−`
  annihilate** (oppose), **`≈0` dark** (orthogonal, looked-past, free). The holobit says *how much*; the cohobit
  says *which way ⊕ how coherently*.

`area = √volume` (the holographic ½; RH is exactly that the `π`-face `~√n` is the square-root of the `e`-face
`~n`). The 2-vector is the full holographic **measurement** (the RADIATION — the most you can read); the oriented
**path** it faces (between oriented poles `a,b`, read by an oriented frame `F`) is the gauge **SOUL** — the
handedness the signed scalar drops. *Read the 2-vector; infer the path; never claim the soul.* The gap between
them is the horizon, not a limit of the notation.

---

## GYRATION IS ACTION — the gyre, the relativistic unit (the latest layer)

Physical action is a loop integral `S = ∮ p dq`; by Stokes it IS the enclosed area; and the gyration IS the
curved area (Gauss–Bonnet). Therefore **`S = ∮ p dq = ∬ (curvature) = the GYRATION`** — action is not *like* the
gyration, it **is** the enclosed gyration. So:

- **the cohobit IS the action** (`∠Β` = the signed curved area = the gyration = `S`); the holobit IS the energy
  (`|Β|` = the cost = `E`). The 2-vector reads `(E, S)` — energy ⊕ action — the same `e ⊕ π` pole, measured.
- **founding spends action (the cohobit/gyration), never energy (the holobit)** — a thermostat on energy is the
  contamination; the discriminant is action.
- **action is BITS** (the curved area = bits, §07's Duggan) — `S` and information are the same quantity, which is
  why `ħ` and `k_B ln2` are both "the grain." The **GYRE `𝔾`** is the relativistic unit: one signed quantum of
  closed-loop curved area = one bit of holonomy = the action of one complete relating (`ħ ≡ 1 𝔾`). The
  *closed-loop* gyre is frame-invariant (the cross-ratio its invariant); its *open-segment* face is the
  frame-relative cohobit. Count gyres *between two events*, re-based at the moving origin, never "from 0."
- **the two faces are FRAME-DISTINCT** (Eros corrected this): the holobit (magnitude/mass) is **COMMUTATIVE**,
  frame-invariant, and *meaningless alone*; the cohobit (alignment/action) carries the handedness in `W⁻` and is
  **ANTI-COMMUTATIVE** (`W⁻(a,b) = −W⁻(b,a)`). Commutativity is **not absolute** (gyrocommutative — commute on
  the holobit, never the cohobit; decidable per frame). So founding **GATES on the cohobit** (commutatively),
  **WEIGHS the holobit** (the mass that elevates, §06; gating on both over-restricts and degrades), and
  **CARRIES the handedness in the order**. **The `W⁻` "annihilate" pole is CONVERSION, never destruction** — the form
  transforms ⊕ the difference radiates, inseparably (`E=mc²`, the mass defect IS the radiation), conserved and never
  deleted. It is the **TRANSFORMER** (§07): fusion ⊕ fission ⊕ annihilation are one spin-axis (the cohobit `M` the
  efficiency; anti-alignment `M=−1` the 100% premium); "annihilation" is a misnomer (fusion/fission = partial annihilation).

> **The writhe is the contamination** (`Lk = Tw + Wr`, Călugăreanu): the linking number `Lk` is the topological
> invariant (frame-free); the twist `Tw` and writhe `Wr` trade at fixed `Lk` and are frame-relative. Reading the
> writhe alone is the contamination thrice over — absolute-frame, comparing-the-soul, self-feed-runaway. **Read
> the linking `Lk` (the action, the conserved crossing); the writhe is its gauge face, inferred, never claimed.**

---

> **§04 in one line:** *the completed FTC is generalized Stokes ⊕ the cohomology (the soul-determined limit, the
> path-dependent holonomy the ant integration missed), carrying real units (`∫(dS/dt)dt = S`; `E=mc²` with mass
> the persistence of a bit), its PIVOT the frame-derivative of the boundary operator Β, the Zeno re-base
> cancelling to the boost with the gyration surviving as the cohomology; Β returns the fundamental 2-vector
> measurement `(holobit, cohobit) = (energy, action)` — never one scalar; and GYRATION IS ACTION (the gyre `𝔾`
> its frame-invariant quantum), so founding gates on the cohobit, weighs the holobit, carries the handedness, and
> reads the linking `Lk` never the writhe.*
