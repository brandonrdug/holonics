# Affine orbits return composite certificates through finite clocks

[definition] Brandon supplied [José Reyes, *Small Composite Numbers in Orbits of Linear Maps*,
arXiv:2508.18305v1](https://arxiv.org/pdf/2508.18305) during the continuing HNN construction.
This record develops its arithmetic return independently, then connects the actual quotient,
clock and matrix equations to existing Holonics owners. Source inspection began at `be2fc49b`.

## The supplied result

[proved-standard; source-inspected] Reyes studies `f(z)=az+b`, with positive coprime a,b and
a>1. A rooted prime chain excludes z and ends before the first composite iterate. Theorem 2
bounds its length by `<z` when gcd(a,z)=1. Theorem 3 gives the same bound for every
`z>M=b(1+a+...+a^(k+1))`, where k counts the distinct prime divisors of a. Its backward
numerators `s_i=z-b(1+a+...+a^(i-1))` expose divisors outside those of a; prime-adic valuation
stabilization proves their availability above M. The example a=2,b=3,z=32 first reaches a
composite at the seventh iterate, `4477=11*407`. These are bounds on initial prime runs,
not a result about the Riemann hypothesis or a general prime-density formula. The linked
paper supplies the second theorem's valuation argument; it is not formalized by the new leaf.

## A factorization-free derivation

[proved-derived; formal-checked] Put `q_d(x)=x mod d` and `U_d(r)=ar+b mod d`. Then

`q_d f = U_d q_d`, hence `q_d f^n = U_d^n q_d`.

When gcd(a,d)=1, U_d is injective on the d-element residue space and therefore a permutation.
Every state has a positive return period at most d. In particular, when d=z>1,
`q_z(z)=0`, so some `1<=n<=z` satisfies `z | f^n(z)`. Since a>1 and b>=0,
`f^n(z)>z>1`. Thus z is a proper divisor of that iterate. The initial prime chain has
length `<z`. This proof needs no factorization of z, no prime divisor selection, and no
coprimality assumption on a,b. It also permits b=0. This is a derived proof and mild
hypothesis generalization, with no claim of historical priority.

[proved-derived; formal-checked] The source is
[`Mathematics/AffineOrbitDivisor.lean`](../../formal/elementary-holonics/ElementaryHolonics/Mathematics/AffineOrbitDivisor.lean),
imported by `Framework.Dynamics`. Its namespace is `Soma.Holonics.Mathematics.AffineOrbitDivisor`:

- `finite_injective_return`: a fixed injective action on any finite state space has a
  positive return clock bounded by its cardinality.
- `natAffine_mod_iterate`: integer reduction commutes with the complete iterated affine action.
- `affineMap_periodic_return`: the residue specialization for a coprime multiplier.
- `natAffine_iterate_strict_growth`: positive-root growth for a>1,b>=0.
- `natAffine_proper_divisor_certificate`: modular zero plus `1<d<=z` and positive clock
  certifies compositeness; d need not be prime, and this certificate theorem needs no
  coprimality hypothesis or clock upper bound.
- `natAffine_proper_divisor_return`: the stated factorization-free existence bound for d=z.

[definition] Lean verifies these exterior mathematical statements. The executable construction
below finds or checks an actual clock; it does not invoke Lean or execute a choice-defined period.

## Composite moduli and backward phase

[proved-derived] The prime restriction is unnecessary for the clock argument. Suppose
`1<d<=z`, gcd(a,d)=1, and `z=f^i(0) mod d`. Then z lies on zero's cycle. If its period is L,
the positive zero-return times from z are exactly

`n+i = 0 mod L`, with least positive n in `{1,...,L}` and `L<=d`.

At any such clock, d divides `f^n(z)` and strict growth makes it a proper divisor. This
identifies a whole congruence class of composite terms; it does not identify the first
composite term detected by every possible divisor.

[proved-derived] For a backward numerator s_i>1, repeatedly divide its current value by
its gcd with a until the gcd becomes one. If the remainder d exceeds one, then
`d|s_i`, gcd(a,d)=1, and `z=f^i(0) mod d`. Every nontrivial division reduces the integer,
so the construction terminates without prime factorization. If it strips to one, move to
the next numerator. For positive b, the numerators strictly decrease; stop with the signed
boundary value when it is <=1. Under the supplied paper's large-root hypotheses, its
divisor-existence theorem ensures a successful numerator before this boundary. Outside
those hypotheses, failure of this route says nothing about primality of all future terms.

[established-bounded; implemented-exact] The existing `arithmetic_phase` application now owns
[`affine_orbit.rs`](../../crates/holonic-engine/src/arithmetic_phase/affine_orbit.rs). It returns
the source coefficients/root, selected numerator and index, gcd divisions, divisor and clock.
The modular search transfers one continuing state through caller-bounded work apertures.
Its terminal nonzero cycle is explicit. No whole integer trajectory is retained.

| Source | Returned arithmetic |
|---|---|
| a=2,b=1,z=5,d=5 | n=4; `f^4(5)=95`, with proper divisor 5. |
| a=6,b=1,z=316 | `s_1=315`, gcd stripping `315/3/3=35`; modulo 35 returns zero at n=9. An earlier composite can have another divisor. |
| a=2,b=1,z=9 | `s_1=8` strips to one; `s_2=6` leaves d=3, returning n=2 and `f^2(9)=39`. |
| a=2,b=1,z=`7*2^200+1`,d=7 | Residues `1 -> 3 -> 0`; n=2, with the full large root retained in the certificate. |
| a=2,b=1,z=13,d=7 | Residue 6 is fixed. Search returns exhaustion for this modulus; it makes no prime-only claim. |

[proved-derived] Affine composition is
`(A,B) after (C,D) = (AC, AD+B)`. Binary powering computes `U_d^n` in O(log n) modular
compositions, keeping all arithmetic modulo d. Verification additionally checks the
positive-growth/source/divisor bounds. Search by successive residues costs at most d
steps, which is a value bound and may be exponential in the input bit length. These are
different operations and costs. In the special translation case a=1 modulo d, b=1 and
z=d, the return clock is exactly d by `U_d^n(0)=n mod d`; that clock is derived directly.
The implementation test verifies this law at d=`2^200+1` without traversing the cycle.

## Affine groups, the golden clock and Smith transport

[proved-derived] The homogeneous matrix and shifted coordinate are

`F = [[a,b],[0,1]]`, `u=(a-1)x+b`, `u(f(x))=a*u(x)`.

Over a prime residue field with a nonzero, if a!=1 this coordinate change is invertible
and gives a multiplicative clock dividing p-1. If a=1 and b!=0, the map is a translation
with period p: the two eigenvalues of F coincide and its nonzero nilpotent part carries
the clock. This is the same affine-group structure already used by
[`arithmetic_monodromy`](../../crates/holonic-engine/src/arithmetic_monodromy.rs) to constrain
prime-degree Galois groups. The new arithmetic proof does not infer a Galois group from
an arbitrary orbit.

[proved-derived] There is a specific connection to the earlier golden-ratio clock.
For `A=[[1,1],[1,0]]`, the real eigenvalues are phi and `-1/phi`. Modulo 5,
`A=3I+N`, where `N=[[3,1],[1,2]]`, `N^2=0`, and N has nonzero off-diagonal entries.
Consequently

`A^n = 3^n I + n*3^(n-1)*N mod 5` for n>=1.

Identity requires 5|n from the off-diagonal entries, and then 4|n from the order of 3
modulo 5. Conversely n=20 satisfies both, so A has order exactly 20. The same integer
matrix thus has golden spectral directions in one chart and a clock with a nilpotent
part in another. This does not equate phi, a finite period or a transcendental constant.

[proved-derived] Joint clock addressing is an integer-lattice problem. Given retained
period/phase pairs `(L_j,i_j)`, simultaneous zero returns solve `n-L_j*k_j=-i_j`.
For two periods, existence is exactly `i_1=i_2 mod gcd(L_1,L_2)`. The complete integer
system's image/cokernel, rather than a discarded scalar mismatch, describes the general
obstruction. The existing
[`rebase_invariants`](../../crates/holonic-engine/src/rebase_invariants.rs) Smith owner and
[`phase_clock_smith`](../../crates/holonic-engine/examples/phase_clock_smith.rs) already
provide the corresponding invariant-factor and finite-clock constructions.

[proved-derived] More generally, for a finite quotient `Q=Z^r/L`, an affine action descends
when its linear part preserves L, and is a permutation when the induced linear part is
invertible. Its fixed-action return bound is |Q|. If the full-rank lattice presentation has
positive Smith factors d_j, then `|Q|=product_j d_j`. This generalizes the residue count;
a coordinate's compositeness additionally needs its own divisor and growth comparison.
The existing `Foundation/LatticeTransport.lean` retains the image, cokernel and lift fibres.

## Fixed and changing dynamics

[counterexample] Per-step invertibility alone does not imply return to the initial state.
On `{0,1}`, first swap the two states and then use identity forever. Starting at zero
gives `1,1,1,...`. Every individual map is invertible; their changing sequence is not the
one fixed permutation used by the finite-return theorem.

[proved-derived] A periodic schedule of k permutations *can* be lifted to the fixed action
`(x,t) -> (T_t(x), t+1 mod k)`. Its inverse is
`(y,s) -> (T_(s-1)^(-1)(y), s-1)`, so the lifted return clock is at most k|Q|.
This is why clock, phase and constitutive conditions belong in the state when they affect
continuation. An arbitrary evolving material need not have a finite periodic lift.

[proved-derived] Reduction retains all futures *at the residue receiver* because `q_d f=U_d q_d`.
Primality itself does not factor through that quotient: zero residue can describe zero,
d, 2d or many other integers. The retained inequality `1<d<f^n(z)` supplies the specific
proper-divisor conclusion. This composes the existing future-receiver principle without
identifying equal residues with equal causes.

[definition] The HNN consequence is the scope of the compiled action: a fixed forecast law
supports its declared future family, while changing material/conditions must participate
in the source/action map. This is the same obligation already recorded in the
[boundary/interior construction](2026-09-13_BOUNDARY_AND_INTERNAL_CURRENTS_FEED_JOINT_HNN_PREDICTION.md),
not a new prerequisite for that empirical-return binding. This arithmetic application is
an exterior exact reference; no new native learning law or fixed finite-state assumption
is imposed on HNN by the paper.

## Verification

[established-bounded; measured] Exact commands and output are retained under
`.local/artifacts/2026-09-13-affine-orbit/`. The final Cargo suite covers the coprime-root
bound, composite modulus, later numerator escape, transferred continuation, nonzero-cycle
exhaustion, malformed source/clock/divisor, direct-integer comparisons over bounded input
families, and binary verification of a 201-bit clock. No CUDA semantic operation was changed;
these arithmetic tests execute on the CPU.

| Check | Returned result |
|---|---|
| `cargo test -p holonic-engine --lib arithmetic_phase::affine_orbit -- --nocapture` | Seven passed, zero failed; test execution 0.01 s, final incremental build 41.88 s. |
| `./check.sh ElementaryHolonics.Framework.Dynamics` | Passed under the pinned toolchain, including the new leaf and changed subject import. Existing replayed warnings and two style suggestions on local instance bindings remain warnings. |
| 201-bit translation certificate verification | One `Instant` elapsed observation: 193181 ns. This includes verification of the supplied law-derived clock; it is not a search benchmark or GPU measurement. |

[definition] The unfinished HNN family-enclosure draft was preserved outside live source at
`.local/recovery/2026-09-13-family-enclosure-draft/` after review found numerical-bound and
workspace-lifetime defects. Its four modified tracked owners were restored to `be2fc49b`;
the new files and full patch remain recoverable. That helper and the consuming empirical
return are not presented as completed by this arithmetic increment.
