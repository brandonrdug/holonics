# Association is evaluation at conserved faces, and a number's digits are a gas of the base's atoms

**Date:** 2026-10-23. **Occasion:** The design thread had said that Athena's arithmetic was
association rather than evaluation: a result such as 60 after `2*30` was read from contexts it had met.
Brandon answered with three lenses within the hour:
- Association and evaluation are equivalent in compression and navigation. To associate faces is to
  evaluate the constraints and causal potentials that produce them, as with the digits of a mantissa
  and the conservation of faces.
- Arithmetic is learned from the digit and mantissa distributions of many interacting digits, the way
  he does mental arithmetic and recognizes primes. Those distributions are bitwise operations moving
  the parts about each other, and they are the flux relations that association and evaluation compute.
  His example: `9·x` ends in ten minus the last digit of `x` (`9·7 = 63`, `9·23 = 207`). Number theory
  from Fermat on is rebasing and geometry.
- The composition is combinatorial potential and thermodynamics: atoms and their constituent
  ingredients, with binary potentials integrating, used to compose the Fermat ideas. He asked that his
  earlier intuitions on this be reviewed and unified.

**Joins:**
- The faces of a numeral: `radix.leading-fibre` (Lean `Mathematics/RadixWindowReceiver`),
  `radix.trailing-unit-rings`, `radix.leading-rotation-benford`, `radix.cheap-faces` and
  `radix.multiplication-table`.
- The producer and its consumer equation: `radix.digit-convolution`, `radix.carry-cascade-consumer` and
  `radix.carry-section-flux` (Lean `Mathematics/ArithmeticContract`); the
  [arithmetic contract](2026-09-29_THE_ARITHMETIC_CONTRACT_A_NUMERAL_IS_A_FACE_OF_A_COUNTING_NAVIGATOR_AND_ITS_PRODUCER_IS_A_KEY.md)
  and the [helix record](2026-09-28_A_NUMBER_IS_A_HELIX_ITS_BASE_IS_A_FACE_AND_A_FAMILY_WINS_WHERE_IT_IS_CLOSEST.md).
- The carry as a carried residue: `release.carried-residue` (Lean `Foundation/CarriedRelease`) against
  `release.plain-rounding-annihilates`; `ratio.div-rem`.
- The fibre and the joint of residues: `info.preimage-fibre`, `winding.crt-diagonal` and
  `lock.coprime-torus-diagonal`.
- The integers as a gas: `heat.zeta-gibbs`, Lean `Zeta/PaletteLaw` (the Euler product as a Fock
  factorization) and `Mathematics/PrimeSimplex` (Möbius as fermion parity), with the primon-gas readings
  of Brandon's October 15 conservation-of-faces lens.
- Binary potentials coupled: `parametron.coupled-locks-lee-yang` (Lean `Objects/ParametronLock`).
- The ring's partition function: `navigator.zeta`, `aeon.zeta-exp`, `aeon.zeta-map-periodic-points`,
  and `landmark.primitive-cycle-count` with `landmark.euler-product` (Lean
  `Compression/Landmark/PrimitiveCycle`, which proves the count and the Euler product for a map).
- The [code-length record](2026-10-23_CODE_LENGTH_IS_A_FIELD_ITS_FLOOR_IS_THE_DARK_ENERGY_TERM_ITS_BINDING_SHOWS_ONLY_THROUGH_CONTACTS_AND_THE_PRIMES_HAND_SITS_ON_THE_FLOOR.md),
  whose lens is measured in §3 and whose §2 and §6 are corrected in §6.

**Truth discipline:**
- `[proved-standard]` marks a classical result, `[proved-derived]` a short derivation given here,
  `[measured]` an exterior reading with its receipts, `[interpretation]` a correspondence and
  `[design]` a consequence for Athena.
- The fibres, digit laws and congruences are exact integer and rational checks. The code lengths are
  exterior float reads.

## 1. Association is evaluation `[proved-derived]`

An operation is a constraint, the graph of `T : X × X → X` (a sum, a product, a difference). A
**face** is a receiver's quotient `q : X → F`: the last `k` digits, the leading `k` digits with the
length, the digit sum, a residue.

- **Association at faces.** To associate faces `f` and `g` of the operands with a face of the result is
  to read the set of result faces the constraint admits, `Fib_q(f, g) = q(T(q⁻¹f × q⁻¹g))`. Until it
  closes, it is a plural Preimage Fibre (`info.preimage-fibre`).
- **A conserved face.** `q` is conserved by `T` when every such fibre is one point. Then there is a
  `T_q` with `q ∘ T = T_q ∘ (q × q)`: the operation descends to the face, and `T_q` is the face's own
  operation.
- **Evaluation.** To evaluate `T` at `(x, y)` is to associate a family of faces that is jointly
  injective on the result's range. Its fibre in `X` itself is one point.

So evaluation is association whose fibre has closed, and association is evaluation that keeps its
fibre. In compression, a result costs at most `log₂ |Fib|` given the associated faces. In navigation,
each face added intersects the preimages and narrows the fibre, and the paths converge on the value
where it closes, a landmark. Brandon's equivalence holds in both.

What separates an associator that reaches unmet operands from one that does not is not the act. It is
whether the faces it associates are conserved by the constraint, and whether their operation `T_q` is
small enough to be met often.
- A whole calculation read as one string is a jointly injective face, so reading it is evaluation. But
  its `T_q` is `T` itself, one entry per string, and is known only on the strings met.
- The conserved faces of arithmetic are few and small. The trailing face mod `b` has the `b²`-entry
  multiplication or addition table as its `T_q`, and that table is met on every calculation. Radix
  arithmetic factors `T` through these faces: a carry-free pair combination at each place followed by
  one carry cascade (`radix.carry-cascade-consumer`), so a product is a convolution of place faces and
  a carry (`radix.digit-convolution`).

Under a description-length objective, the factored description is the shorter once the distinct
calculations outnumber the faces' tables, a few hundred entries in base 10. A learner that compresses
enough arithmetic must therefore come to evaluate at these faces `[interpretation: the count is an
order of magnitude, not a bound]`.

## 2. The faces of a number, and which operations keep them `[proved-standard; proved-derived where marked]`

A number is a helix ([helix record](2026-09-28_A_NUMBER_IS_A_HELIX_ITS_BASE_IS_A_FACE_AND_A_FAMILY_WINS_WHERE_IT_IS_CLOSEST.md)):
`log_b x = k + θ`, with the length as its winding and the mantissa `θ` as its phase on the base's log
circle.

| face | sum | product | difference |
|---|---|---|---|
| trailing, `x mod b^k` | exact | exact | exact |
| leading, `θ` read at `j` digits | up to the carry fibre | rotation by `θ(y)`, up to the carry fibre | not conserved (cancellation) |
| length | up to one carry | `k_x + k_y`, up to one carry | not conserved |

- **The trailing face** is a ring homomorphism, so the carry flows up and never down
  (`radix.leading-fibre`).
- **The leading face of a product** is the sum of the mantissas on the circle, with the winding
  carried into the length (`radix.leading-rotation-benford`). Read at `j` digits it is exact only up to
  the fibre that the unread lower places send up (`radix.leading-fibre`). The digits of a mantissa are
  this face's expansion: each further digit is a finer face, and associating more of them closes the
  fibre.
- **Cancellation** `[proved-derived]`. If `x ≥ y` both have length `n` and share their `j` leading
  digits, then `0 ≤ x − y < b^(n−j)`, so the difference's leading face is read from the places below
  `j` alone. `5102 − 5097 = 5` and `5199 − 5001 = 198` have the same operand faces at one leading digit,
  and that fibre holds every leading digit.

Brandon's conservation of faces is literal here. An operation keeps a face exactly when the face is a
homomorphic image of it, and it keeps the leading face only modulo the residue that the carry carries.

## 3. Measured: the lens associates faces that arithmetic does not conserve `[measured]`

The lens is the online released tree with the ring lock of the code-length record, unchanged: an
exact reach of six bytes, a mixture horizon of `2^13` cells, and a lock that reaches the whole passage.
The passage is the GSM8K training partition, with 21,268 calculations `<<expr=result>>`, of which 20,466
have integer results. A calculation is **met** when the same expression occurred earlier in the
passage.

Bits a result digit (the ring arm; a uniform decimal digit costs `log₂ 10 = 3.32`):

| result digit | met: digits | met: bits | unmet: digits | unmet: bits |
|---|---|---|---|---|
| leading (results of two or more digits) | 8,194 | 1.105 | 8,347 | 3.536 |
| middle | 2,362 | 0.911 | 6,696 | 3.365 |
| units (results of two or more digits) | 8,194 | 0.657 | 8,347 | 3.397 |

**The faces' own budget**, over the single-operation integer calculations `x op y`. The leading fibre
is the exact interval enclosure of `radix.leading-fibre`, not a sample, and every result's leading
digit lies inside its fibre.

| | sum | product | difference |
|---|---|---|---|
| calculations | 3,815 | 6,284 | 3,388 |
| units, given the operands' units | one digit, always | one digit, always | one digit, always |
| leading, given one leading digit and the lengths: mean `log₂` fibre | 0.743 | 0.799 | 1.735 |
| the same, share closed to one digit | 25.7% | 47.5% | 8.6% |
| leading, given two leading digits and the lengths: mean `log₂` fibre | 0.015 | 0.008 | 0.212 |
| the same, share closed to one digit | 98.5% | 99.2% | 81.9% |

The units row also holds on the data itself: among 13,491 such calculations, the operands' units and
the operation fix the result's units in every case.

**Reading.**
- On unmet calculations the lens pays more than a uniform digit at every place. A units digit that the
  operands' units fix exactly costs it 3.40 bits, and a leading digit costs 3.54, although for products
  two leading digits leave a fibre under a hundredth of a bit. It evaluates nothing it has not met.
- Its faces are byte contexts and loop closures to earlier occurrences, and arithmetic conserves
  neither. Its association is evaluation of the whole-string face, one table entry per string.
- **The order of writing.** Numerals are written leading digit first, and the exact face, the units,
  comes last. A digit's place is fixed only when its numeral ends. Evaluation in writing order resolves
  the leading face first through its carry fibre, carries the residue, and closes the units face
  exactly at the end. Here two leading digits close the leading fibre for 98–99% of the sums and
  products.

## 4. A number's digits are a gas of the base's atoms

Brandon's second and third lenses say where the conserved faces come from and how they compose. With
his earlier intuitions (the primon gas and the conservation of faces of October 15, locks as Ising
sites, computation as information diffusion of October 17) they make one picture.

### 4a. Atoms and energy `[proved-standard]`

An integer is a multiset of prime atoms, `n = ∏ p^(v_p)`, with energy `log n = Σ v_p log p`.
- The integers at inverse temperature `σ` form the bosonic gas `ζ(σ) = ∏_p (1 − p^(−σ))⁻¹`
  (`heat.zeta-gibbs`; Lean `Zeta/PaletteLaw`). Squarefree numbers are its fermionic states, and `μ` is
  their parity (Lean `Mathematics/PrimeSimplex`).
- Multiplication composes states, and their energies add.
- **The leading face is the energy read in the base's unit.** The length is its integer part (the
  winding) and the mantissa its fractional part (the phase). Rebasing changes the unit, and
  multiplication rotates the phase.
- **Benford's law is the gas at its transition.** Under `p_σ(n) = n^(−σ)/ζ(σ)`, as `σ → 1⁺` the
  leading digit's law tends to `log_b(1 + 1/d)` (the Dirichlet density). Weights `1/n` over
  `[10⁴, 10⁵)` already give Benford to five places. `σ = 1` is the gas's Hagedorn point and the
  normalization boundary of the zeta law.

### 4b. The trailing face is the gas read through the base's own atoms `[proved-derived]`

`ℤ/b ≅ ∏ ℤ/p^e` over the base's prime atoms (CRT). Base 10 has two:
- a **parity sheet** `ℤ/2`, a binary potential on which a product is an AND;
- a **five-ring** `ℤ/5`, an absorbing zero beside the units `⟨2⟩ ≅ ℤ/4`, on which a product is a
  rotation (`1 → 2 → 4 → 3`) or an absorption.

Every digit rule is a symmetry of these two faces:
- `9 ≡ (1, −1)`: the identity on the sheet and the half-turn on the ring. So `9x ≡ −x (mod 10)`, and
  `9·x` ends in ten minus the last digit of `x`, Brandon's rule. All 153 products by 9 in the passage
  obey it.
- The units `{1, 3, 9, 7}` of `ℤ/10` are `⟨3⟩`, with discrete logs `0, 1, 2, 3`. Units multiply by
  adding these phases mod 4, so multiplication becomes phase addition on the ring. All 228 products of
  two units in the passage obey it.
- `10 ≡ (0, 0)`: multiplying by the base absorbs both faces and moves the trailing face up a place. It
  is the winding.

**Binary potentials integrate into the digit law.** For uniform operands, the trailing digit's law is
the product, over the base's atoms, of each atom's two-level law: absorbed with weight `2p − 1`, and
each unit with weight `p − 1`, out of `p²`.
- Base 10 gives `27, 4, 12, 4, 12, 9, 12, 4, 12, 4` per hundred: the parity sheet's `3 : 1` times the
  five-ring's `9 : 4 : 4 : 4 : 4`. These are exactly the counts of `radix.multiplication-table`.
- Base 12 factors the same way, over `ℤ/4 × ℤ/3`.

In base 2 the only atom is one sheet. Addition is `x + y = (x ⊕ y) + 2(x ∧ y)`: parity, plus a bound
pair carried up a place, repeated until no pair is left. The carry is the pair binding that moves up
the tower, the section flux of `radix.carry-section-flux`. These are the bitwise operations moving the
parts about each other.

### 4c. Fermat composes the ingredients on a ring of p sites `[proved-standard]`

Place `a` ingredients on the sites of a ring of `p` sites, a necklace. Of the `a^p` configurations, the
`a` constant ones are fixed by the ring's rotation, and every other one lies in an orbit of exactly
`p`. So `p ∣ a^p − a`. Fermat's little theorem is the ring's combinatorial potential, and its orbits are
the atoms: `(a^p − a)/p` primitive necklaces.

The same holds with any integer transfer matrix `A`, which couples neighbouring ingredients along the
ring as binary or wider potentials:
- `tr(A^p) ≡ tr(A) (mod p)`: the partition function of a periodic chain of `p` sites is congruent to
  that of one site.
- `P_n = (1/n) Σ_(d∣n) μ(d) tr(A^(n/d))` is an integer, the count of primitive closed orbits of length
  `n` (Gauss's congruence). The dynamical zeta factors over them as atoms,
  `1/det(1 − T A) = ∏_n (1 − Tⁿ)^(−P_n)` (`navigator.zeta`, `aeon.zeta-exp`). For the 0/1 matrix of a
  map this is formal-checked (`PrimitiveCycle.primitive_count_moebius`,
  `transfer_determinant_euler_product`). The integers'
  `ζ(s) = ∏_p (1 − p^(−s))⁻¹` has the same form, with the primes as the primitive orbits.
- The `2^p` binary words of length `p` are two constant words and orbits of `p` (length 7: 128 words in
  2 fixed words and 18 orbits of 7). So `(x + y)^p ≡ x^p + y^p (mod p)`: modulo `p`, binary potentials
  integrate as if they were independent.

**Composed over the base's atoms.** Fermat at 2 and at 5, joined by CRT, gives `n⁵ ≡ n (mod 10)`: a
fifth power ends in the same digit as its root. It is a digit rule of the same kind as `9x ≡ −x`.
Euler's `a^φ(b) ≡ 1` for units is the order of the unit ring's rotation (`φ(10) = 4`).

### 4d. The thermodynamic reading `[interpretation]`

A chain's partition function is `tr(Aⁿ) = Σ λ_iⁿ`. Its free energy density is `log λ_max`, an entropy
rate, and the rest of the spectrum is a finite-size correction that decays. Read on code, the floor of
the code-length record (`w = −1`) is the passage's entropy rate, and its learning part is the decaying
correction. Coupled binary sites are the parametron's locks, and ferromagnetic coupling puts the zeros
of their partition function on the unit circle (`parametron.coupled-locks-lee-yang`), the RH-shaped
statement already inside the machine's objects.

### 4e. So arithmetic is learned as Brandon describes

The conserved faces are the base's atom rings (trailing, exact) and the energy circle (leading, up to
the carry fibre) `[proved-derived]`. The digit distributions of interacting digits are pushforwards of
the operands' distributions through these faces' maps. The maps are the symmetries of each ring
(rotation, reflection, absorption) and rotations of the log circle. Learning arithmetic is locating
these keys from the joint distributions, and once they are located, associating at these faces is
evaluating `[interpretation]`.

The passage offers these maps thinly `[measured]`. Of its 6,284 products, 2,729 have an operand ending
in 0, and 3,327 more have an operand that is even or ends in 5. Only 228 have both operands on the unit
ring, and 54% of the results end in 0. The leading digits follow Benford except near 4 to 6, where
round amounts dominate: 760 fours and 603 sixes where Benford gives 609 and 421, and 256 fives where it
gives 498.

## 5. What this means for Athena `[design]`

1. **One mechanism.** Association and evaluation are not two parts. Athena associates through
   contacts, and whether that evaluates on unmet operands depends on which faces her modes carry.
2. **The faces are rotations, and her complex modes are rotations.**
   - A digit placed as a phase on a ring carries the trailing face of a sum as phase addition, with the
     carry as the winding past a full turn (`ratio.div-rem`: the quotient is the winding, the remainder
     the phase).
   - A product's trailing face is phase addition on the unit ring's discrete log, beside the parity
     sheet's AND and the absorbing zero. Its leading face is phase addition on the log circle.
   - The tower's diagonal complex modes can carry all of these if learning places the digits on them.
     No new object is needed.
3. **The product is a pair contact.** Composing two operands' faces is bilinear, the convolution's
   `x_i y_j`. In Athena that is a pair contact or a gate between two carried faces, not a sum into one
   mode.
4. **The carry is the carried residue.** A dormant mode holds it, with `|λ|` at one while a numeral
   passes, and its residue is carried, never rounded away (`release.carried-residue` against
   `release.plain-rounding-annihilates`).
5. **Place is right-anchored.** A digit's place is known only when its numeral ends, and the result is
   written leading digit first. The leading face needs the operands' two leading digits and lengths to
   close its fibre (98–99% of sums and products here). The units face closes exactly from the operands'
   units at the end.
6. **A terrain of interacting digits.** The GSM8K passage shows the unit ring in 228 products. A
   terrain generated by an exact routine, with many sums, products and differences across the rings and
   lengths, gives the maps enough encounters. A terrain may generate its truth exactly. Operand pairs
   are held out.
7. **Nothing authored inside.** The machine gets no calculator, digit-to-phase table, place counter or
   carry routine; those are catered machinery. Her own encoding and deposition must locate the faces.
8. **Readings each run, beside the generations:**
   - the held-out code of result digits on unmet calculations, by place and operation, against the face
     budget of §3 (the lens's baseline: 3.40 bits at the units and 3.54 at the leading digit);
   - the trailing digit law of the products she writes, against `27, 4, 12, 4, 12, 9, 12, 4, 12, 4`;
   - the located keys: whether her digit representations sit on the parity sheet and the five-ring,
     and whether multiplying by 9 acts on them as the half-turn.

## 6. Corrections to the code-length record

- **§2** called the lens's result digits "a table at the lens's grain, not arithmetic". It is evaluation
  at the lens's grain, at faces that arithmetic does not conserve, so it reaches only the calculations
  met (§3 here). The sentence there now says so and points here.
- **§1 and §6** read `w` as unchanged under the casts. That holds for constant casts: bits↔nats,
  cell↔byte, and a region's steady share of the passage. A clock whose units change length is not a
  constant cast (Epime's review note of October 23). In general `w′ = w · d ln V/d ln V′`. With `N_k`
  bytes for `k` founded units, `w_unit = w_byte · d ln N_k/d ln k`. A region at its byte floor
  therefore reads `w_unit = −d ln N_k/d ln k < −1` while its units lengthen. That phantom reading is the
  cast, not hardening. It agrees with §1's law that expansion needs the material to change, since
  founding longer units changes the clock's material. A report on a unit clock declares its cast
  (`code.clock-cast`).

## 7. Owed

- **Lean** (one box in #410):
  - a conserved face descends (`q ∘ T = T_q ∘ (q × q)` exactly when every fibre is one point), and a
    jointly injective face family evaluates `T`;
  - the cancellation of a difference's leading face;
  - the factorization of the trailing digit law over the base's atoms, with the base-10 counts;
    `9x ≡ −x` and `n⁵ ≡ n (mod 10)`; the unit ring's discrete log;
  - `tr(A^p) ≡ tr(A) (mod p)` for integer matrices, which extends #410's box on necklace integrality
    for a general return map (the map case is `PrimitiveCycle`);
  - the clock cast of `w`.
- **Atlas rows:** `arith.association-is-evaluation`, `radix.difference-leading-cancellation`,
  `radix.multiplier-face-action`, `radix.product-digit-law-factors`, `arith.fermat-ring-partition`,
  `radix.leading-face-gas` and `code.clock-cast`.

## Receipts

`2026-10-23_ASSOCIATION_IS_EVALUATION_receipts/`.

**Programs:**
- `assoc.py` reads the code-length record's lens output beside the passage and writes `assoc.json`.
  The lens output is the per-cell bits of the whole passage (169,352,064 bytes), which is not committed;
  that record's `run.sh` regenerates it.
- `fibre.py` computes the leading fibres by interval enclosure and writes `fibre.json`.
- `digits.py` reads the products' trailing and leading digit laws and writes `digits.json`.
- `fermat.py` checks §4's identities exactly, including 3,600 congruence checks over random integer
  matrices, with no failure.

**Run receipts** `run_assoc.txt`, `run_fibre.txt`, `run_digits.txt` and `run_fermat.txt`.

**Time.** The runs were unmeasured beforehand, so they were planned under the one-to-three-minute rule,
with deadlines of 120 s (`assoc.py`) and 60 s (the others).
- `assoc.py` took 16.9 s with a cold read and 1.5 s warm, with a peak of 260 MiB. That is 0.14 of its
  deadline.
- `fibre.py` took 0.1 s, `digits.py` under a second and `fermat.py` 2.2 s.
