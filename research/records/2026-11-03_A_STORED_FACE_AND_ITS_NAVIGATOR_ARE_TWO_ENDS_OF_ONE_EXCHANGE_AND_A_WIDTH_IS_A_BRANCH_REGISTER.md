# A stored face and its navigator are two ends of one exchange, and a width is a branch register

November 3. Refs #404 #601. Status: [lens] for Brandon's statement (paraphrased; his words stay outside the repository),
[source-inspected] for the owners it joins, [definition; agent-inferred] for what it changes in the field's plan. Claude
(opus), design lead.

Computational object: the helical pair interaction. Of the winding guide's six general objects the lens touches the
**helix** (a ring's period is a register's base, its winding the carry) and **faces and placement** (a stored face against
the navigator that regenerates it); the pair, cell holonomy, the tube and the tower thread stay attached through the field.

## 1. The lens

Brandon, November 3 (two messages, on the field's growth by copies from width 32 to 64):
- **A width is a branch register.** A width is a partition, a sum of parts such as `2² + 2¹ + 2⁰`, each part a lane of a
  morphodynamic circuit, not one undivided register doubled.
- **A stored face and its navigator are two ends of one exchange.** `17179869185` and `2³⁴ + 2⁰` carry one value; the second
  stores less and must be navigated (converted) to give the first's face; storing a value in the form it will be read
  saves the navigation, storing its generator saves the memory. A float's sign, exponent and most of its mantissa are
  stored although the system they sit in already implies them. A constraint identity (π, `e`) is the extreme: the
  navigator alone, no stored digits, at the most navigation. A machine that keeps both, cached partial faces and fitted
  fractal navigators, and moves between them, optimizes whatever it holds. He called this keystone.

## 2. Where the framework already holds it, and the one refinement

- `docs/ELEMENTARY_OBJECTS.md` (π and `e`): the identity is the navigator; digits are a receiver face
  (`RadixWindowReceiver`); the **partial navigators** (the compiled binary-splitting blocks `(P, Q, T)`, composing
  associatively) are the cached partials, extendable where stored digits are not.
- The canon's compression tablet §5 and the atlas rows `code.levin-kt`, `code.compact-program-pi`, `code.window-cost`: the
  exchange's standard carrier is Levin's `Kt(x) = min_p {|p| + log₂ t(p)}`; a window at offset `k` costs about `2 log₂ k`
  against `ℓ log₂ b` for its literal digits.
- **The refinement** (the tablet's own): the exchange is a Pareto frontier over description bits, work, time, space,
  erasures and energy, not a conserved product. Blum's speedup theorem gives functions with no fastest program, and the
  only fundamental energy floor is on erasures (Landauer), so a change of base, a bijection, costs time and the erasure of
  its intermediates, never a fixed energy per bit.
- **Number bases.** A part of a width is a coordinate (parts add, a direct sum); a base-`b` digit is a register of `b`
  states (`ℤ/b`; lanes multiply state counts); `2² + 2¹ + 2⁰` is the integer seven written in base two, equal in value to
  `10₇` and unlike it in carries. Exact parallel lanes are the Chinese remainder theorem's, over coprime periods
  (`ℤ/14 ≅ ℤ/2 × ℤ/7`, no carry between lanes); `1097 − 1 = 2³ · 137` is the split `n − 1 = 2ˢ d`, `d` odd, of Fermat's
  and Miller–Rabin's tests.

## 3. Where the field stands against it

[source-inspected] `hnn::tower::field`:
- **The rings already hold the lens.** The ring periods (`ring_periods`) are powers of two and three (2, 3, 4, 9, 16, 27,
  … 4,096, 6,561), so the place clock is carried in coprime lanes `ℤ/2ᵃ × ℤ/3ᵇ`, and the source enters as phase-carried
  moments on them, the passage held in a navigator's basis rather than as a tape (the retention law).
- **The material does not.** The learned material is a dense array of exact integers on one fixed grain (`2^(−24)`), every
  site's state a dense register of `D` coordinates read by dense charts, and growth by copies
  (`FieldLearner::widened`) doubles that register. Apart from its clocks' paces (located keys, §16.15 of the field record),
  nothing in the field fits a navigator to a regularity and then regenerates its faces instead of storing them.
- **GSM8K's arithmetic is where the exchange bites.** `<<65*5=325>>` cannot be learned as a stored table of products; the
  field must locate the carry law. Its rings are odometers with carry (selective stepping, the carry chain), so that
  navigator is of the machine's own kind, located, never authored (no catered machinery).

## 4. What it changes in the plan

[definition; agent-inferred] In order, each a short loop on the card:
1. **The answer reads its question first** (the field record's §16.35: the copy lab, and the question's information
   through the joint code). Arithmetic presupposes it.
2. **Growth by a fresh branch** in place of copies: a part with its own normalization and frame, opened from its own
   drawn rows and read through columns founded at zero, so every face is kept and no copy has to part from its source
   (§16.29 measured copies parting slowly). Its size is the part the withheld code's stall asks for, never a doubling by
   rule.
3. **A located carry navigator for the calculations**: a ring whose winding is the carry, its keys located from the
   answers' own calculations, read against the joint code's information on the calculation sites.

Failures this could repeat, checked: **catered machinery** (no calculator: the carry navigator's keys are located by the
field's deposition); **a design thought in the programming language** (a width is stated as parts and lanes, never as an
array size picked by hand); **a lens resetting the work** (it changes item 2's law and adds item 3, and the order keeps the
failed gate, the question's coherence, first).
