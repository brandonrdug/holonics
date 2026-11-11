# A grip of letters is a navigator word, the fixed-advance moment reads only pair terms, and the contact's product must carry along its own circle

Status (2026-11-10, night; amended 2026-11-11, 00:22 UTC): a ruling of theory with its host rulers. A lens of 23:49 UTC amended the ruling within the hour: §8 holds the amended law and its reads, and §2.4 and G30 stand only as the first form. The card attempt is unbuilt. Refs #73, #406, #408, #410.

[historical] The lens (Brandon, November 10, 22:15 UTC, paraphrased). Walking toward a wall, a step is not a fixed half of what remains. Each step is founded discretely, the gap it leaves has a basis of its own, and the steps still possible re-tile as one moves, so one stride can be longer than another and change how many remain. This record takes that part of the lens to the machine: what a written letter does to the frame in which the next one is read. The rest of the lens is in [the navigation record](2026-11-10_THE_COST_OF_NAVIGATING_BETWEEN_STATES_HAS_A_FLOOR_FROM_COUNTING_A_HALF_FROM_REVERSAL_WITH_A_POSITIVE_PAIRING_AND_LANDMARKS_ARE_ITS_COMPRESSED_POTENTIAL.md).

It also corrects a reading of the same evening. At 22:40 UTC theory read design's transmission table as "the field holds the two-body law and lacks each further body's joint term". The fitted pair-only reader below shows that this was wrong in its second half: the field already holds part of two letters' joint term, and little or nothing of longer words.

## 1. Recovered

| Part | Held as | Where |
|---|---|---|
| The source enters as a moment with a fixed advance | `m(l ++ [u]) = U m(l) + I E(u)`; the future after any word is affine in the moment | `navigator.source-moment`, `navigator.moment-append-affine` (Lean) |
| A word of transports keeps its order | `transportWord T (w₁ ++ w₂) = transportWord T w₂ ∘ transportWord T w₁` | `navigator.transport-word` (Lean) |
| The moment of a contracting reader is the word's address | the Cantor reader | `navigator.moment-is-address` |
| A clock is part of the phase | the same advance and encoder read differently under two clocks | `navigator.clock-changes-moment` |
| A reader built from pair contacts misses the three-body part | functions on `L × x × R` modulo pair terms | `code.pair-contact-conditional` |
| A held block is a leaky grip | `h_g − h_∞` passes through `g` held letters | `code.register-content-by-distance` |
| Growth is a partition, never a doubling | widths add over branches and multiply along registers | `radix.register-composition` |
| The built contact pairs a site with one strand mate a tick | `Field::tick`, `strand_mate` | [the grip record](2026-11-10_A_HELD_LETTER_IS_A_LEAKY_GRIP_THE_LAW_ACROSS_A_PLACE_IS_THREE_BODY_WIDTHS_ADD_ALONG_A_BRANCH_AND_PLASTICITY_IS_ANISOTROPY.md); [design's reads](2026-11-10_FOUNDED_PARTS_AT_THEIR_OWN_DEPOSIT_RATES_GAIN_0.022_IN_FOUR_LAPS_AND_THE_FIELD_PASSES_LITTLE_PAST_TWO_LETTERS.md) §2 |

**Recovered after the lens of 23:49 UTC.** The first ruling (§5) was made without these. §8 says what each changes.

| Part | Held as | Where |
|---|---|---|
| A unit above the byte is founded by a merge that its price accepts | the merge law: a count proposes a pair, the complete code accepts it | `hnn.founded-units` (`crates/holonics/src/hnn/units.rs`), October 23 |
| A level's clock ticks on news | a level ticks where the running face code crosses a multiple of its unit | `hnn.tower-news-clock`, October 27 |
| A tower of scales over the field | `Scale {period, split, coarse, glue}`: a packet of `P` sites restricts to one coarse site by one chart of its reads in place order, the coarse field ticks, and a prolongation chart founded at zero returns it | `crates/holonics/src/hnn/tower/field/scale.rs`, built on host and card on November 3 and 4 ([its record](2026-11-03_THE_FIELD_BECOMES_A_TOWER_OF_SCALES_A_PACKET_IS_THE_RETENTION_QUOTIENT_OF_ITS_INTERIOR.md)); its first reading missed its acceptance (the field record §16.39); packets cut at landmarks were deferred. It had no atlas row; this change adds `tower.field-scale-packets` |
| The turned heads' clocks run at class rates | `κ_h(t) = 1 + c_h[u_t]`, `τ_h = Σ κ`, the moment and the frames read `τ` | `tower.field-pace` (the field record §16.2 and §16.16), November 2 |
| A packet is an affine move, and any partition composes to the same move | `(T₂, m₂) ∘ (T₁, m₁) = (T₂T₁, T₂m₁ + m₂)` | `radix.packet-affine-move` |
| Merging constituents carries the moment through a square | `m′(π∘u) = P m(u)` | `encoding.merge-moment-square` |
| Re-segmenting a tube is an equivalence on its complete face | the split, rejoin and associator laws | `tube.resegmentation-associator` (Lean) |

## 2. The derivation

### 2.1 A fixed advance reads only pair terms

[proved-derived] The source moment with a fixed advance is `m(l) = Σ_k U^(n−1−k) I E(u_k)`, linear in the letters' encodings. Any linear reading of it is therefore a sum of one-letter terms:

`⟨γ_x, m(l)⟩ = Σ_k f_k(u_k, x)`, with `f_k(u, x) = ⟨γ_x, U^(n−1−k) I E(u)⟩`.

Logits that are sums over the letters of pair terms are what a pair-only reader fits. So a source that enters by place-clocked moments and is read linearly holds no joint term of two written letters, at any width. A joint term can enter only where the passage is not linear in the encodings: a product of two faces, or a normalization.

[amended November 11] This is the plain clock's case. The built field's turned heads read their moment on clocks whose rate is a class's own (`tower.field-pace`), which is a content stride of a restricted form: one real rate a class a head, with the skin tied to the turn. What those clocks have located on this line is G33 (§8.4).

### 2.2 The content-stride moment

[proved-derived] Let each letter `u` act on a circle as the move `z ↦ α(u) z + β(u)`, with `α(u)` and `β(u)` complex: a turn and a boost (`α = e^(−λ + iθ)`), and a deposit. In passage order:

- `m([]) = 0`, `m(l ++ [u]) = α(u) m(l) + β(u)`;
- `m(l) = Σ_k (Π_(j>k) α(u_j)) β(u_k)`;
- `m(l ++ w) = A(w) m(l) + m(w)`, with `A(w) = Π_j α(w_j)`.

The append law stays affine, so the moment is still a retention quotient for the append action, and a constant `α` returns 2.1. The moves do not commute, `(α₂, β₂) ∘ (α₁, β₁) = (α₂α₁, α₂β₁ + β₂)`, so order is carried by composition alone, with one table for every offset. Numbering the letters back from the nearest, the read holds products of every order:

`m = β₁ + α₁β₂ + α₁α₂β₃ + α₁α₂α₃β₄ + …`

This is the lens's re-based step. A letter's stride is its own, and each written letter re-bases the frame in which the earlier ones are read. On the objects it is a clock driven by the content (`navigator.clock-changes-moment`), an ordered transport word (`navigator.transport-word`) and the Swing's turn, boost and shear on each circle. Atlas `navigator.content-stride-moment`.

[derived] Its limit. On one circle with one table, the term of letters 2 and 3 that is free of letter 1 needs `α(u₁)` constant while `α(u₂)` varies, which one table cannot give. Several circles approximate it by cancellation. Strides read from a face that knows its neighbours, or moves that do not commute, remove the limit. The ruler in §3 measures what the limit costs.

### 2.3 What the built tick does

[reading of the source; `crates/holonics/src/hnn/tower/field.rs`, `Field::open` and `Field::tick`]

- **Opening.** A site's face is `E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1)) + release(C s_t + b)`. It already holds both strand neighbours' encodings, added.
- **A tick.** The lane chart; the heads (a lock between the receiver's probe and each met source's key, one normalized series, a current added through `out`); the lane chart again; `a = A·read`, `b = B·read` (`f` each); the pair contact `c_e(t) = (a_e + i a_(f/2+e))(t) · (b_e + i b_(f/2+e))(mate)`, the mate being the site before at even `e` and the site after at odd `e`; then `face += W c`.
- **So.** At tick 1 the open site's product with its mate holds the two nearest letters of one side as a bilinear form of rank `f/4` complex, 16 at `f = 64`. A word of `n` letters takes `n − 1` ticks and passes through the face (`W`, the lane chart, `A` or `B`) `n − 2` times. The face is 64 wide and also holds three letters' encodings and the heads' currents. `K = 4` ticks give words of five letters in form.

### 2.4 The carried contact

[ruling; the definition of an attempt, unbuilt; **replaced on November 11 by the scan of §8.4**, which runs the carry to its stop inside one tick and reads the stride by its own chart]

`p_e^k(t) = a_e^k(t) · ( b_e^k(m) + κ_e · p_e^(k−1)(m) )`, with `m = strand_mate(t, e)` and `p⁰ = 0`; `W` reads `p` where it read `c`.

Unrolled along the mates `t₀ = t`, `t_(i+1) = m(t_i)`:

`p_e^K(t) = Σ_(j=1..K) κ_e^(j−1) (Π_(i<j) a_e^(K−i)(t_i)) b_e^(K−j+1)(t_j)`.

- This is 2.2 with the stride `κ_e a_e` and the deposit `b_e`, both read from each site's own face.
- `κ_e` is complex, one a circle (`f` numbers): the circle's own place turn and leak. Founded at zero, the attempt's outputs equal the founding state's.
- No width changes: `f`, the face, the lanes and `K` stay as built. The cost is one complex multiply and add a contact a tick, and a buffer of `f` numbers a site.
- The adjoint walks the carry back with the producing operands. The carry of tick `k − 1` is a forward carrier of the pass, so no tape is added.
- A word on one side no longer re-enters the face between its letters. The product of a left word with a right word at the open site still passes the face once.

On the objects: a helix is a circle and a carry. The built contact has the circle, which is the complex product, and no carry along the strand: it hands its product to the face every tick. Atlas `contact.carried-product`.

## 3. The reads

[measured; host rulers, never machinery; the PC's VM, 2 cores; fitted on TRAIN's distinct contexts (8,096,768 places in 24,685 passages), read on HELD128 (43,470 places); the target from `g` letters on its left; nats a place]

**The codes.**

| g | Contexts | Held places | Joint count tables | Pair-only reader | Joint term |
| --- | --- | --- | --- | --- | --- |
| 2 | 6,584 | 43,214 | 1.989 | 2.468 | 0.479 |
| 3 | 67,083 | 43,087 | 1.475 | 2.348 | 0.873 |
| 4 | 242,724 | 42,960 | 1.249 | 2.290 | 1.041 |

The pair-only reader has one table a letter, with the logits added (`cap_n.py`, `r = 0`). The joint term is its code less the joint tables'.

**The share of the joint term held by products of one factor a letter.**

| Reader | Circles | g = 2 | g = 3 | g = 4 |
| --- | --- | --- | --- | --- |
| Free factors, one table an offset (`cap_n.py`) | 4 | 0.50 | | |
| | 16 | 0.81 | 0.57 | 0.48 |
| | 64 | 0.98 | 0.85 | 0.75 |
| One stride a letter, composed in passage order (`cap_o.py`) | 16 | 0.77 | 0.49 | 0.40 |
| | 64 | 0.92 | 0.79 | 0.65 |

- The codes behind the shares: free factors 2.078, 1.848, 1.787 on 16 circles and 1.998, 1.608, 1.507 on 64; one stride a letter 2.099, 1.916, 1.874 on 16 and 2.026, 1.659, 1.608 on 64.
- Each fit stopped at its time budget (213 to 947 steps for the products). The 64-circle fits were still falling slowly, so their shares are lower bounds of the forms.
- The strides contract. Their mean modulus is 0.97 to 0.99 at two letters, 0.68 to 0.76 at three and 0.58 to 0.67 at four: a leak a letter, which is the leaky grip.
- One stride a letter holds 0.93 and 0.87 of what free factors hold at three and four letters on 64 circles. That is the cost of the limit in 2.2.

**The field beside them** (design's read of ct8, the rest of the answer open, one target a region; its own count tables read 1.898, 1.423 and 1.224 at two, three and four letters, so its places are easier than the rulers' by 0.09, 0.05 and 0.02):

| What each added left letter passes | Third letter | Fourth letter |
| --- | --- | --- |
| The field (2.239, 2.069, 2.040) | 0.169 | 0.029 |
| Pair-only reader | 0.120 | 0.058 |
| One stride a letter, 16 circles | 0.183 | 0.042 |
| One stride a letter, 64 circles | 0.367 | 0.050 |
| Free factors, 64 circles | 0.391 | 0.100 |
| Joint count tables | 0.514 | 0.227 |

- The field reads 0.23, 0.28 and 0.25 under the pair-only reader at two, three and four letters, or about 0.14, 0.23 and 0.22 once the two sets of places are aligned by their count tables. That is three to five tenths of two letters' joint term, and a quarter of three and four letters'.
- The field's joint content hardly grows past two letters. Its third letter passes 0.05 more than a pair term would, and its fourth passes less than a pair term.
- At two letters, where the built tick forms the product at once, 16 circles can hold 0.77 to 0.81 and the field holds 0.3 to 0.5. That lack is of location, not of form.

## 4. Guesses and scores

All fixed in `guess_capacity_28_30.txt` before their reads.

- **G28a, the pair-only reader** (fixed 22:55 UTC). Guessed 2.25, 2.10 and 2.03; read 2.468, 2.348 and 2.290. Missed by 0.22 to 0.26. The rule "the field's open read is the two-body reader" (within 0.06) failed: the field reads well under it.
- **G28b, free factors.** Guessed 0.20, 0.50 and 0.75 at two letters on 4, 16 and 64 circles; read 0.50, 0.81 and 0.98. Guessed 0.35 and 0.55 at three letters and 0.30 and 0.45 at four; read 0.57 and 0.85, and 0.48 and 0.75. Every share read higher than guessed. Both rules held: the third body's term is expressible by the built contact's count, and a word of content turns holds the further bodies.
- **G29, one stride a letter** (fixed 23:18 UTC). Guessed 0.97, 0.65 and 0.50 on 64 circles; read 0.92 (213 steps), 0.79 and 0.65. Guessed 0.80, 0.45 and 0.35 on 16; read 0.77, 0.49 and 0.40. The rule held: three quarters or more of the free factors' share at three and four letters, so the carry along the circle holds the grip.
- **The part-rate arm** (guess of 19:05 UTC; design's read). Guessed 0.03 on the held joint after four laps; read 0.022. Missed, and over the 0.01 floor, so travel binds. Guessed 0.02 on the locked code; read 0.023. Held.
- **G30, the carried contact on the card** (fixed 23:26 UTC, unread; superseded by G30′ of §8.4 unless laps of the site-a-tick build had already started). After four laps the third letter passes 0.21 or more (now 0.169), the fourth 0.06 or more (now 0.029), and the held joint ends 0.02 or more under the same line's laps without the carry. Mean `|κ|` under 0.05 means the carry did not open (travel). Mean `|κ|` over 0.2 with the fourth letter still under 0.04 means it opened and the grip did not use it, and the attempt fails there.

## 5. The ruling

[ruling; theory, November 10, 23:30 UTC, sent to design]

1. **Growth is not width now.** Not 128 contacts and not a wider face. At two letters the field uses its 16 circles toward a mate about as 2 to 4 would be used, and it forms almost nothing of longer words. More circles would be founded into the same lack.
2. **At two letters the lack is of location.** The laps locate it. Part rates are the line's law from here, since travel binds.
3. **At three and four letters the tick lacks the carry.** The carried contact of 2.4 is ordered as a named attempt, with host and card realizations and their parity, `κ` a founded part of its own under the part rates.
4. **The test** is G30: four laps from the part-rate line's lap 4 state, beside that line's laps 5 to 8, read by the transmission table before and after and by `|κ|` and its lap cosines.
5. **Withdrawn:** "the field holds the two-body law and lacks each further body's joint term" (theory, 22:40 UTC), in that form.
6. **Amended, November 11, 00:22 UTC** (§8.4). Point 3's carry is replaced by a scan that runs to its stop inside one tick with a stride chart of its own, and point 4's test by G30′. Withdrawn with it: the carry of one site a tick with its stride tied to the reader (`κ_e a_e`) as the law, and "the built moment advances by a fixed stride" as a description of the built field.

## 6. What does not transfer

- The rulers' tables. A table of strides indexed by a letter is the ruler's instrument. In the machine a stride is read from a site's face by the contact's own `A`, a located part of the constitution, and deposition locates it. A stride table built into the machine would be a cache.
- Adam and the float fits belong to the ruler.
- The shares are of this passage (bytes of the code passage) at this grain. Text, image, acoustic and motor terrains owe their own reads. The carried contact itself is not specific to text: it composes whatever the faces hold along a strand, and the strand's mates belong to the boundary codec.
- **Against the lessons.** The carry is stated as holonomy along the contact's circles, never as a window of offsets. Its reach is the field's own tick count, the bound the built tick already has. The test is read by structure (what each added letter passes) beside the held code. The attempt enters a run only with its card realization, its parity and its adjoint.

## 7. Owed

- Design: the amended attempt of §8.4 with G30′, and G33.
- Theory: the rulers on design's own places, since the field and the rulers were read on different places. The locked visits of §8.2 are on the rulers' places, which closes this for the locked read.
- Theory: the ruler for both sides, a left word times a right word at the open site.
- Lean, for #410: the append law `m(l ++ w) = A(w) m(l) + m(w)` for an advance that depends on the letter, over a commutative ring, with `moment_append` as its constant case; and the statement that a linear reading of the fixed-advance moment is a sum of one-letter terms.

## 8. The lens of 23:49 UTC: a longer word is a founded unit

[historical] The lens (Brandon, November 10, 23:49 UTC, paraphrased). A longer word is one larger unit founded on the finer grains of elements. That is coarse graining, or telescoping, and it is the idea a tokenizer rests on.

It arrived twenty minutes after the ruling of §5 and corrects it in two ways. The ruling treated a word as letters composed one site a tick, where the lens says the word is one unit at a coarser grain. And the ruling was made without recovering what the repository already holds on founded units, on a tower of scales and on clocks driven by content (§1's second table). Two recovery misses are stated here as misses:

- The founded-unit owners (`hnn.founded-units`, `hnn.tower-news-clock`, the tower of scales in `scale.rs` with its deferred landmark packets) were not read before the carried contact was ordered.
- The built field's turned heads already carry clocks whose rate is a class's own (`tower.field-pace`). §2.1's "fixed advance" is the plain clock's case, and "the built moment advances by a fixed stride" was wrong as a description of the built field.

The repair to the practice: before a part is ordered, `crates/` and the field record are searched for a clock, a tower or a unit that already does the part's work, beside the atlas. The tower of scales had no atlas row, which is how an atlas-first search passed it, and this change adds one.

### 8.1 One law at two grains

[proved-derived] A unit `w = w₁ … w_n` is the composed move of its letters, `(A(w), m(w))` with `A(w) = Π_j α(w_j)` and `m(w) = Σ_j (Π_(i>j) α(w_i)) β(w_j)` (§2.2).

- **Telescoping is associativity.** `(A₂, m₂) ∘ (A₁, m₁) = (A₂A₁, A₂m₁ + m₂)` is associative, so every bracketing of a passage into units composes to the same move, and for units `w₁, …, w_n`: `m(w₁ ++ … ++ w_n) = Σ_j (Π_(i>j) A(w_i)) m(w_j)`. This is §2.2's law one grain up, with units in the place of letters. It is the law the atlas already holds for a numeral (`radix.packet-affine-move`: any partition composes to the same move) and for merged constituents (`encoding.merge-moment-square`).
- **A stop is a contraction.** `m(l ++ w) − m(l′ ++ w) = A(w) (m(l) − m(l′))`. Where `|A(w)|` is small every earlier state arrives at nearly one state after `w`. That is a landmark in the repository's sense (a face where paths converge) and the Cantor reader's address condition (`navigator.moment-is-address`). The tower-of-scales record of November 3 already names it as the ideal packet boundary: after a word's last letter the next state no longer depends on which word it was. Automata theory calls such a word synchronizing, and coding theory calls it a comma. A unit's boundary is therefore read from the modulus of a stride. Nothing has to be told where it is.
- **Founding stores what composing computes.** A founded unit keeps `(A(w), m(w))` for one `w`; a composed unit recomputes it from its letters. This is the precision law's exchange of storing and computing. What a founded unit can hold and a composed one cannot is the part of a unit's law that is not the product of its letters' moves.
- **In the machine a unit is a store.** The carried state on a circle is charged by deposits, leaks by its strides and is read through a port, so it passes the test of stores and caches. A table of units addressed by their letters has no balance and no port: it is the cache the lessons refuse.

### 8.2 The reads

[measured; host rulers, never machinery; the PC's VM; TRAIN and HELD128 as in §3; nats a place; the kinds of letters (space-class: newline, space, tab, carriage return; word letters: letters, digits, underscore; punctuation: the rest) are the ruler's and are told to no machine]

**The fitted strides stop at separators** (`cap_p.py`; the strides of §3's word ruler, their modulus averaged over the circles and weighted by each letter's frequency).

| Fit | Space-class | Punctuation | Word letters | Separators |
| --- | --- | --- | --- | --- |
| four letters, 64 circles | 0.365 | 0.528 | 0.862 | 0.426 |
| four letters, 16 circles | 0.314 | 0.488 | 0.745 | 0.379 |
| three letters, 64 circles | 0.461 | 0.603 | 1.030 | 0.514 |
| three letters, 16 circles | 0.393 | 0.543 | 0.915 | 0.449 |

- Of the twenty most frequent letters the newline is lowest in all four fits (0.28 to 0.40), then the space and the closing bracket. At four letters on 64 circles the stride's modulus is under 0.5 on 0.84 of the circles for the newline, 0.77 for the space, 0.72 for the closing bracket, and 0.06 to 0.33 for the word letters.
- The ruler was given no boundary. It found them from the code alone, as the letters whose strides contract.

**Founded units by count cost about what composed strides cost** (`cap_p.py`; a context of two to eight left letters is founded when TRAIN meets it `c` times or more; Witten–Bell down the founded suffixes; 42,960 places).

| c | Units of 2 to 8 letters | Cells | To 4 letters: code | its units | its cells | To 8 letters: code |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | 4,919,527 | 7,159,787 | 1.2485 | 317,561 | 854,320 | 1.1661 |
| 4 | 1,047,937 | 2,959,158 | 1.2544 | 132,127 | 636,462 | 1.1504 |
| 16 | 303,948 | 1,495,101 | 1.2781 | 59,519 | 456,797 | 1.1648 |
| 64 | 89,806 | 731,896 | 1.3458 | 26,155 | 299,873 | 1.2600 |
| 256 | 23,892 | 314,523 | 1.4739 | 10,440 | 172,490 | 1.4235 |
| 512 | 11,302 | 190,593 | 1.5812 | 5,997 | 120,918 | 1.5482 |
| 1024 | 5,204 | 112,220 | 1.7039 | 3,265 | 81,024 | 1.6823 |
| 2048 | 2,286 | 64,318 | 1.8450 | 1,656 | 51,992 | 1.8302 |
| 4096 | 1,099 | 36,358 | 1.9930 | 828 | 30,709 | 1.9820 |

- The carried word's code on 64 circles (1.608) is met by about 5,300 founded units holding about 110,000 cells.
- At equal store the two are close: 51,992 cells read 1.845 where the word ruler's 16 circles (about 50,600 numbers) read 1.874, and 81,024 cells read 1.704 where its 64 circles (about 79,700 numbers) read 1.608. Founding by count buys no store on this passage.

**Contexts that end at unit boundaries read further** (`cap_q.py`; the ruler's cut: a unit is a run of word letters, a run of one repeated space-class letter, or one other letter; 0.408 units a place, word runs of 4.82 letters on average; every context is a function of the letters before the place alone).

| Levels | 1 | 2 | 3 | 4 | 5 | 6 | 8 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Letter chain (one more letter a level) | 2.728 | 1.994 | 1.478 | 1.249 | 1.165 | 1.141 | 1.166 |
| Unit chain (the unit so far, then one more whole unit a level) | 1.597 | 1.280 | 1.086 | 1.051 | 1.047 | 1.064 | 1.102 |
| The unit chain's mean reach in letters | 3.3 | 5.1 | 8.1 | 10.1 | 13.0 | 15.2 | 20.2 |
| Four letters, then units | | | | 1.249 | 1.275 | 1.089 | 1.050 |

- The last row reads 1.2485 at four letters, then 1.2750, 1.0889, 1.0538 and 1.0504 as one to four levels of units are added past them. The first added level is not a refinement of four letters, so the chain is not monotone there.
- The unpruned letter chain rises past six letters (1.297 at twelve, 1.425 at sixteen). Its best is 1.141 at six letters, and 1.150 pruned at eight.
- Where the gain sits. With four letters the code is 1.902 at unit starts (0.613 of the code) and 0.809 inside units. With four levels of units it is 1.586 at unit starts and 0.690 inside. The unit grain takes 0.32 nats off unit starts and 0.12 off the interiors.
- Store. The unit chain's first four levels hold 252,951, 653,797, 1,663,816 and 2,430,197 cells, about 5.0 million; the letter chain to four letters holds 0.86 million and to eight letters about 7.2 million. The ruler's coarse grain buys reach at the price of store.
- The first run of this ruler drew the unit cut with the letter being read, which told the context that letter's kind and read 0.982 at four levels. The size of the gain exposed it. The contexts were rewritten on the prefix alone, checked by changing the letter read at 400 places (no context changed), and rerun. The leaked run is kept in the receipts under its own name, and the guess was not changed.

**The field's locked faces** (`cap_r.py`, `cap_s.py`; design's locked visits of the states ct8 and rt4, each place read with the other places locked, 43,470 places; the same places and letters as the rulers').

| Read | ct8 | rt4 |
| --- | --- | --- |
| Locked code | 0.552 | 0.529 |
| at unit starts (0.408 of places) | 0.677 | 0.656 |
| inside units | 0.465 | 0.442 |
| share of the code at unit starts | 0.501 | 0.505 |
| space-class, word letters, other | 0.224, 0.592, 0.872 | 0.216, 0.565, 0.847 |
| Correlation with the count law of two letters each side | 0.367 | 0.380 |
| Its surprise against itself 1, 2, 4 places on | 0.387, 0.299, 0.181 | 0.377, 0.292, 0.180 |
| 8, 16, 32 places on | 0.105, 0.072, 0.044 | 0.102, 0.070, 0.043 |
| 64, 128, 256 places on | 0.031, 0.007, 0.014 | 0.029, 0.007, 0.016 |

- The count law of two letters each side reads 0.576 on the same places: 0.825 at unit starts and 0.404 inside units.
- The field's surprise is more clustered than that ruler's at short range (0.30 against 0.21 at two places, 0.18 against 0.13 at four): its misses come in runs about a unit long.

**The product of the field's faces with a count law** (`cap_s.py`; the field's stored face at each place multiplied into the ruler's whole distribution and renormalized).

| Read | rt4 | at unit starts | inside units | ct8 |
| --- | --- | --- | --- | --- |
| The field alone | 0.529 | 0.656 | 0.442 | 0.552 |
| The count law of two letters each side alone | 0.576 | 0.825 | 0.404 | 0.576 |
| The field times that law | 0.389 | 0.609 | 0.237 | 0.391 |
| The field times that law's square root | 0.361 | 0.530 | 0.245 | 0.368 |
| An even mixture of the two | 0.390 | | | 0.395 |
| The field times the square root of four left letters' law | 0.390 | 0.584 | 0.256 | 0.401 |

- Multiplying a local count law into the field's faces takes 0.14 nats off the whole locked code and takes the interior of a unit from 0.44 to 0.24. This is the product test of the guide's ruler rule, repeated on the states ct8 and rt4 from the evening's read of earlier states (the chord record, 2.8), with the split by unit added. Its reading stands: the field does not hold the local joint law of two letters each side.
- The interior of a unit is the field's largest located lack on this passage. It is where the carry of §8.4 acts.

Design's line beside these (its report of 00:10 UTC): the part-rate arm's lap 5 reads 1.7544 on the held joint, and the plain arm ended at 1.7748 after lap 10.

### 8.3 Guesses and scores

All fixed in `guess_capacity_32_36.txt` before their reads.

- **G32a, the fitted strides** (fixed 23:55 UTC). Guessed separators 0.15 or more under the word letters, 0.50 against 0.75, and the newline among the three lowest. Read 0.43 against 0.86 at four letters on 64 circles, the newline lowest in all four fits. Held, and stronger than guessed. The rule's reading: the fitted strides stop at separators.
- **G32b, founded units by count.** Guessed 1,500 units to read the carried word's 1.608; read about 5,300, a miss by a factor of 3.5, between the rule's two readings (4,096 or fewer; over 16,384), so the rule is undecided. At `c = 64`: guessed 8,000 units and 1.33; read 26,155 and 1.3458, the code held and the count missed. To eight letters at `c = 64`: guessed 1.15, read 1.2600, missed. All units: guessed 1.05, read 1.1661, missed.
- **G34, reach at the unit grain** (fixed 00:10 UTC). a) Share of the four-letter code at unit starts: guessed 0.62, with 1.90 at starts and 0.80 inside; read 0.613, 1.902 and 0.809. Held. b) The unit chain at four levels: guessed 1.20, read 1.0505; at eight: guessed 1.14, read 1.1016. Missed low; the rule held (under 1.21, so at the field's four ticks mates at unit boundaries read more than mates at the next letter). c) Four letters then units: guessed 1.16, read 1.0504, which is 0.198 under four letters where 0.09 was guessed. The rule held: the coarse grain is worth its build. d) The letter chain to twelve and sixteen letters: guessed 1.155 and 1.150, read 1.2965 and 1.4247. Missed: the unpruned chain rises.
- **G31, the field's surprise against itself** (fixed 23:46 UTC in the navigation record). Guessed 0.03 or more at 64 places and 0.02 or more at 256. Read 0.031 and 0.029 at 64 (5.8 and 5.4 standard errors), and 0.014 and 0.016 at 256 (1.8 and 2.2). Held at 64 on ct8, short by 0.001 on rt4, missed at 256. By its rule it is undecided, and no further read is owed on it.
- **G35, where the field's locked code falls** (fixed 00:18 UTC). Guessed a share of 0.62 at unit starts, 0.82 there and 0.34 inside, and a correlation of 0.75 with the count law. Read 0.50, 0.68 and 0.66, 0.47 and 0.44, and 0.37 and 0.38. Missed throughout: the field's code is spread more evenly than the ruler's and follows it less.
- **G36, the product** (fixed 00:19 UTC). Guessed 0.40; read 0.389 and 0.391. Guessed the ruler alone at 0.80 at unit starts and 0.42 inside; read 0.825 and 0.404. Held. The rule's reading (0.45 or under): the field does not hold the local joint law of two letters each side.

### 8.4 The amended ruling

[ruling; theory, November 11, 00:22 UTC, sent to design; the definition of an attempt, unbuilt]

The carry stays, as the interior of a unit. It runs to its stop inside one tick, and its stride is read by a chart of its own.

- `g = G r̂`: a third chart beside `A` and `B`, `f × D` numbers (4,096 at `f = D = 64`), founded at zero, a part of its own under the part rates, complex as `a` and `b` are (`g_e + i g_(f/2+e)`). `κ_e` of §2.4 is dropped.
- `γ_e(t) = g_e(t) / (1 + |g_e(t)|²)^(1/2)`: the chart of the open disk, so `|γ| < 1` and every stride contracts.
- At even `e`: `Q_e(t) = b_e(t) + γ_e(t) Q_e(t−1)` and `p_e(t) = a_e(t) Q_e(t−1)`. At odd `e` the same with `t + 1`. `Q` starts at zero at the region's edge. `W` reads `p` where it read `c`.
- Unrolled: `p_e(t) = a_e(t) Σ_(j≥1) (Π_(0<i<j) γ_e(t_i)) b_e(t_j)` along the mates `t_j`. This is §2.2's moment on each circle, with the stride `γ` and the deposit `b` read from each site's own face.
- **Founding.** At `G = 0`: `γ = 0`, `Q = b` and `p_e(t) = a_e(t) b_e(mate)`, the built contact bit for bit. Every site begins as a stop, and deposition on `G` opens the strides where carrying lowers the code.
- **The adjoint** runs the scan backward with the producing operands; `Q` is a forward carrier of the tick, and nothing is kept across ticks:
  `δa_e(t) += conj(Q_e(t−1)) δp_e(t)`;
  `δQ_e(t−1) += conj(a_e(t)) δp_e(t) + conj(γ_e(t)) δQ_e(t)`;
  `δb_e(t) += δQ_e(t)`;
  `δγ_e(t) += conj(Q_e(t−1)) δQ_e(t)`;
  `δg = δγ / (1 + |g|²)^(1/2) − g · Re(conj(g) δγ) / (1 + |g|²)^(3/2)`.
- **The order of products is declared.** The moves compose associatively over the ring, so a card may lay the scan out as a tree. At declared widths each product is released, and released products do not associate bit for bit, so the bracketing along the strand is declared once and is the same on host and card.

The reasons for the amendment:

1. A unit is as long as its stops allow. One site a tick holds five letters at `K = 4` and no unit of units. A scan holds a unit of any length inside one tick, and its length is the strides' own contraction.
2. The stride is its own read. §2.4's stride `κ_e a_e` tied a site's stride to its reading, so a site that receives strongly would also pass strongly. The ruler's strides were tables of their own, and what they located (§8.2) is the letters that stop.
3. The built field already has the restricted form (`tower.field-pace`: one real rate a class a paced head, on the opening moment). The scan is the same object on the contact's circles, with the stride complex, read from the face a tick has made, and one a circle.

[derived, in form; unmeasured] What each tick composes. Tick 1 composes letters up to their stops, and `W` writes each site's unit so far into its face. Tick 2 reads its strides and deposits from faces that hold units, so a circle whose strides stay open inside units composes units into larger units. `K` ticks give up to `K` grains by one law, with no boundary told and no second field. This is the tower of scales as the carry's own bracketing, which is the landmark tower that `scale.rs` deferred. If the strides do not locate stops (G30′'s last clause), packets with sites of their own are the next object, with their boundaries read from the strides.

**G30′** (fixed 00:20 UTC, unread). Four laps from rt4, beside the part-rate line's laps 5 to 8: the third letter passes 0.21 or more (now 0.169); the fourth 0.06 or more (now 0.029); letters five to eight together 0.03 or more; the held joint ends 0.02 or more under the line's at lap 8; the locked code inside units ends 0.02 or more under the line's (rt4: 0.442; theory reads design's visit); mean `|γ|` is 0.08 (0.05 or more: the carry opened; under 0.02: it did not, and travel binds); and on 6 of the 32 circles the mean `|γ|` at separator sites is 0.7 or less of that at word-letter sites (4 or more: the strides are locating units; none with the strides open: place strides, units not located).

**G33** (fixed 00:20 UTC, unread; a host read of rt4). Each paced head's rate `1 + c_h[u]` by class: the separators' mean rate over the word letters' is 1.3 on the stronger head. 1.5 or more, or 0.67 or less, on a head: that clock already stops or idles at separators, and the opening moment is cut into units there. 0.8 to 1.25 on both heads: the clocks are place clocks in effect.

### 8.5 What does not transfer

- **The ruler's cut.** Units cut by the kinds of letters are the ruler's instrument and this codec's. The machine is told no boundary and no kind. A stride is read from a face by `G`, and deposition locates it.
- **A vocabulary or a merge table as machinery.** `hnn.founded-units` stands as a founding ruler. As the input codec, founded units blocked the copying of numerals on October 31, so bytes stay level 0. The tokenizer's discipline leaves behind its authored vocabulary and its merge table; what transfers is that a token is a composite move, that composition telescopes, and that a stop is a contraction.
- **Count tables.** The context trees here hold millions of cells indexed by content. They are rulers.
- **Other terrains.** The scan composes whatever the faces hold along a strand, and a strand's mates belong to the boundary codec: an image's strokes, a sound's partials and a motor word's screws are composed by the same law at their own strands. Each owes its own read; the figures here are of bytes of the code passage.
- **Against the lessons.** No tokenizer or grammar is authored: the stops are located by deposition. No window of offsets: the scan's reach is the contraction of its own strides. No cache: the carried state has a balance and a port (§8.1). Text on its codec's grain is not the exception: the law is stated on strands and strides, and the kinds of letters appear only in the ruler. The attempt enters a run only with its card realization, its parity and its adjoint.

### 8.6 Owed

- Design: the amended attempt on host and card with its parity; G30′; G33.
- Theory: the locked visit of the attempt's state read inside units (a clause of G30′); the scores of G30′ and G33.
- Theory: the unit-grain ruler for both sides, and a ruler whose stops are located from fitted strides in place of the kinds of letters.
- Lean, for #410: associativity of `(A₂, m₂) ∘ (A₁, m₁) = (A₂A₁, A₂m₁ + m₂)` and the telescoped moment over any bracketing; `m(l ++ w) − m(l′ ++ w) = A(w)(m(l) − m(l′))`; `|g / (1 + |g|²)^(1/2)| < 1`.

## Receipts

Device: host rulers on the PC's VM (2 cores, 3.9 GB), no card and no learner run. Each fit ran in calls of at most 180 s with its state saved between calls; the projection was 100 s a call and each call ended at 99 to 105 s. The rulers read a private passage, so only aggregate codes are published.

In `*_receipts/` (`README.md` there lists every file):
- `cap_n.py`: the pair-only reader and free factors by offset.
- `cap_o.py`: the word of shared strides, with its gradient checked against finite differences before the first fit.
- `grip_readers.log.txt`: the final line of every fit.
- `guess_capacity_28_30.txt`: G28 to G30 as fixed, with their times.
- `cap_p.py`, `cap_p_strides.log.txt`, `cap_p_units.log.txt`: the fitted strides by kind of letter, and founded units by count.
- `cap_q.py`, `cap_q_letters.log.txt`, `cap_q_units.log.txt`, `cap_q_read.log.txt`: the letter chain and the unit chain; `cap_q_read_leaked_first_run.log.txt`: the first run, whose contexts saw the kind of the letter read.
- `cap_r.py`, `cap_r.log.txt`: design's locked visits, the field's surprise against itself, by unit start and by kind.
- `cap_s.py`, `cap_s.log.txt`: the field's stored faces multiplied into a count law.
- `guess_capacity_32_36.txt`: G32, G34, G35, G36, G30′ and G33 as fixed, with their times.

The reads of §8 ran on the same VM between 23:55 and 00:20 UTC, each inside one call of at most 180 s; the tables took 8 to 20 s each.
