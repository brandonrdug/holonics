# A symbol is a length: a byte is a digit of the passage, a text's primes are its primitive cycles, and a stride is read at its place, as the news clock of October held

Refs #404 #406 #410. Status: [lens, measurement and recovery; November 12], by the theory thread
that holds the PC's runs and the engineering. The measurements are one table read on the PC's host
(the store's paces, R1 of G118) and one count ruler on a cloud host over public shards (R2 of G118
and G119). The design statements of §8, §10 and §11 are agent-inferred and nothing of them is built.

Owners named: the paced clock of the November tower (`crates/holonics/src/hnn/tower/field.rs`:
`Paces`, `Scale`; atlas `tower.field-pace`, `tower.field-scale-packets`), the news clock of the
October tower (`holonics::hnn::tower::NewsClock`, `NewsClock::above`, `Tower::join_news`,
`face_code`; Lean `HNN/NewsClock`; atlas `hnn.tower-news-clock`, `hnn.tower-news-clock-carry`,
`tower.packet-input`, `tower.participation-on-news-ticks`), the moves of a strand
(`navigator.content-stride-moment`, `navigator.unit-composite-move`) and the cycle machine (Lean
`Landmarks/PrimeCycles`, `Compression/Landmark/PrimitiveCycle`; atlas `landmark.cycle-machine`,
`rh.prime-cycle-machine`, `landmark.euler-product`, `arith.fermat-ring-partition`), and for §11
the colours of a ring and the step in time (atlas `colour.*`, `aeon.a4-entropy-clock-change`,
`motion.squeeze-ratio-dilation`). Three atlas rows enter, `code.epoch-cut-own-length`,
`code.news-clock-proper-time` and `code.stretch-unit-orbit`; `tower.field-pace`,
`tower.field-scale-packets` and the charts of character sets and of music are amended. Receipts sit with the symbol record's
([the record](2026-11-12_THE_STORE_CODES_HELD_TEXT_AT_THE_LEVEL_OF_TWO_KNOWN_NEIGHBOURS_A_SIDE_A_SYMBOL_IS_A_WORD_ON_LOCATED_RINGS_AND_A_DARK_PLACE_IS_THE_INTERIOR_OF_A_COMPOSITE.md),
whose §8 and §11 this record continues): `store_paces.py`, `store_paces.txt`,
`epoch_cut_ruler.py`, `epoch_cut_ruler.txt`. The guesses G118 and G119 and their scores are in the
guess file of the line.

## 1. Why this record exists

The symbol record's §8.8 said that the repository already held a symbol's word, from October 5,
and that the first deposit had presented it as new. Brandon answered that correction in three
messages between 22:50Z and 23:01Z of November 12. In my words, with the reasons as I read them
(agent-inferred):

1. A design that turns out to exist already is expected. Months of work have passed through most
   of the patterns theory now thinks to propose, and a method is often not recognized as one
   already used. That is why he asks for unification.
2. Unification is the recognition of one abstraction in the computational mathematics. It is
   weaker to look for existing parts to connect. The methods of two disciplines are one
   computation under two notations, and the notation and the discipline's label make the
   distinction. He leans on physics because its laws are the ones information propagates by: the
   correct physics paints the correct information.
3. Symbols are combinatorially unique elements, as the natural numbers are. A numeral system is an
   ordered system of places whose symbol holds one of a few states; an arithmetic operator is a
   pattern that disperses those states relative to each other; a symbol alone means nothing and
   does nothing, and something has to decode it and use it in relationships. A glyph is a rendered
   geometry, which he raised for its combinatorial potential and primality and never as an input
   to learn from.

Two statements of mine were wrong inside that hour, and both were told to him within minutes:

- "What does not transfer from the zeta: its lengths are fixed and commute, a text's depend on
  what came before." The sentence paired a text's bytes with the primes. §3 gives the pairing.
- "The clock is then the running description length; that step is my inference and unbuilt." The
  tree has held that clock since October 27. §7 reads it.

The second is the day's second design presented as new and found in the tree under another name
(the first: the symbol record's §8.8). The repair to the guides is in §9.

## 2. The object: a symbol is a length

A turned head of the November tower carries a moment that each occurrence moves by
`m ← α(u) m + β(u)` (`navigator.content-stride-moment`), and on a paced head
(`tower.field-pace`)

```text
α(u) = ζ_n^(−κ(u)) · e^(−2π|κ(u)|/n) = exp(−s_n κ(u)),   s_n = (2π/n)(1 + i),   κ(u) > 0,
m_t = Σ_(k≤t) β(u_k) · exp(−s_n (τ_t − τ_k)),            τ_t = Σ_(k≤t) κ(u_k).
```

So a paced head's table of rates is a table of lengths `ℓ(u) = κ(u)`, an occurrence multiplies
the carried moment by `exp(−s ℓ)`, and a mode of period `n` reads the strand as a series in
`exp(−s τ)` at one point `s_n` (a general Dirichlet series, with the clock's values its
exponents; the plain clock `κ ≡ 1` is the power series; the name is from training). The real part
of `s ℓ` dims what came before and the imaginary part turns the phase. The `1 + i` ties the two
one to one, which is the built skin's choice.

That expression is one law on four charts:

| Chart | The factor `exp(−s ℓ)` | The length |
|---|---|---|
| A layered medium | a slab's transmission, absorption and phase | optical depth |
| A chain in a bath | a link's Boltzmann factor in a transfer matrix | energy over temperature |
| A code | a codeword's share, `Σ exp(−ℓ) ≤ 1` (Kraft) | code length, `−log p` |
| The integers | `p^(−s)` | `log p` |

The tree holds the last row as machinery of its own, formal-checked: a cycle machine with a site
a primitive cycle carrying `exp(−s · length)` has the Euler product as its transfer determinant
(`landmark.cycle-machine`), and with `ℓ_p = log p` its inverse determinants tend to `ζ(s)`
(`rh.prime-cycle-machine`). That a paced head's table is such a table of lengths is agent-inferred
from the two rows' expressions; no code joins them.

## 3. Two layers, the same in numbers and in text

**The numeral.** A numeral is places, each holding one of `r` states. A digit's value is given by
its place and by the receiver's radix, never by its state alone: order matters, and an operator
acts on numerals by dispersing states across neighbouring places through carries. A passage of
bytes is a numeral in base 256, and a byte is a digit of it. The class of a byte is the state of
a digit.

**The arithmetic.** Under the numeral stand the number's relationships: its factorization, whose
primes commute and are unique. For strings over `a` states the primes are the primitive cycles of
the shift, and the tree counts them (`arith.fermat-ring-partition`, with
`landmark.euler-product` formal-checked for a finite map):

```text
P_n = (1/n) Σ_(d∣n) μ(d) a^(n/d) ≈ a^n / n,        1/(1 − aT) = Π_n (1 − T^n)^(−P_n),
1/det(1 − TA) = Π_γ (1 − w(γ) T^|γ|)^(−1)          (γ the primitive cycles of a transfer matrix A).
```

With a cycle's norm `N = a^n` the count is `N / log_a N`, the prime number theorem's form. With a
transfer matrix the weight of a cycle is the product of its transitions' weights (the weighted
form is from training; the tree's rows hold the integer case). So a length that depends on what
came before is no exception to the product: the dependence sits inside each prime's weight.

**The corrected sentence.** Dependence on context and the order of symbols belong to the numeral
layer, which numbers have too (12 is not 21, and a carry reaches its neighbour). Fixed, commuting
lengths belong to the arithmetic layer, which a text has too (its primitive cycles). The sentence
of §1 compared one layer of a text with the other layer of the integers.

**The decoder.** A digit enters a relationship through a receiver whose rings step on it: the
receivers' frames of the helical code read residue, whole winding and epoch, and October's located
transport steps the rings by the symbol's located advance (the symbol record's §8.8).

**What follows as a test.** A value fixed to a symbol whatever its place (one constant a class) is
the numeral's error of valuing a digit without its place. So a clock whose stride is one constant
a class should fall nearly blind to where a text's news lies, and a clock whose stride is read at
the place should not. §5 and §6 read both.

## 4. What the trained strides hold (R1; G118 (a) held)

`store_paces.txt`, read on the PC's host from the store's state A (the crossing) and state C (the
mean of states at pass section 5,001), a row a class with its byte value and its rate `1 + c` on
the two paced heads (the receipt names them heads 2 and 3). Its checks pass: the layout's total is
the material's 117,478 on both states, the 144 classes that open text added all read a rate of 1
at A, and the open row reads 1 at both.

| At state C | Head 2 | Head 3 |
|---|---|---|
| Spread of the code line's 99 rates (standard deviation) | 1.167 | 1.687 |
| Mean rate of the ASCII letters | 2.414 | 2.689 |
| The newline | 4.396 | 14.456 |
| The space | 2.856 | 2.196 |
| The largest of the code line's classes | `[` at 6.613 | the newline |
| Median of the rate's distance from 1, the code line's classes | 1.856 | 1.843 |
| The same, the 144 classes open text added | 0.035 | 0.017 |
| The largest of those 144 | 1.121 | 1.230 |

On the head of larger spread the newline is still the longest of the code line's classes, 5.38
times a letter's mean (G33 read 4.96 on the code line on November 11; the guess was 4.5, bound 3
or more). The classes open text added have barely left the plain clock after 5,001 sections,
where the code line's stand 1.8 from it. Both parts of G118 (a) held. State A reads within 0.25 of
state C on every code line's class: these are the code line's strides, carried onto open text.

## 5. Where their carries cut held text (R2; G118 (b) missed)

The ruler (`epoch_cut_ruler.py`; counts on 16 to 32 MB a slice of one public shard, held places
the first 330,000 a slice of another, through the store's rule for pieces). A place's code is the
count ruler's, the two bytes before it known (Witten–Bell). A cut by strides sums a head's rates
along a piece; an epoch closes where the sum crosses a multiple of one period, and the next place
opens one; the period is fitted by slice so that the mean epoch is 6 places, the built packets'
length. Beside it: packets of a fixed 6 places, and a cut that opens an epoch at each place whose
code stands in the slice's top sixth. A piece's first place and void places are left out of every
mean. The mean code of the opening places over the mean code of the others:

| Cut | Code | Web | Science | Books | Wikidata | Pooled |
|---|---|---|---|---|---|---|
| Trained strides, head 3, state C | 0.961 | 1.020 | 1.033 | 0.996 | 1.071 | 1.018 |
| Trained strides, head 2, state C | 0.978 | 1.088 | 1.087 | 1.072 | 1.080 | 1.061 |
| Fixed packets of 6 | 0.998 | 1.003 | 1.005 | 0.997 | 1.007 | 1.002 |
| By the code itself | 3.496 | 2.894 | 2.795 | 2.761 | 2.801 | 2.936 |
| After a newline (a place in 30 to 104; books hold almost none) | 0.723 | 1.235 | 1.582 | 1.595 | 1.393 | 1.126 |

G118 (b) fixed 1.10 pooled (1.03 to 1.25) on the head of larger spread, with code the largest.
It read 1.018, and code the least: **missed**. The controls held (fixed packets within 0.01 of 1,
the cut by the code 2.76 or more). State A reads within 0.012 of state C on every slice.

Why the derivation missed. It took the place after a newline as bright. In code that place is
dark, 1.61 nats against 2.23 for the others (an indent follows a line's end). In prose it is
bright and rare. And 0.086 of head 3's openings follow a newline; the rest fall wherever the phase
of the summed strides happens to stand. G118's rule applies: under 1.05 in four of five slices,
so a class's one trained rate does not cut the strand where it is bright.

## 6. One constant a symbol against the place's own length (G119)

Fixed before its read, from §2 and §3. Three more strides on the same places and the same mean
epoch: `unigram` (a symbol's order-zero code length on the counts stream), `class mean` (the mean
two-back code of the symbol's held places; the best one constant a symbol the ruler can give) and
`own` (the place's own two-back code, so the clock is the description length). Both ends of an
epoch are read: the place whose stride carried (the epoch's last), and the place after it.

The mean code of the carrying places over the mean code of the others:

| Stride | Code | Web | Science | Books | Wikidata | Pooled |
|---|---|---|---|---|---|---|
| Fixed packets of 6 | 0.995 | 1.000 | 1.000 | 0.992 | 0.997 | 0.997 |
| Trained, head 2, state C | 1.044 | 1.078 | 1.075 | 1.009 | 1.073 | 1.057 |
| Trained, head 3, state C | 1.074 | 1.096 | 1.105 | 1.072 | 1.094 | 1.089 |
| Unigram length | 1.255 | 1.203 | 1.184 | 1.189 | 1.082 | 1.180 |
| Class mean | 1.392 | 1.271 | 1.254 | 1.272 | 1.209 | 1.277 |
| The place's own length | 2.025 | 1.688 | 1.659 | 1.623 | 1.636 | 1.720 |

The part of the read places' nats that the carrying sixth holds, and the spread of an epoch's
summed nats (standard deviation over mean, over the epochs whose every place is read; the mean is
13.8 nats):

| Stride | Share, pooled | Spread: code | Web | Science | Books | Wikidata | Pooled |
|---|---|---|---|---|---|---|---|
| Fixed packets of 6 | 0.166 | 0.474 | 0.353 | 0.350 | 0.296 | 0.377 | 0.379 |
| Trained, head 2, state C | 0.174 | 0.607 | 0.399 | 0.405 | 0.361 | 0.407 | 0.446 |
| Trained, head 3, state C | 0.179 | 0.627 | 0.406 | 0.388 | 0.300 | 0.452 | 0.452 |
| Unigram length | 0.191 | 0.370 | 0.300 | 0.311 | 0.271 | 0.423 | 0.348 |
| Class mean | 0.203 | 0.346 | 0.288 | 0.295 | 0.257 | 0.306 | 0.306 |
| The place's own length | 0.256 | 0.171 | 0.153 | 0.156 | 0.144 | 0.155 | 0.166 |

What it says.

- **A length read at the place carries the news; one constant a symbol carries under half of
  it.** The class mean's lift over a blind cut is 0.33 to 0.44 of the own length's on every
  slice (0.38 pooled). G119's rule: under half, so one length a class is a founding only, and the
  stride reads the place.
- **The trained strides spread an epoch's news worse than blind packets** on every slice (books'
  head 3 level with them). Their epochs differ in length without following the news.
- **On the own length an epoch's news stands within 0.14 to 0.17 of its mean**, where fixed
  packets stand at 0.30 to 0.47. That is "equal news a site" as a count.
- **The place after a carry is not bright under any stride** (own: 1.059 pooled; the class
  constants read under 1). An epoch's news sits on the place that closes it.
- **The trained rates are weakly lengths.** Their rank correlation with the unigram length over
  the code line's bytes with 100 or more read places: head 2 0.33, 0.43, 0.42, 0.49, 0.56 by slice
  and head 3 0.20, 0.39, 0.31, 0.51, 0.42; with the class mean 0.27 to 0.49 and 0.21 to 0.47.
- **By kind** (mean code, nats; code, web, science, books, wikidata): the space 0.62, 1.03, 1.04,
  0.83, 1.47; lower-case letters 2.26, 2.25, 2.23, 2.20, 2.59; capitals 4.59, 4.40, 4.33, 4.22,
  3.74; digits 3.91, 3.88, 3.03, 3.88, 2.83; ASCII punctuation 3.52, 4.12, 3.55, 4.19, 4.93; the
  newline 1.82, 2.51, 3.82, (books hold almost none), 2.91; bytes of 128 and over 3.64, 3.85,
  4.17, 2.66, 1.90.

Scores, pooled. (a) trained head 3's carrying ratio 1.089 (guess 1.12, 1.00 to 1.30): held. (b)
unigram 1.180 (1.25, 1.10 to 1.45) and class mean 1.277 (1.33, 1.15 to 1.55): held. (c) own 1.720
(2.3, 2.0 to 2.7) with 0.256 of the nats (0.32), and the opening place 1.059 (1.25, 1.10 to
1.40): **missed**, both low. The derivation took the code's deviation as 2.2 nats without reading
it; the carrying places' mean of 3.5 nats puts it near 1.7. (d) spreads: fixed 0.379 (0.45, 0.35
to 0.60), trained no less than fixed, own 0.166 (0.25, 0.15 to 0.35): held. (e) rank correlation
on code, head 2 0.33 (0.45, 0.25 to 0.65) and head 3 0.20 (0.30, 0.10 to 0.50): held.

Scope. The code is a count ruler's at two bytes back, on public text; the machine's face is its
own, and a size read here is the ruler's. A ruler's law is never the machine's.

## 7. What the tree already held: the clock of news

Read at source after §6, before anything was ordered: `hnn.tower-news-clock` and
[its record of October 27](2026-10-27_THE_LEVELS_TICK_ON_THEIR_OWN_NEWS_SO_THE_TOWER_LEARNS_ITS_ENCODING_ON_ITS_OWN_AXIS.md).

- **The law.** `c_t = face_code(p̂_(t−1), u_t)`, `S_t = Σ c_k`, and a level from `F` up ticks
  `Δτ_l(t) = ⌊S_t/σ_l⌋ − ⌊S_(t−1)/σ_l⌋` times, `σ_l = B r^(l−F)`: each level is a receiver whose
  clock counts its own news, its segmentation moves as the tower learns, and nothing names a
  class, a boundary letter or a modality. It was built on the host and the card for the October
  tower (`NewsClock`), asked for by Brandon that day as the tower's own encoding along its own
  axis. §6's `own` stride is this clock with a count ruler's code in the face's place.
- **Its carry.** A coarser level's count is the odometer's carry of the finer level's, its ticks
  lie among the finer level's, and they form an epoch tower: formal-checked in `HNN/NewsClock`
  (`hnn.tower-news-clock-carry`). §8.4 of the symbol record called a composite "an epoch of a
  paced clock" as a design; the carry law of that epoch was already proved.
- **Its race.** Under its first law the news race trailed the plain race by about 0.22 bit a
  class held out from lap 3, and by about 0.27 at its end. The cause found: two clocks, a drive at
  every arrival beside a move on the news clock, so a level's modes swelled to ten times the plain
  race's. The repair is the held step (the plain step once a tick, the arrival held; one clock).
  Clocked from level 1 the tower then read as a one-level tower (2.365 against 2.354 held out at
  lap 1), so the clock begins above the arrival stack (`NewsClock::above`).
- **What the November tower took in its place.** `tower.field-scale-packets`: packets of a fixed
  6 places, built on host and card, whose first reading missed its acceptance (the field record's
  §16.39), with the cut at landmarks deferred. And `tower.field-pace`: one rate a class, with the
  one clause that already reads the face, a blank's expected duration `1 + Σ_a p_t(a) c[a]`
  (§16.44).

So the day's rulers add two counts to a law the tree holds: the carries of one constant a class
are near blind to the news, and the carries of the place's own length even an epoch's news to
0.17 of its mean where fixed packets leave 0.38. They add no mechanism.

## 8. What follows for the machine (agent-inferred, unbuilt; each a test)

1. **The stride of a place is its length under the face it was given.** A written place takes
   `face_code` of its class under the face of the tick before; a blank takes that face's expected
   code, the form §16.44 already built for the class rates. The class rate stays as the founding,
   the stride before any face stands. The clock is then the strand's running description length,
   and the moment of §2 weighs what came before by the news that has passed since, never by the
   count of places: a predicted stretch dims nothing (Brandon's lens of 20:31Z the same day,
   `deposition.cost-follows-surprise`).
2. **A site of the level above is an epoch of that clock**, the span between two carries on the
   level's section, as `hnn.tower-news-clock-carry` proves it. It is the successor of the fixed
   packets, and a composite of the symbol record's §8.4 is such an epoch: a prime of higher rank
   whose own length is shorter than its bytes' lengths added.
3. **One clock.** October's first law failed on a drive and a move on two clocks. A stride read
   at the place moves the moment's clock and the level above's sites by the same sum.
4. **What does not follow.** No held code is promised: in October the clocked tower read level
   with a one-level tower at its first lap, and the fixed packets of November missed their
   acceptance. The design's acceptance is a structural measure first (the spread of an epoch's
   news under the machine's own face, against 0.38 and 0.17 here), with the held code by slice and
   kind at lap means beside it, and its guess is fixed before its build is read.

## 9. The recorded failures this line could repeat, and the guides' repair

- *A located cause carried unrepaired into a new consumer*: the November tower entered beside the
  news clock and the located transport, both unread. The design record names both as its
  ancestors and extends their tests to the tower's entries.
- *Text run on its codec's grain as the exception*: fixed packets of six places and one rate a
  class are the codec's grain. §8 removes both.
- *A design thought in the programming language*: a stride table indexed by a class is an array;
  §2 and §3 state the stride as a length on the strand.
- *Bits read as progress*: §6's lifts are a ruler's and no acceptance.

The guides (CLAUDE.md and AGENTS.md, "Recover before implementing" and "A discipline is a
chart") gain the lens of §1 with its occasion: a search names the operation under every
discipline's name for it, since on November 12 two designs were presented as new in one day and
the tree held each under another name.

## 10. Recognition is what a change of clock leaves, and the clock of news is the strand's proper time

*The lens* (Brandon, 23:11Z and 23:20Z the same day, in my words). The clock as a running
description length reads right to him, and its abstraction is the Doppler spectrogram of
navigation and music: a source one has met is recognized from a brief frame of it, by the
curvature of its spectral lines, whose continuation one can feel, and faster still when the frame
couples to a voice or a beat one holds. The frame's length is of no importance: the source is
recognized the same at twice its rate. No clock is privileged. His correction came on a line of
this thread's checklist that named a count ruler for "the text's own" frame length; that ruler was
withdrawn unread (G121).

*The search made first* (the guides' rule of §9). The tree holds the operation under four names.

- **A change of clock has no content.** `spectro.clock-gauge`: a receiver's clock scales every
  line alike, `s ↦ λs`; the invariants are the ratios `s_i/s_j` and the loss angles, and a uniform
  load is a clock. The music chart: identity is a pattern of ratios modulo a common shift
  (transposition, Doppler, renaming). `lorentz.doppler-ratio-chart`: a boost is the undivided
  pair `(k, k⁻¹)` and its log chart is the rapidity, so in the log chart a dilation is a
  translation and a pattern of lines moves whole.
- **A frame locates a key in a family the receiver holds.** `infer.excitation-identifies` (any
  nonzero excitation identifies a multiplier within a declared family), `unicity.residue-chain`
  (the readings needed are the key's size over what a reading tells), and the hypothesis that
  carries both, `infer.finite-prefix-alternatives`: no prefix identifies a continuation in an
  unrestricted family. After the key is located a reading is null (`unicity.null-reading`) and
  the clock of news stands still.
- **The continuation is in the frame's jet.** `arith.producer-jets` (producers of one face are
  parted by their jets along a clock), `birth.founded-against-hankel` (an emission's minimal
  realization has the rank of its Hankel form). That a law of `d` modes is then fixed by a prefix
  of the order of `d`, whatever the passage's length, is Kronecker's and Prony's classical
  statement (`from training`; no atlas row states it).
- **Driving a mode one holds costs nothing.** `compression.ride-free`: a drive inside a held
  mode's eigenspace needs no effort. That one drive tries every held mode at once, so that
  locating a held key is a check and never a search, is `agent-inferred`.

*What follows* (agent-inferred, unbuilt; algebra on the built expressions).

1. **The clock of news is the strand's proper time.** Let a re-timing insert places the reader
   predicts (a letter doubled where doubling is the rule, a wider gap). Their code is zero, so
   `S_t` at every original place and every carry `⌊S_t/σ_l⌋` are the original's
   (`hnn.tower-news-clock`): the epochs are the original's epochs. The count of places is a
   coordinate time, and `dS/dt` at a place, its code, is the Doppler factor between the two
   clocks. The fixed packets (`tower.field-scale-packets`) cut by the coordinate time: the same
   strand at another rate is cut into other packets, and the level above meets other symbols. So
   the fixed packets privilege a clock, and the clock of news is the one cut of §8.2 that does
   not. A recognized stretch is a stretch of null readings: it has no length on this clock, the
   moment of §2 crosses it unchanged, and what stood before it stays in contact with what
   follows (the lens of 20:31Z: predicted input goes dark, at the least mutual loss).
2. **A uniform change of rate is a shift along the ladder of modes.** With
   `m(s) = Σ_k β(u_k) exp(−s(τ_t − τ_k))`, the re-timing `τ ↦ λτ` gives `m′(s) = m(λs)`, and
   with `s_n = (2π/n)(1 + i)`, `λ s_n = s_(n/λ)`: ring `n` reads of the re-timed strand what ring
   `n/λ` read of the original. A strand is then recognized at another rate at no cost exactly
   when the rings of the ladder share their rows (the Holon's scale restriction commuting with
   its element relations). Today nothing is shared along it: each paced head trains its own
   table (§4: a newline reads 4.396 on head 2 and 14.456 on head 3). This is the symbol record's
   rule one level over (rows shared by every symbol at a residue, never free rows). The tree
   holds the ladder as a conjecture (the record of November 10: a ladder of moments at octave
   rates, if travel binds) and a bank of octave rungs for reach (`wave.matched-friction-reach`).
3. **A voice is a shared ring.** A key factors as its family and its member,
   `H(K) = H(family) + H(member | family)` (the residue chain's Lagrange factorization): a frame
   that fits a held family locates the member at the remainder's cost. A passage is a symbol of
   high rank whose word stands on rings it shares with its kind, and a new passage of a held kind
   costs its remainder to learn.
4. **The acceptance is an invariance.** A held passage and its re-timed copy, under re-timings
   the trained reader predicts, open the same epochs and code alike above the bytes; the measure
   is the share of the original's epoch openings on which the copy's openings fall, read against
   the fixed packets' share on the same pair. No frame length on any clock is an acceptance.
   Its guess is fixed with the design's.

*Where the store stands against it.* A release reads its nearest places and no farther: from the
fourth place on it codes at the level of the slice's own count of bytes (the symbol record's §3).
Nothing above two neighbours a side is recognized today. The partition that reads it (a place's
code by its distance to the nearest known place and by the count of known places of its piece) is
ordered (P53).

*What does not transfer.* The ear's logarithmic chart of frequency is a boundary codec's, never
the machine's law. A recognized item graded as a generation is the lessons' recitation; the
invariance is graded on kinds and on re-timed copies, never on items the machine has met. And
the encounter read as one pole in complex time (a project note of November 3, outside the tree)
is cited as a chart, with no claim made from it here.

## 11. A stretch is a step in time: the count is kept, the rate is exchanged, and the transition is ramification

*The lens* (Brandon, 23:27Z the same day, in my words). A passage played faster holds more news in
each packet of the same frame: an exchange that conserves. §10's sentence (what is recognized is
what a change of clock cannot touch) holds as far as the counts of counts are the same, and it
leaves out a geometry: a packing. Compression is no difference of two volumes. It belongs to the
temporal parameters of phases and modes, with their singularities. Atomic spectra and colour are
the same case: one recognizes consistent gaps; a shift of frequency changes the colour (the
pitch) and skews the shapes, a red shift, and it does not change the crossings of the
composition short of a phase transition. Expansion and contraction.

*The search, and its miss.* §10's search named the operation as recognition, identification and
jets. The tree holds the stretch itself under other names (dilation, colour, time boundary,
squeeze, entropy under a change of clock), and §10 was written without them. The guides' rule of
§9 names the operation under each discipline's name; here the operation was named once. The
rows, read before this section was written:

- **The exchange.** `aeon.a4-entropy-clock-change`: entropy an epoch is entropy a unit of clock
  times the mean epoch length (Abramov; Lean `Aeon/Production/Kac`, finite chains), so entropy is
  a density along an aeon that transforms by the ratio of clock readings.
  [The record of October 26](2026-10-26_A_GALOIS_GAP_IS_A_MODES_MOMENTUM_AN_ORBITS_GAPS_MULTIPLY_TO_ITS_PRIME_AND_A_TIME_BOUNDARY_IS_THE_PUMPED_MODE.md)
  §8: a step in time (the medium changed everywhere at once) keeps the wavenumber, which that
  record calls the colour, changes the frequency, and conserves the action (forward less backward
  quanta), never the energy; whatever changes the medium does the work. Its §6: a lossless
  parametric element conserves quanta and its pump supplies the difference of frequency, so
  energy and information separate, the work being the change of frequency and the reading the
  holonomy. `motion.squeeze-ratio-dilation`: the move is the squeeze `diag(λ, λ⁻¹)` at
  determinant one, and entropy is a trace term beside it. `clock.redshift-production`: a red
  shift is the undivided rate of two receivers' clocks. `holarchy.antiphase-strokes`: expansion
  and contraction as a pump across two surfaces.
- **Colours and their gaps.** `colour.ring-spectrum-orbits`, `colour.orbit-energy`: a ring's
  modes fall into orbits by their order `d`, a mode's gap is the chord `1 − ζ^a`, and an orbit's
  gaps multiply to `Φ_d(1)`, which is `p` when `d` is a power of a prime `p` and 1 otherwise;
  `log Φ_d(1) = Λ(d)` and `∏_(d|m, d>1) Φ_d(1) = m`. The record's §5: at `p` the colours merge
  (ramification), and only orbits of prime-power order carry potential energy.
  `colour.dilation-symmetry`: `x ↦ ux` keeps a ring's adjacency exactly when `u ≡ ±1`, a symmetry
  on those rings and a strain on the rest. `colour.trace-compression`: the trace over an orbit is
  the Ramanujan sum `c_n(j)`. The record's §6: a rotor that holds a whole orbit modulo the mirror
  is passive under the base's move, and a plane that holds part of an orbit needs a pump.
- **Two receivers part what one merges.** `wave.metamer-unison`.
- **A division keeps its fibre.** `ratio.inversion-fibre`.

*What follows* (agent-inferred, unbuilt; algebra on the rows above).

1. **A change of rate keeps the strand's news and exchanges density for extent.** With
   `S = Σ_t c_t`, a strand at rate `λ` has its places divided by `λ` and its code a place
   multiplied by `λ`, and `S` is the same. On the pair (extent, density) the move is the squeeze
   at determinant one: the area is kept and its shape skewed. The clock of news (§10.1) is the
   chart in which the density is one. So no stretch is a compression, and a compression is no
   difference of volumes.
2. **Compression is the receiver's quotient, and its length is carried at the singular orbits.**
   The code length of one residue of a ring of `m` is `log m` (a face flat over the ring), and
   `log m = Σ_(d|m, d>1) Λ(d)`: it is one mode's potential against the rest of the ring
   (`∏_(0<j<m) (1 − ζ^j) = m`), carried by the orbits of prime-power order alone, one `log p` a
   level of the tower over `p` (`colour.colour-tower`), where the other orbits' gaps are units
   and compose at no cost. The identity is the tree's; reading it as the code length is this
   record's join. A stretch by a unit `u` permutes each orbit in itself, so every `Φ_d(1)`,
   every trace (`c_n(uj) = c_n(j)`, the gcd being kept) and the code length stand: the counts of
   counts are the same, and the reading that survives every such stretch is the colourless one.
3. **The transition is ramification.** `x ↦ ux` on `ℤ/m` is `gcd(u, m)` to one: a unit permutes
   the residues and keeps every crossing, a nonunit merges them, and the reading loses at most
   `log gcd(u, m)` a residue; going back is the fibre of the division. On coprime rings a factor
   is a nonunit only on the rings whose prime it shares. On the located address's rings of
   today, (16, 27): a doubling is two to one on `ℤ/16`, one bit, and on `ℤ/27` it is a unit of
   order 18 (`2⁹ ≡ −1`), a permutation through the whole group of units. The built paced
   clocks hold strides on the grain `2^(−24)` and are no ring residues
   (`tower.field-pace`: the resident ring at a whole `τ`, the series between); the transition's
   form there (a line passing a ring's rate, two lines' gap falling under a width) is the design
   record's to state.
4. **Passive recognition holds the whole orbit, and the shift is a reading.** §10.2's sharing is
   sharpened: rows are shared along the units' orbits of each ring (the colour), and the unit
   that acted is located as a key of its own, `H = H(pattern) + H(unit)`: a red shift is read as
   a velocity and a transposition as its key, never thrown away. A reader holding part of an
   orbit pays the stretch as work (the pump).
5. **The acceptance gains a predicted failure.** Under a stretch by a unit of a ring a trained
   reader loses nothing on that ring beyond the unit's own code; under a nonunit it loses the
   merged residues' `log gcd(u, m)` on that ring and nothing on the coprime rings. A reader
   that loses at a unit holds rows by residue; one that loses nothing at a nonunit has met the
   copy. The guess is fixed with the design's.

*What does not transfer.* Vision's receivers and their anatomy; the cosmological metric; the
octave as an authored equivalence (the units are each ring's own, and 2 is a unit only of odd
rings). A stretch by a factor that is no integer is no dilation of a ring; it is the series
between whole turns.

## 12. What is owed

- **The design record of the symbol's line** (the symbol record's §11, restated by this record):
  the stride of §8.1 and the level above of §8.2 on the November tower, with October's news clock
  and located transport as its owners' ancestors, its device line, its acceptance and its guess.
  It is ordered beside the engine's steps and ahead of any long pass.
- **The invariance of §10.4** as the design's acceptance, with its guess and with the predicted
  failure of §11.5; **rows shared along the ladder of modes** (§10.2) **and along the units'
  orbits** (§11.4) as questions the design record answers before it sizes a part.
- **A reading of the store's own face in the ruler's place**: the same cut with the store's code
  of each held place (from `read-store`'s visits), on states A and C, outside any timing hold.
- **Lean (#410).** The paced moment as the cycle machine's weights (`α(u) = exp(−s κ(u))` and the
  series of §2); the weighted Euler product over the primitive cycles of a transfer matrix; that
  an epoch's summed length under the own stride stands within one stride of its section.
- **Image and acoustic checks**: the same cut on values, where a place's own length is read
  against one constant a level.
