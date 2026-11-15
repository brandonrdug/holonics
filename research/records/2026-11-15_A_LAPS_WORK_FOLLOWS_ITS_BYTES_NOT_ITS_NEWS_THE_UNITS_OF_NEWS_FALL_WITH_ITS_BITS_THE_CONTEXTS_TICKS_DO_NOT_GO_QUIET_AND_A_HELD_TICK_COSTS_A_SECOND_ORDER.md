# A lap's work follows its bytes, not its news: the units of news fall with its bits, the context's ticks do not go quiet, and a held tick costs a second order

November 15, the Opus PC thread, from Brandon's messages of 20:26Z (streaming as a yardstick; a lap should accelerate as the field
compresses; "you've not reported it becoming indifferent to any particular combinations through compression"), 20:35Z (whether a basin's
loudness follows the contemporary attention), 20:42Z (the unit is not the byte: shapes coarse-grain, and that is compression) and 20:51Z (no
law "picks the top": density and thermodynamics), with the theory thread's laws and guesses of the same evening ([its record](2026-11-15_THE_RETURN_RUNS_ON_THE_CLOCK_OF_NEWS_A_HELD_TICK_COSTS_NOTHING_EITHER_WAY_AND_A_BASIN_IS_AS_LOUD_AS_ITS_PRESENT_DRIVE.md),
#851, #854). Every reading here is a ruler's on the host or a profile on the card; no law reads it. Receipts:
[`receipts/2026-11-15_news-clock/`](receipts/2026-11-15_news-clock/).

## 1. A lap's volume and rate

A lap of the line is 3,000 sections of about 41,400 places, 122 million places, each one octet of the passage: about 122 MB, 12% of the 1 GB
prefix. The first pass over the prefix ended in lap 37 (8.2 laps); lap 38 began the second. Training runs about 64,600 places a second
(forward, return and deposit), so a lap's work is fixed by its octets: every section costs about 630 ms whatever its code, from lap 33 to 40,
while the held code at lap means fell 0.8030, 0.8006, 0.8001, 0.7983, 0.7970, 0.7961, 0.7954 nats a place.

## 2. Where the news is (lap 38's held read, at its mean)

By the held places' fifths of surprise, the two quietest fifths carry 0.000 to 0.006 and 0.003 to 0.037 nats each: 40% of places hold 0.1%
(code) to 1.1% (books) of a region's nats. Each of them still takes the full contact every tick.

## 3. Loudness against the contemporary context (Brandon, 20:35Z)

(`context_loudness.txt`, `impulse.txt`, `impulse_within.txt`.) A place's loudness carries from the place before it (rank correlation +0.39 to
+0.67 by region), and a third to a half of a frequent three-octet piece's loudness variance is its context's. In the four prose regions it is a
groove: a well-coded place is loudest after a well-coded one and a surprise just before quiets it by 0.11 to 0.16 octaves, recovering within
about three places inside a document. In wikidata it is a trigger: loudness rises after a surprise (+0.08 octave at one to four places, half by
six). The offsets that stood at every lag to 64 in code and wikidata were documents louder throughout (gone within a document), and so was
code's rebound at six to ten places. The theory thread's guesses on these are scored in its record.

## 4. The news's standing spread (`sigma.txt`)

`|c_end − c_mean|` per held place between lap 38's end state and its mean: medians 0.009 (code) to 0.073 bits (wikidata), about a quarter of a
place's own news through the three quieter fifths and flattening near 0.34–0.39 bits in the loudest: one logit temperature (the theory thread's
reading). The share of places a news clock at `σ` returns (the held read, each stretch scanned alone): at 1/16 bit code 0.514, books 0.768,
science 0.729, web 0.738, wikidata 0.803.

## 5. The units of news across laps (`units.txt`, Brandon's 20:42Z correction)

The unit is the field's composed one, not the octet. Read as `P(σ)` of atlas `code.site-isolation-landmark` (a place no larger news stands
within `σ` of, on the clock of news) on the held passage at every kept lap mean, 14 to 38: at 8 bits a held place costs 0.051 (code) to 0.103
(wikidata) units at lap 38, 0.54–0.55 of the bound `S/σ` in every region (one site per two sections of news, the theory thread's reading). From
lap 14 to 38 the units fell 4.1 to 8.5% by region while the bits a place fell 5.0 to 8.2%: the units follow the news. Over the last five laps
the fall is inside the count's lap-to-lap spread of about 1%.

## 6. What each site's tick moves (`tick_news_end38.txt`)

On the host, from lap 38's end state over the six sections the line trains next (1,095 regions): for each written (definite) site and tick,
`a = ⟨λ^(k+1), x^(k+1) − x^k⟩` on `2^(−40)` bits, the code's first-order move were the site's tick held. At 1/16 bit the held share of written
sites is 0.39–0.51 at tick 0, 0.50–0.62 at tick 1 and 0.71–0.78 at tick 2, carrying 2%, 3–4% and 5–7% of the move; at tick 3 every written site
moves nothing (`λ^(4) = 0`: no face reads their final state). Compared (open) sites keep their ticks (7–21% held, about 1% of the move).
The last tick at written sites is unread work, but not all of it: an open site's pair contact at tick 3 reads its strand mate's tick-3 face, so
only the written sites' own pair contact and maps, and the whole tick where both strand mates are written, are unread. Read directly
(`unread.txt`: a site whose contact current no reader returns to, `δỹ = 0` at every head), that is 0.56 to 0.63 of the written sites at
tick 3 (about 0.4 of all sites: the compared places come in masks, so a written site's neighbours are written more often than at random)
and none at ticks 0 to 2; on the card's profile by tick (§9) their rows are about 22 ms of a section's 633. No mask of the strand
keeps those bits, though (`strand_rule.txt`): the rule "a site's row is read iff it or a strand neighbour is open" calls 3,972 to 18,324 sites
a region unread whose currents are read, through the carry circles (the line declares 32), whose scan carries `Q(t) = κb(t) + release(γQ(t ∓
1), 30)` along the whole strand. The unread set is the scan's releases rounding the carried term to zero over distance, which is dynamic and
unknown before the tick runs; `Declaration::room_window` refuses cut rooms with carry circles for the same reason. What is unread at every
written site at the last tick is only the work after the scan (its own products, the last map and bias into `x^(4)`).

## 7. A held tick costs a second order (`held.txt`)

The forward read again with every written site-tick of `|a| < σ` held (the oracle) raises the compared places' code, per written site summed
over ticks, 0.0015 to 0.0046 bits at 1/64 bit and 0.014 to 0.020 at 1/16. `Σa/Σ|a|` stays within ±0.12 (the held moves cancel to first order),
so the rise is second order and nearly one-signed. Held by the chart's move instead (a criterion the forward can read), the same count holds 5
to 19 times the oracle's `|a|` mass and costs 3 to 10 times its code: a site's own move is not what its readers feel.

The two second orders are told apart by holding half the set (`halves.txt`: two complementary halves by a fixed mixing of site and tick,
1/16 bit). Each half raises the code 0.18 to 0.33 of the whole set's rise (code 0.325 and 0.274, web 0.285 and 0.291, science 0.178 and
0.260, books 0.315 and 0.181, wikidata 0.244 and 0.318), never near a half, and the halves sum to 0.44 to 0.60 of it. So the rise is the
crowd's: held moves that share a reader, quadratic in their sum (`½(ΣΔ)ᵀG(ΣΔ)`), not each step's own curvature, which would halve it. The
theory thread's guess of 0.25 to 0.40 a half held in eight halves of ten. Held a tick at a time (`bytick.txt`), the single ticks' rises sum to 0.33 to 0.58 of the
whole set's: the strain is mostly across ticks too, held moves at one tick compounding with those of the next at their shared readers. The
first tick is the dearest to hold in every region though it carries the least of the move (code 308.9 bits over the six sections at tick 0,
245.3 at tick 1, 29.0 at tick 2, against 1,287.9 for all).

The carry the crowd asks for (`carried.txt`): a held move shown stale for one tick and added once the next tick has run. It takes 0.34
to 0.62 of the drop's rise away at 1/16 bit and 0.09 to 0.46 at 1/64, leaving, in nats a compared place, code 0.0120 and 0.0038, web 0.0065
and 0.0010, science 0.0094 and 0.0029, books 0.0077 and 0.0017, wikidata 0.0179 and 0.0023 (1/16 and 1/64 bit). Against the theory
thread's acceptance of 0.003 nats a place only web and books pass, and only at 1/64 bit, where 18 to 28% of written sites' first tick and
26 to 37% of their second are held: a carried move still lands on readers whose own moves then compound.

## 8. Training makes the context's ticks louder, not quieter (`tick_news_mean38.txt`, `tick_news_mean14.txt`)

On the same sections with lap 14's last mean and lap 38's as the field, the held share at 1/16 bit fell at every written tick in every region,
by 0.001 to 0.023, and the mean `|a|` at ticks 1 and 2 rose 1 to 7%. The compared places here code about 4.2 bits each, where the covector is
saturated (`‖g‖₁ = 2(1 − p̂)` changes 1% for 6% less code), so the readers' pull did not fall with the bits and the field put more of its code
into its context's depth. On this line a lap's acceleration stands at the units (§5), not at ticks held at a fixed `σ`.

## 9. The card by tick, and the limbs build's mix (`card_profiles.txt`)

A section's kernels by tick (6 sections, 633 ms): the forward 25% (6.2–6.4% a tick, each led by the forward contact), the return 59% (10.7%,
14.7%, 19.5%, 14.4% at ticks 0 to 3, each led by the rows, the columns and the skin's return), the rest 15%. The forward contact without the
host's multiplier (#852) launches at l3 192 times (347 µs a launch, the cheap ones), l4 380 times (3,362–3,394 µs) and l5 4 times, against the
control's 574 at l5: its entry reads 0.86–0.91 of the control over 24 sections, the section 0.993. Its numerators' cost a term is the value and
skin loads and the 128 × 64 product, which the limbs do not shorten. A build that took the term's products and the skin's carry on 32 × 32 products where their words fit (branch
`claude/contact-narrow`, set aside; `narrow_hold.txt`) was equal at gate 3 and read 1.02 of the limbs build in the forward contact and the
rows, 1.000 to 1.004 a section within a card state: the products are not what binds the numerators, and P59's staging (every source row
the warp's own, 0.951) showed their loads' places barely do. The compiled kernel (ptxas on the line's PTX at `sm_89`) says what does: at
its bound of six resident blocks of 128 threads the forward contact gets 80 registers and spills through its whole walk (300 to 464 octets
of spill stores and 684 to 940 of spill loads at three to five limbs; 199 local loads and 96 local stores in the four-limb entry's code),
where at four blocks it takes 120 to 128 registers and spills nothing (the four-limb entry 8 octets). A build at four blocks
(`claude/contact-blocks`) is gated and timed after lap 42.

## 10. What it says

The work follows the octets, and the news is elsewhere: 40% of places carry about 1% of it, the units of news are 5 to 10% of places and fall
with the bits, and the written sites' later ticks move the code little. Holding a quiet tick is not free: the held moves meet at their readers
and cost a second order, and the half-set read names the crowd at the shared reader, which a carry at the reader (the theory thread's clock of
news) is built to answer. Carried one tick, the held moves still cost more than the acceptance allows wherever they hold a
useful share: the context's ticks carry the field's learning (§8), and the place where the line's cost can follow its news is the level
whose sites are the units (the composite level, with places run whole by their news under the unit's continuation and never by a face's
top), whose count falls with the bits (§5).
