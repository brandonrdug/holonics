//! **The declared extents: the head line and the constitution's loci.**
//!
//! the head line `hnn-field-v14…` (alphabet, width, heads, modes, still, contacts, ticks, frames, reach, lanes, depth, carry,
//! triads, opening, junction, mark, loud); `Loci` gives each block's offset and length in the material
//!
//! Kind: declarations, read once a field. Kernels: none (the card reads `Loci` at upload, `hnn/resident.rs`).
//! Lean: none.
//! Atlas: `code.symbol-word-located-rings`, `tower.field-growth-by-contacts`, `tower.field-growth-by-lanes`, `tower.field-moment`,
//! `tower.field-one-region`, `tower.field-open-row-pairs`, `tower.field-room-cut`.
//! Records: THE_CONSOLIDATION §10, `2026-11-01_THE_PROBLEM_IS_ONE_FIELD…`. The derivations' history is in the records; the items below keep their
//! reasons.

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use rayon::prelude::*;

/// [definition; agent-inferred, November 1] **The field's declared law**: an alphabet of `A`
/// classes (the face's; the encoding carries one more row, the unresolved operand), a face width
/// `D`, `H` heads of `n` complex modes each, `f` pair contacts and `K` ticks of the one
/// constitution; `frames`, the founding's heads, whose ring sets every grown head copies (head `h`
/// is of set `h mod frames`), the first `still` of them still (every mode unframed, reading the
/// word) and the rest turned (every mode on the solenoid's rings, [`ring_periods`]); and `reach`,
/// the most sites a region may span (the terrain's extent, read from the passages the field will
/// meet), which the rings' coarsest closures cover; and `lanes`, the registers the width is read in
/// (§16.40, the tower record's D2: each lane of `D/lanes` coordinates a ratio to its own power,
/// [`lane_chart`]; one lane is the chart over the whole width).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Declaration {
    pub alphabet: usize,
    pub width: usize,
    pub heads: usize,
    pub modes: usize,
    pub still: usize,
    pub contacts: usize,
    pub ticks: usize,
    pub frames: usize,
    pub reach: usize,
    pub lanes: usize,
    /// [definition; agent-inferred, November 6, the unified-theory readings of 04:34 to 04:47] **The depth rings**: the last
    /// `depth` turned ring sets turn by located increments alone. A depth head's rate is `κ = r_h[u]` on its class sheet (its
    /// pace row, base zero: only a located increment turns it, so a matched opener and the site before its closer differ by
    /// exactly zero, an unmatched one by its net winding), its frames turn at `τ = Σ κ` on the solenoid's ring periods, its
    /// pairs and crowds take no skin (`|μ| = 1`: relative depth carried exactly at any span, its adjoint exactly back), and it
    /// carries no moment (without a skin its moment would sum the whole region). The ring `ρ ← μρ + r` with `μ = 1` and `r`
    /// keyed by the arriving class; `r` is located by deposition, never authored.
    pub depth: usize,
    /// [definition; theory, November 11 17:25 (the follow-up record §9 item 4) and November 12 (G96's third branch, G98), `lean/Holonics/HNN/CarryGate.lean`]
    /// **The carry circles**: the last `C` of the `f/2` complex contacts carry the move `z → γ(t) z + κ(t) b(t)` along the strand inside one tick, each on
    /// a circle of its own; the first `f/2 − C` stay the built pair contact with their strand mate. On circle `k` (complex contact `e = f/2 − C + k`) the
    /// scan runs in strand order (`Q` zero before the region's first site): even `e` from the left, `p_e(t) = a_e(t) Q_e(t−1)` and `Q_e(t) = κ_e(t) b_e(t) +
    /// γ_e(t) Q_e(t−1)`; odd `e` from the right, the same with `t+1`; the pair's return `W` reads `p` where it reads `c`. The drive is charged through the
    /// circle's own leak, `κ = N₀ d/(1 + d)` with `N₀ = NEAR − 1` ([`carry_coupling`], [`CARRY_GROUP_FOUNDING`]), so `|γ| + κ/N₀ = 1`. The gate is a turn and a
    /// friction charted apart ([`carry_gate`]): `γ = γ̂(q)/(1 + d)`, `γ̂(q) = ((4 − q²) + 4iq)/(4 + q²)` the Cayley step of `iq/2` on one circle
    /// (`carryTurn_eq_cayley`: it keeps the circle, so a site's turn does no work), and `d = d₀ 2^ℓ` the friction on the leak's log chart
    /// ([`carry_friction`], `leak`), `d₀ = 1/(NEAR − 2)` ([`CARRY_LEAK_FOUNDING`]), a pure dissipation's implicit step (monotone, never past a sign
    /// change), with `q = Q r̂ + q_b` and `ℓ = L r̂ + ℓ_b` read from the site's own pair chart ([`Loci::carry`]). So `|γ|² = 1/(1 + d)² < 1` at
    /// every site (`carryGate_leak_normSq_lt_one`: the move is strictly passive by its form, and a circle's quality is finite). Founded
    /// ([`Constitution::with_carry`]) a circle is a turn with the near field's friction: `q`'s rows drawn, `q_b = 0`, `L = 0` and `ℓ_b = 0`, so `d = d₀ =
    /// 1/4` at every site (`leak_zero`) and `|γ| = 4/5`, a group of `N = (1 + d)/d = NEAR − 1 = 5` places (atlas `contact.carried-product-group-size`).
    ///
    /// Why (the follow-up record §8.5 and §9 item 4): the built gate `g/√(1 + |g|²)` founded at `g = 0` was total friction, so every letter past the
    /// first waited behind gates deposition had to open first, and a letter `d` back entered as `|γ|^(2(d−1))`; it tied the gate's modulus to its
    /// phase through a fixed `1`, an unlocated friction. Founded as a turn, a letter `d` back enters at modulus one and its pull is first order at every
    /// distance, and deposition locates the turn's phase and the leak. Why founded with friction (theory, November 11 19:56, G83 scored, G85): a
    /// contact has finite width; founded at `d = 0` a circle's group `N = (1 + d)/d` is unbounded and its scan sums `b` over its whole region (2,000
    /// to 3,000 sites a section), so `Q`, `p = a Q` and the circle's covector grew with the region's length, and the first carry lap (tc1) was refused
    /// at its sixth section with a sum past its 128-bit carrier. The width the field already declares for a tick is the near field's, a place's
    /// state moving at most `NEAR − 1` places a tick; a circle hears one side, so its group is founded at `N = NEAR − 1`. Why the log chart (theory,
    /// November 12, G96 scored): the leak was first charted linearly, `d = max(0, h)` with its right derivative at `0`, and at eight times the base
    /// rate that chart became a switch: of tp4's reads 0.685 stood at `h ≥ 1` (a friction of one or more, forgotten within a place) and 0.104 below
    /// zero, where the friction was off and the read had no covector, so nothing at the site could pull it back (a store with no loss, atlas
    /// `store.finite-quality`); those reads stood at known letters and mostly alone (a mean run of 1.43 sites), and the line's next lap (tp5) was
    /// refused at its section 1,501 of 1,535 with a sum past its carrier. On the log chart a step of `ℓ` moves the friction by a ratio and never
    /// past zero; its covector `δℓ = ln 2 · d · δd` stands at every read (`leak_hasDerivAt`), and the gate's covector per unit `δγ`,
    /// `ln 2 · d/(1 + d)²`, is at most `ln 2/4` (`leak_sensitivity_le`); the friction keeps at least one grain, so a circle holds at most `2^16 + 1`
    /// places. Why the drive is charged through the leak (theory, November 12, G97 scored, G98): G97 read the bursts as the carried charge's (all six
    /// burst sections stood among the 18 of 1,501 with the largest charge, and the host refused section 1,501 in the return at a head's lock covector,
    /// a contact's covector past its return's carrier). In the sum form `Q = b + γ Qm` a circle held `(1 + d)/d` places' drive, which the log chart
    /// lets reach `2^16 + 1` places, longer than any region (at most the reach), and its covector `δγ = conj(Qm) u` grew as the group behind the site
    /// times the group ahead. Charged through the resistor it leaks by (atlas `store.finite-quality`: a store is shaken through the coupling by which
    /// it leaks), the move is the implicit step of a dissipation relaxing the turned charge toward `N₀ b`, so the charge is a turned mean of `N₀ b`
    /// and stays within `N₀ max |b|` at every friction (`charge_le`); `Q`, `p = a Q`, `δa`, `δb` and `δℓ` then stand at a plain contact's scale,
    /// and `δq` and `δd` grow only with the group ahead. At the founding `κ = 1` (`coupling_leak_zero`), so a grown state reads every face of its
    /// source bit for bit. A field with carry circles keeps every room whole ([`Declaration::room_window`]). The circles are the last contacts, grown with
    /// `W`'s columns at zero ([`Constitution::with_carry`]), so a trained field continues bit for bit. `C` is even (a carry circle's side is its contact's
    /// parity, so as many scan from each side) and at most `f/2`; `C = 0` is the `hnn-field-v14` line exactly, and `C > 0` writes `hnn-field-v14e`
    /// with `C` its thirteenth word (the log chart and the coupling, together from the head's first state). The retired carries are refused, their
    /// states receipts only: `hnn-field-v14k` (founded at zero friction) and `hnn-field-v14t` (the leak's linear chart, its drive summed).
    pub carry: usize,
    /// [definition; theory, November 12 (the triad record,
    /// `2026-11-12_THE_LAW_ACROSS_A_PLACE_IS_HELD_BY_A_PUMPED_CONTACT_A_TRIAD_IS_A_CHARACTER_OF_A_LAW_OF_COMPOSITION_AND_ITS_THREE_LEGS_EXCHANGE_EQUAL_QUANTA`,
    /// §3 and §4)] **The triads**: `J` complex triads, each the plain pair contact with one operand more, the word of two contacts through a place.
    /// At a site `t` with both strand mates in the region, triad `k` reads `α = A r̂ + α_b`, `β = B r̂ + β_b` and `γ = G r̂ + γ_b` from the site's pair
    /// chart ([`Loci::triad`]) and forms `p_k(t) = α_k(t) β_k(t − 1)` and `c^T_k(t) = p_k(t) γ_k(t + 1)`, each released at the face's grain as
    /// the plain contact's product is ([`triad_products`]); `c^T = 0` at the region's two ends; the return `W_T` ([`Loci::w_triad`]) joins
    /// the pair's `W` in one sum released once ([`affine_joint`]). One object read three ways (§3): a word of two contacts through the place (its
    /// phase the sum of its three legs'), the mates' contact pumped by the place's own read (the parametron's reading: the mates' relative phase is
    /// even under the half-turn and enters only through the pump), and the junction's three beside its pairs. Why (§1 to §3): nothing else in the
    /// field reads a place with both of its strand mates in one product (the carry's terms of three sites lie on one side of the place), and an
    /// abelian law of composition across a place, `x = L + R`, is held by characters, each a complex triad, where every pair term reads nothing of
    /// it. The triads are grown onto a field as its last families, the charts drawn and `W_T` and the biases at zero ([`Constitution::with_triads`]), so
    /// every face is kept bit for bit. A triad reads its two strand mates, one place on each side a tick, as far as the plain pair contact reads,
    /// so it keeps a cut room wherever the plain contacts keep it ([`Declaration::room_window`]). `J = 0` writes `hnn-field-v14` or
    /// `hnn-field-v14e` exactly as before and every path is the one before it; `J > 0` writes `hnn-field-v14f`, the thirteen words of `v14e` with
    /// `C` written even where it is zero, then `J`.
    pub triads: usize,
    /// [definition; theory, November 13, the design record of that day §4.4a (G132, G139)] **The opening is compared**: the cavity opening of every
    /// place of a region (§4.4: the unresolved row in place of the place's own, its two neighbours' strand rows, and the moment's chart on the moment
    /// the others bring at their standing phases, the place's own term absent and its own stride bare, [`Constitution::cavity_openings`]) is read through a
    /// lift of its own onto the one tied face, `p̃_t = face(tied(R⁰ chart(x^cav_t) + b⁰))` at temperature one, and compared at the class the passage
    /// holds there at unit gain ([`Loci::opening`]). Why (§4.4a): the opening's chart holds 2.502 nats of news of its place where the class
    /// frequencies code 3.435, and the trained readout reads the same words at 8.260: what it misses is the opening's frame, so the opening takes a
    /// transport of its own, and a written place's surprise is as physical as an open one's. The block is founded at zero ([`Constitution::with_opening`])
    /// as the last families. `false` writes every head line exactly as before; `true` writes `hnn-field-v14g`, the fourteen words of `v14f` with `C`
    /// and `J` written even at zero, then `1`. The declaration carries it; no variable, flag or argument decides it.
    pub opening: bool,
    /// [definition; theory, November 13, the junction record §7 (atlas `tower.field-tick-return`, `junction.restitution-family`)] **The junction's
    /// return**: after each tick past the first, a site's state of two ticks before returns, half-turned about the tick's output and shortened by
    /// the reflection of the site's own load, `x^(k+1) = v^k + Γ^k (v^k − x^(k−1))` with `v^k` the built tick's output, `Γ = (ρ − 1)/(ρ + 1)`,
    /// `ρ = 2^ℓ` and `ℓ = L r̂(x^k) + ℓ_b` read from the site's own chart at the tick's opening ([`Loci::junction`], [`junction_gamma`]);
    /// `x^(k−1)` is the state the tick before began from. The first tick is the built one (the reflection of time about the opening,
    /// `x^(−1) := x^1`, gives `x^1 = v^0` at every `Γ`). Founded ([`Constitution::with_junction`]) at the matched load, `L = 0` and `ℓ_b = 0`, so `Γ = 0`
    /// in integers and every face is the built tick's bit for bit; the covector of `ℓ` stands there, `(ln 2/2)(1 − Γ²) ⟨λ^(k+1), v^k − x^(k−1)⟩`.
    ///
    /// Why (the junction record §6 and §7): the built tick keeps the junction's anchor (the mean its contacts meet at) and drops its return, so a
    /// tick is a move of first order, which no periodic change of the constitution can pump, and a free iteration past the trained depth relaxes
    /// as a diffusion does (G149: the ratio of successive changes climbed from 0.633 to 0.906 with no gap seen). The return gives each site a
    /// second coordinate, its rate, and `|Γ| < 1` at every finite `ℓ`, so the step is passive by its form (a store's quality stays finite, atlas
    /// `store.finite-quality`). Why founded at the matched load: G151 read the constitution's own value `Γ* = B/(1 − B)` from each site's echo on
    /// the line's third-lap mean, the median `B` 0.00068 over written rows, so the matched load is where the constitution stands on most rows and
    /// the deposit locates `ℓ` from there. `false` writes every head line exactly as before; `true` writes `hnn-field-v14j`, the fifteen words of
    /// `v14g` with the opening's word written as `0` or `1`, then `1`.
    pub junction: bool,
    /// [definition; agent-inferred, November 14, the ring record §4 and §5] **The release marked as the field's own**: the field reads a region
    /// twice. The first read is the built read; the second opens each open, silent site `s` on `E_b(∗) + release(α_b (release(Σ_c w_(s,c)
    /// E_b(c), 16) − E_b(∗)), 24)` in each encoding `b` its row enters (its own `enc`, its neighbours' `before` and `after`), `w` the shares
    /// of the face the first read gave it, the site silent otherwise; the faces are the second read's. `α_b`, one strength an encoding on the
    /// material's grain ([`Loci::mark`]), is founded at zero ([`Constitution::with_mark`]), so at the founding the second read is the first
    /// bit for bit. The return runs through the second read into every part and into `α_b`; the first read's faces are data to it.
    ///
    /// Why (the ring record §5, G169 to G176): a field that hears its own release as written text takes its own news for the passage's and
    /// runs off at any temperature it holds; a faint mark of its own first read in the opening lowers the open places' code at first order
    /// (G175: −0.046 nats a place a unit of strength, 5.9 times its floor), and along the strength with the constitution fixed it buys 0.003
    /// and turns by a quarter (G176), so the field is trained through the mark. The mark mixes the text's own rows toward the open row and
    /// keeps no rows of its own (a table of free rows indexed by a class is refused, November 12). `false` writes every head line exactly as
    /// before; `true` writes `hnn-field-v14m`, the sixteen words of `v14j` with the junction's word written as `0` or `1`, then `1`.
    pub mark: bool,
    /// [definition; Brandon, November 15 02:06Z on the loudness reading; the record of November 15 on loudness beside surprise, §4] **The face
    /// reads a site's loudness as its own sharpness**: at each open site the face is `z(a) = release(β v_a, 16) + c_a`, `v_a =
    /// release(⟨E(a), y⟩, 16)` the plain face, with `β = 2^16 + release(Σ_ℓ κ_ℓ λ_ℓ, 16) + b` on `2^(−16)`, `λ_ℓ` the logarithm on the face's
    /// grain of lane `ℓ`'s power (the scale the chart divides that lane by, [`lane_chart`]) at the stage the face reads. `κ_ℓ` and `b`
    /// ([`Loci::loud`]) are deposited material, founded at zero ([`Constitution::with_loud`]), so at the founding every face is the source's bit
    /// for bit. The return runs through `β` into `κ`, `b` and, radially, into the state's lane powers, the part the unit chart sets aside.
    ///
    /// Why (the loudness reading of lap 13, G193): no forward term read a site's power (atlas `tower.field-site-power-unread`), so a site's
    /// loudness was inertia alone and moved by tenths of an octave where its surprise moved by three nats; the pump is the inverse temperature
    /// (atlas `parametron.pump-inverse-temperature`), and a temperature is a store's state (CLAUDE.md), here the site's own power. `false`
    /// writes every head line exactly as before; `true` writes `hnn-field-v14l`, the seventeen words of `v14m` with the mark's word written
    /// as `0` or `1`, then `1`.
    pub loud: bool,
    /// [definition; theory, November 16 19:10Z (the crossing triad); agent-inferred realization] **The triads' legs stand at the site**: with
    /// `true`, triad `k` at site `t` is `p = α_k(t) β_k(t)`, `c^T = p γ_k(t)`, all three legs charts of the site's own read after the current's
    /// return, which holds every head's gathered current, so a far pair the heads gathered meets at the site in one product and the third leg
    /// reads the site itself (`u_k(L) w_k(x) v_k(R)`, atlas `code.triad-character-of-composition`). Every site has its legs, the region's ends
    /// included. With `false` the legs are the strand's, `α(t) β(t − 1) γ(t + 1)`, as before. Why at the site: on November 16 the heads
    /// addressed an answer digit's aligned operand digits (head 0 gave them seven to eight times the other operand digits' share, R2), while
    /// every answer digit coded at ln 10 under every receiver (R1, G-ar4): the gathered pair was summed, and a sum of pair terms reads nothing of
    /// `L + R` on `Z/n`; the strand's triad multiplies only the strand's neighbours. Realized as the strand triad's legs moved to the site, so the
    /// legs read the gathered currents through the return's material (`W_out`), not through a chart of their own: the theory's `α(y^h)` is
    /// `α(r̂(x + W_out y))` (`agent-inferred`). Needs triads; `false` writes every head line exactly as before; `true` writes `hnn-field-v14x`,
    /// the eighteen words of `v14l` with the loudness's word written as `0` or `1`, then `1`.
    pub crossing: bool,
    /// [definition; the lead, November 17 (the founding records); agent-inferred realization] **The closed characters**: `E` characters of a
    /// ring whose keys were located by closing a menu of the field's own rows (atlas `key.ring-closed-from-rows-menu`). Each class holds a
    /// key, `E` complex numbers on `2^(−16)` (a ring member's eigenvalue at unit modulus under each closed character; zero for a class off the
    /// ring), and each open site's face is the field's own mixed with what its heads' last-tick rows close to, at odds read from the chart
    /// the readout reads ([`crate::closed`]: the law, its reverse and why it is a mixture at the face). Founded by
    /// [`Constitution::with_closed`] from a ruler's keys and odds; `E = 0` writes every head line exactly as before, and `E > 0` writes
    /// `hnn-field-v14c`: the nineteen words of `v14x` with the crossing's word written as `0` or `1`, then `E`. An attempt: the card
    /// refuses a field with closed characters until its realization is built, and the keys take no deposit.
    pub closed: usize,
}

impl Declaration {
    /// Whether head `h` is a depth ring ([`Declaration::depth`]).
    pub fn is_depth(&self, h: usize) -> bool {
        h % self.frames + self.depth >= self.frames && self.carries_moment(h)
    }

    /// A lane's coordinates, `W = D / lanes`.
    pub fn lane_width(&self) -> usize {
        self.width / self.lanes
    }

    /// `M = H n`, the complex modes over every head.
    pub fn complex(&self) -> usize {
        self.heads * self.modes
    }

    /// `⌈log₂ reach⌉`, at least one bit.
    pub(crate) fn reach_bits(&self) -> usize {
        (usize::BITS - self.reach.saturating_sub(1).leading_zeros()).max(1) as usize
    }

    /// [definition; agent-inferred, November 1] **The contact's gain covers the falloff** (the
    /// dispersing field's §2.5 and §15.2): the head's row is scored by its modes' locks ([`lock`]),
    /// whose sum at an equal word is half the word's power, `Σ_m |ŵ_m|²/2 = n` at unit power over its
    /// `2n` reals; an equal word at the farthest reach pays `⌊log₂ reach⌋` bits of falloff and must still
    /// outweigh the rest of its support together, at most another `⌈log₂ reach⌉` bits. `β` is the
    /// largest shift, negative where it must amplify, with `2^(−β) n ≥ 2⌈log₂ reach⌉`: `−2` at reading
    /// 8's declaration (`n = 8`, reach 2,221: an equal word locks at 32 bits; the falloff at the reach is
    /// 11). What it bounds is the peak, not the gaps: near-equal words share its weight, a plural fibre
    /// the closure reads as one class. A turned head carries the lock by its skin decay, so its far
    /// counterparts are heard more faintly by design (§12).
    pub fn score_shift(&self) -> i32 {
        let (reals, need) = (self.modes as u128, 2 * self.reach_bits() as u128);
        let mut beta = 0i32;
        if reals >= need {
            while (reals >> (beta + 1)) >= need {
                beta += 1;
            }
        } else {
            while (reals << -beta) < need {
                beta -= 1;
            }
        }
        beta
    }

    /// [definition; agent-inferred, November 2] **A listener's opening temperature** (§15.10, §16.20): the
    /// largest gain `g = 2^(−β)` at which the random maximum of the lock over a listener's support stays within
    /// the falloff's own span over the support's octaves, `span = ⌊log₂ reach⌋ − 1`, from the near field's to the
    /// reach's: two unrelated words at unit power pair at a sum of `2n` products of unit variance, so the lock's
    /// spread is `σ = g √(2n)` bits and the maximum over `N` sources stands about `σ √(2 ln N)` above the mean;
    /// the gain holds `g² · 2n · 2 ln N ≤ span²` with `N` the reach, read exactly through `ln N ≤ ⌈log₂ N⌉ ln 2`
    /// and `ln 2`'s face rounded up (`(ln2_face + 1) 2^(−30)`). `β = 1` (`g = ½`) at reading 8's reach of 2,221
    /// with `n = 8`, `β = 2` at 484. Why not the spread alone (`g² 2n ≤ span²`, the criterion until November 2,
    /// `g = 2` at 2,221): its stated intent was that the random maximum of a few hundred unrelated far words
    /// not drown the near field, and the spread bounds the mean, not the maximum: at `g = 2` the founding's far
    /// mass at GSM8K's answer sites stood on 5.7 random sources of about 220 (Rényi-2 count, §16.20). Why not the
    /// class receiver's `−2`: that guarantee is for a support of class-mates, where an equal word is expected;
    /// a listener hears every definite site. The temperature is deposited from there ([`Constitution::temper`]).
    pub fn listen_shift(&self) -> i32 {
        let span = (usize::BITS - 1 - self.reach.leading_zeros()).saturating_sub(1).max(1) as u128;
        // `g² · 2n · 2 ln N` with `ln N ≤ ⌈log₂ N⌉ ln 2`, on `2^(−30)`, against `span²` on `2^(−30)`.
        let need = 4 * self.modes as u128 * self.reach_bits() as u128 * (ln2_face() as u128 + 1);
        let holds = |beta: i32| if beta >= 0 { need <= (span * span) << (LN2_FACE_BITS + 2 * beta as u32) } else { need << (2 * beta.unsigned_abs()) <= (span * span) << LN2_FACE_BITS };
        let mut beta = 0i32;
        if holds(beta) {
            while holds(beta - 1) {
                beta -= 1;
            }
        } else {
            while !holds(beta) {
                beta += 1;
            }
        }
        beta
    }

    /// [definition; agent-inferred, November 1] **The resonance classes' shells** (the dispersing
    /// field's §12): each of a head's first `b` modes is a trit of its unframed word, the sky plate
    /// (`Re > |Im|`, the in-phase part dominates: the mode locks and boosts), the ground plate
    /// (`Re < −|Im|`) or the bridge (`|Re| ≤ |Im|`, the quadrature dominates: it turns), the mode's
    /// light cone `|Re| = |Im|` (the null set of its Lorentz form `Re(w²)`) on the bridge.
    /// `b = min(n, ⌈½ log₃ reach⌉)`, the least `k` with `9^k ≥ reach`, so about `√reach` classes of
    /// about `√reach` sites each at a region of the reach (4 trits, 81 classes, at reading 8's
    /// declaration).
    pub fn class_trits(&self) -> usize {
        let mut k = 0usize;
        while 9u128.pow(k as u32) < self.reach as u128 {
            k += 1;
        }
        self.modes.min(k)
    }

    /// [agent-inferred, November 1] **The contact's return carrier**: the word's return sums, as the
    /// probe, `δs D ŵ` (`D ≤ 2^30`, `ŵ` on 32 bits) and, as the key, `δs (D ŵ_i − D² ŵ_j/2^g)`, the
    /// lock's bracket released once by the skin's bits (two terms of at most `2^61`), over a support
    /// of at most the reach, so a contact covector `|δs| < 2^(126 − 62 − ⌈log₂ reach⌉)` keeps every
    /// sum inside 128 bits; one past it is refused. A crowd's member part multiplies its bracket by the
    /// crowd's count before the division by its square, so its product is checked and refused past
    /// the carrier ([`KEY_RETURN`]), on the host and the card alike.
    pub fn contact_return_bits(&self) -> u32 {
        (126 - 2 * MOVE_BITS - 2).saturating_sub(self.reach_bits() as u32)
    }

    /// [definition; agent-inferred, November 1] **A series row's bound**, read from the declaration's
    /// own bounds (§14.11, §15.2), never chosen: a mode's lock is at most `2^(−β)·n` above zero (half a
    /// head's whole power in one mode, `|ŵ|² ≤ 2n`) and at most `2^(−β)·3n` below it (`|a||b| + |b|²/2`),
    /// and the falloff at the reach below that, so a row's whole bits spread over `2^(−β)·4n +
    /// ⌊log₂ reach⌋ + 2`; a term's face is 62 bits and its multiplier 62 (a far source's weight,
    /// [`WEIGHT_BITS`]) and `⌈log₂ reach⌉` more for a crowd's count; a row holds at most the reach and two
    /// crowds an octave, `⌈log₂⌉` of that; a value is at most a 64-bit carrier summed over the reach. A
    /// realization's carrier is as wide as the exponents a row actually holds and never past this bound;
    /// a row past it is refused. Owed to #410 with the grouped row's equality.
    pub fn row_bits(&self) -> u32 {
        let reach_bits = self.reach_bits() as u32;
        let gain = if self.score_shift() >= 0 { (4 * self.modes as u32) >> self.score_shift() } else { (4 * self.modes as u32) << -self.score_shift() };
        let spread = gain + (usize::BITS - 1 - self.reach.leading_zeros()) + 2;
        let terms = (usize::BITS - (self.reach + 2 * reach_bits as usize).leading_zeros()) as u32;
        62 + WEIGHT_BITS + reach_bits + spread + terms + 64 + reach_bits + 1
    }

    /// The classes a head reads, `3^b`.
    pub fn classes(&self) -> usize {
        3usize.pow(self.class_trits() as u32)
    }

    /// The key draws the founding reads, four bytes a draw: the encoding and the strand contacts'
    /// rows of every class (their unresolved rows open at zero), the key chart, the value chart, both
    /// pair drives, the probe chart and the moment's chart into the face at the modes that carry a moment.
    pub fn founding_draws(&self) -> usize {
        let m2 = 2 * self.complex();
        3 * self.alphabet * self.width + 3 * m2 * self.width + 2 * self.contacts * self.width + 2 * self.moment_modes() * self.width
    }

    /// The key draws a growth by `factor` reads ([`Constitution::growth_draws`]): `f − 1` parts of each chart entry and of
    /// each copied pair drive's entry.
    pub fn growth_draws(&self, factor: usize) -> usize {
        factor.saturating_sub(1) * self.width * (3 * 2 * self.complex() + 2 * self.contacts * factor)
    }

    /// [definition; agent-inferred, November 3, §16.29] The declaration grown by `factor`: the width and the merge's
    /// contacts; the heads (their modes, ring sets and clocks) and the reach are kept. Why the heads are kept: the
    /// card's time follows the contact's site pairs, which follow the heads, while the field's memory lies in its
    /// width and its merge (a trained field widened with its heads read a section in 2.4 times the time; a founded
    /// field of width 128 with four heads reads one in 0.41 s against 0.69 s at width 32).
    /// The lanes multiply with the width, so each copy of a lane is a lane of the old width and reads the old lane's chart.
    pub fn grown(&self, factor: usize) -> Result<Self> {
        let grow = |v: usize| v.checked_mul(factor).ok_or(TowerError::Refused("a grown extent outgrew its carrier"));
        Ok(Self { width: grow(self.width)?, contacts: grow(self.contacts)?, lanes: grow(self.lanes)?, ..*self })
    }

    /// [definition; agent-inferred, November 4, §16.40] The declaration with one more lane ([`Constitution::laned`]): the width
    /// grows by a lane's coordinates; the heads, contacts and reach are kept.
    pub fn laned(&self) -> Result<Self> {
        let width = self.width.checked_add(self.lane_width()).ok_or(TowerError::Refused("a laned width outgrew its carrier"))?;
        Ok(Self { width, lanes: self.lanes + 1, ..*self })
    }

    /// The key draws a lane's founding reads ([`Constitution::laned`]): the encoding's and the strand contacts' rows of every
    /// class over the lane, and the moment's chart into the lane at the modes that carry a moment.
    pub fn lane_draws(&self) -> usize {
        let w = self.lane_width();
        3 * self.alphabet * w + 2 * self.moment_modes() * w
    }

    /// [definition; theory, November 10 09:55] The declaration with `added` more pair contacts ([`Constitution::contacted`]): the
    /// merge's contact count grows and nothing else (the width, heads, modes, lanes, ticks and reach are kept). The new contacts
    /// come in complex pairs even at each strand side, as the founding's do.
    pub fn contacted(&self, added: usize) -> Result<Self> {
        if self.carry > 0 {
            return refuse("a plain growth in contacts of a field with carry circles (the carry circles stay the last contacts)");
        }
        if self.triads > 0 {
            return refuse("a plain growth in contacts of a field with triads (the triads are founded last; a growth after them is not built)");
        }
        if added == 0 || added % 4 != 0 {
            return refuse("a growth in contacts adds complex pairs, even at each strand side (a count divisible by four)");
        }
        let contacts = self.contacts.checked_add(added).ok_or(TowerError::Refused("a contact count outgrew its carrier"))?;
        let d = Self { contacts, ..*self };
        d.admit()?;
        Ok(d)
    }

    /// [definition; theory, November 12 (the record of the opening's room, §4 item 4)] The declaration with `fresh` more letters
    /// ([`Constitution::lettered`]): the alphabet grows and nothing else. No key is read.
    pub fn lettered(&self, fresh: usize) -> Result<Self> {
        let alphabet = self.alphabet.checked_add(fresh).ok_or(TowerError::Refused("an alphabet outgrew its carrier"))?;
        let d = Self { alphabet, ..*self };
        d.admit()?;
        Ok(d)
    }

    /// The key draws a growth in contacts by `added` reads ([`Constitution::contacted`]): the new contacts' rows of both pair drives
    /// over the whole width, as the founding draws them (`a` then `b`).
    pub fn contact_draws(&self, added: usize) -> usize {
        2 * added * self.width
    }

    /// The key draws a growth by `circles` carry circles reads ([`Constitution::with_carry`]): the circles' contacts (`2 circles` pair contacts, as a growth
    /// in contacts draws them), then the turn chart's rows `Q`, one row of `D` a circle.
    pub fn carry_draws(&self, circles: usize) -> usize {
        self.contact_draws(2 * circles) + circles * self.width
    }

    /// [definition; the lead, November 18, the record of the two streams §19] The declaration with `circles` more carry circles
    /// ([`Constitution::more_carry`]): the contact count grows by `2 circles` and the carry circles by `circles`, and nothing else. The new
    /// circles follow the standing ones as the last complex contacts, so every standing contact and circle keeps its complex index and its
    /// strand side. Refused for a field with no circles (its first are founded by [`Constitution::with_carry`]), for one with triads (a
    /// growth after them is not built) and for an odd count (as many scan from each side). The draws it reads are
    /// [`Declaration::carry_draws`]'s.
    pub fn more_carry(&self, circles: usize) -> Result<Self> {
        if self.carry == 0 {
            return refuse("a growth in carry circles of a field with none (its first circles are founded as a field takes them)");
        }
        if self.triads > 0 {
            return refuse("a growth in carry circles of a field with triads (the triads are founded last; a growth after them is not built)");
        }
        if circles == 0 || circles % 2 != 0 {
            return refuse("a growth in carry circles adds an even count (as many scan from each side)");
        }
        let contacts = self.contacts.checked_add(2 * circles).ok_or(TowerError::Refused("a contact count outgrew its carrier"))?;
        let d = Self { contacts, carry: self.carry + circles, ..*self };
        d.admit()?;
        Ok(d)
    }

    /// The key draws a growth by `triads` triads reads ([`Constitution::with_triads`]): the triads' charts, `6 J` rows of `D` (`A`, then `B`, then `G`),
    /// as a growth in contacts draws its drives' rows.
    pub fn triad_draws(&self, triads: usize) -> usize {
        6 * triads * self.width
    }

    /// The first complex contact that is a carry circle, `f/2 − C` ([`Declaration::carry`]).
    pub fn carry_first(&self) -> usize {
        self.contacts / 2 - self.carry
    }

    /// [definition; theory, November 11 19:56 (G83's second defect, G85)] **The cut room's admission**, one owner for the host's forward and the
    /// card's region upload: the region's windows ([`Region::window`]) where the field has no carry circle, and none (the room whole) where
    /// it has. Why: the cut reads the whole room's bits only because the near field and the strand's pair contact carry a place's state at
    /// most `NEAR − 1` places a tick; a carry circle's scan carries it the whole strand inside one tick, over every site, computed or not, so
    /// from the second tick a cut room's heard faces would read, through the circles, receivers that met no source. A triad
    /// ([`Declaration::triads`]) reads its two strand mates, one place on each side a tick, as far as the plain pair contact reads, so triads
    /// keep the cut wherever the plain contacts keep it.
    pub fn room_window(&self, region: &Region) -> Option<Vec<bool>> {
        if self.carry > 0 {
            return None;
        }
        region.window(self.ticks)
    }

    /// The turned slots: `(frames − still) · n`, slot `l · (frames − still) + (g − still)` the ring
    /// of local mode `l` in every head of turned ring set `g`.
    pub fn turned_slots(&self) -> usize {
        (self.frames - self.still) * self.modes
    }

    /// [definition; agent-inferred, November 1] **The modes that carry a moment** (§15.1): every mode of
    /// a turned ring set, `T = H (frames − still)/frames · n`, numbered by head then mode. A still mode has no
    /// skin to bound its sum.
    pub fn moment_modes(&self) -> usize {
        (0..self.heads).filter(|&h| self.carries_moment(h)).count() * self.modes
    }

    /// Whether head `h`'s modes carry a moment: a turned ring set.
    pub fn carries_moment(&self, h: usize) -> bool {
        h % self.frames >= self.still
    }

    /// The heads that read a pace (§16, Law 1): the turned ring sets, the heads that carry a moment.
    pub fn paced_heads(&self) -> usize {
        (0..self.heads).filter(|&h| self.carries_moment(h)).count()
    }

    /// The moment index of head `h`'s first mode.
    pub fn moment_index(&self, h: usize) -> usize {
        (0..h).filter(|&k| self.carries_moment(k)).count() * self.modes
    }

    pub(crate) fn admit(&self) -> Result<()> {
        // [§16.34] The contacts come in complex pairs, as many complex contacts toward each strand mate (`f/2` even), so a
        // growth's copies keep their side.
        if self.alphabet < 2 || self.width == 0 || self.heads == 0 || self.modes == 0 || self.contacts == 0 || self.contacts % 4 != 0 || self.ticks == 0 {
            return refuse("a field needs two classes, a nonempty width, heads, modes, contacts in complex pairs even at each strand side, and ticks");
        }
        if self.lanes == 0 || self.width % self.lanes != 0 {
            return refuse("a field's lanes divide its width");
        }
        if self.frames == 0 || self.heads % self.frames != 0 || self.still > self.frames || self.reach < 2 {
            return refuse("a field's ring sets divide its heads, no more of them are still than there are, and its reach spans two sites");
        }
        if self.depth > self.frames - self.still {
            return refuse("a field's depth rings are among its turned ring sets");
        }
        if self.carry % 2 != 0 || self.carry > self.contacts / 2 {
            return refuse("a field's carry circles are even in count (as many scan from each side) and among its complex contacts");
        }
        if self.crossing && self.triads == 0 {
            return refuse("a field whose triads' legs stand at the site needs triads");
        }
        // The closed characters' families, `A × 2E` keys and `heads × (D + 1)` odds, are laid within the carrier their offsets are counted in.
        if self.closed.checked_mul(2).and_then(|r| r.checked_mul(self.alphabet)).is_none() {
            return refuse("a field's closed characters past the carrier their families are laid in");
        }
        // The triads' families, `6J` rows of `D`, `6J` biases and `D × 2J`, are laid within the carrier their offsets are counted in.
        if self.triads.checked_mul(6).and_then(|r| r.checked_mul(self.width.saturating_add(1))).is_none() {
            return refuse("a field's triads past the carrier their families are laid in");
        }
        // The score is released `16 + β` bits from its products' grain, and a head's classes are
        // listed on the card in at most `2^12` buckets.
        if (FACE_BITS as i32) + self.score_shift() < 0 || self.class_trits() > MAX_CLASS_TRITS {
            return refuse("a field whose gain passes the face's grain or whose classes pass 3^7 a head");
        }
        Ok(())
    }

    pub(crate) fn to_text(self) -> String {
        // [theory, November 12, the triad record §4] With triads the head is `v14f`: `v14e`'s words with `C` written even at zero, then `J`; without
        // them the line before, exactly.
        let head = if self.closed > 0 {
            "hnn-field-v14c"
        } else if self.crossing {
            "hnn-field-v14x"
        } else if self.loud {
            "hnn-field-v14l"
        } else if self.mark {
            "hnn-field-v14m"
        } else if self.junction {
            "hnn-field-v14j"
        } else if self.opening {
            "hnn-field-v14g"
        } else if self.triads > 0 {
            "hnn-field-v14f"
        } else if self.carry > 0 {
            "hnn-field-v14e"
        } else {
            "hnn-field-v14"
        };
        let tail = if self.closed > 0 {
            format!(" {} {} {} {} {} {} {} {}", self.carry, self.triads, u8::from(self.opening), u8::from(self.junction), u8::from(self.mark), u8::from(self.loud), u8::from(self.crossing), self.closed)
        } else if self.crossing {
            format!(" {} {} {} {} {} {} 1", self.carry, self.triads, u8::from(self.opening), u8::from(self.junction), u8::from(self.mark), u8::from(self.loud))
        } else if self.loud {
            format!(" {} {} {} {} {} 1", self.carry, self.triads, u8::from(self.opening), u8::from(self.junction), u8::from(self.mark))
        } else if self.mark {
            format!(" {} {} {} {} 1", self.carry, self.triads, u8::from(self.opening), u8::from(self.junction))
        } else if self.junction {
            format!(" {} {} {} 1", self.carry, self.triads, u8::from(self.opening))
        } else if self.opening {
            format!(" {} {} 1", self.carry, self.triads)
        } else if self.triads > 0 {
            format!(" {} {}", self.carry, self.triads)
        } else if self.carry > 0 {
            format!(" {}", self.carry)
        } else {
            String::new()
        };
        format!("{head} {} {} {} {} {} {} {} {} {} {} {}{tail}", self.alphabet, self.width, self.heads, self.modes, self.still, self.contacts, self.ticks, self.frames, self.reach, self.lanes, self.depth)
    }

    pub(crate) fn from_text(line: &str) -> Result<Self> {
        let words: Vec<&str> = line.split(' ').collect();
        // A v13 head line is a field with no depth ring (the line before the depth rings, its states the line's own).
        let n = |w: &str| w.parse::<usize>().map_err(|_| TowerError::Refused("a field's declaration that is not a count"));
        // [theory, November 16 19:10Z] The crossing's word is read from `v14x` alone; every older head line is a field whose triads, if any, are the
        // strand's.
        // [the lead, November 17] The closed characters' count is read from `v14c` alone, whose crossing word is zero or one.
        let closed_line = words.first().copied() == Some("hnn-field-v14c") && words.len() == 20;
        let crossing = words.first().copied() == Some("hnn-field-v14x") || (closed_line && words[18] == "1");
        let closed = if closed_line {
            match n(words[19])? {
                0 => return refuse("an hnn-field-v14c head line with no closed characters (a field without them writes the line before it)"),
                e => e,
            }
        } else {
            0
        };
        let (depth_word, carry, triads, opening, junction, mark, loud) = match (words.first().copied(), words.len()) {
            (Some("hnn-field-v14c"), 20) => match (n(words[14])?, n(words[15])?, n(words[16])?, n(words[17])?, n(words[18])?) {
                (o @ (0 | 1), j @ (0 | 1), m @ (0 | 1), l @ (0 | 1), 0 | 1) => (Some(words[11]), n(words[12])?, n(words[13])?, o == 1, j == 1, m == 1, l == 1),
                _ => return refuse("an hnn-field-v14c head line whose opening, junction, mark, loudness or crossing word is not zero or one"),
            },
            // [theory, November 16 19:10Z] The words of `v14l` with the loudness's word zero or one, then the crossing's word, one.
            (Some("hnn-field-v14x"), 19) => match (n(words[14])?, n(words[15])?, n(words[16])?, n(words[17])?, n(words[18])?) {
                (o @ (0 | 1), j @ (0 | 1), m @ (0 | 1), l @ (0 | 1), 1) => (Some(words[11]), n(words[12])?, n(words[13])?, o == 1, j == 1, m == 1, l == 1),
                _ => return refuse("an hnn-field-v14x head line whose opening, junction, mark or loudness word is not zero or one or whose crossing word is not one"),
            },
            (Some("hnn-field-v14"), 12) => (Some(words[11]), 0, 0, false, false, false, false),
            (Some("hnn-field-v14e"), 13) => match n(words[12])? {
                0 => return refuse("an hnn-field-v14e head line with no carry circles (a field without them is hnn-field-v14)"),
                c => (Some(words[11]), c, 0, false, false, false, false),
            },
            // [theory, November 12, the triad record §4] `C` may be zero here, `J` may not, as `v14e` refuses `C = 0`.
            (Some("hnn-field-v14f"), 14) => match n(words[13])? {
                0 => return refuse("an hnn-field-v14f head line with no triads (a field without them is hnn-field-v14 or hnn-field-v14e)"),
                j => (Some(words[11]), n(words[12])?, j, false, false, false, false),
            },
            // [theory, November 13, §4.4a] The opening's word is one; a field without the comparison writes a line before `v14g`.
            (Some("hnn-field-v14g"), 15) => match n(words[14])? {
                1 => (Some(words[11]), n(words[12])?, n(words[13])?, true, false, false, false),
                _ => return refuse("an hnn-field-v14g head line whose opening word is not one (a field without the comparison writes the line before it)"),
            },
            // [theory, November 13, the junction record §7] The opening's word is zero or one here and the junction's is one; a field without the
            // return writes a line before `v14j`.
            (Some("hnn-field-v14j"), 16) => match (n(words[14])?, n(words[15])?) {
                (o @ (0 | 1), 1) => (Some(words[11]), n(words[12])?, n(words[13])?, o == 1, true, false, false),
                _ => return refuse("an hnn-field-v14j head line whose opening word is not zero or one or whose junction word is not one"),
            },
            // [agent-inferred, November 14, the ring record §4] The opening's and the junction's words are zero or one here and the mark's is one; a
            // field without the mark writes a line before `v14m`.
            (Some("hnn-field-v14m"), 17) => match (n(words[14])?, n(words[15])?, n(words[16])?) {
                (o @ (0 | 1), j @ (0 | 1), 1) => (Some(words[11]), n(words[12])?, n(words[13])?, o == 1, j == 1, true, false),
                _ => return refuse("an hnn-field-v14m head line whose opening or junction word is not zero or one or whose mark word is not one"),
            },
            // [Brandon, November 15 02:06Z] The opening's, the junction's and the mark's words are zero or one here and the loudness's is one; a
            // field whose face does not read its sites' loudness writes a line before `v14l`.
            (Some("hnn-field-v14l"), 18) => match (n(words[14])?, n(words[15])?, n(words[16])?, n(words[17])?) {
                (o @ (0 | 1), j @ (0 | 1), m @ (0 | 1), 1) => (Some(words[11]), n(words[12])?, n(words[13])?, o == 1, j == 1, m == 1, true),
                _ => return refuse("an hnn-field-v14l head line whose opening, junction or mark word is not zero or one or whose loudness word is not one"),
            },
            (Some("hnn-field-v14k"), _) => return refuse("the carry founded at zero friction is retired (hnn-field-v14k): its states are receipts only"),
            (Some("hnn-field-v14t"), _) => return refuse("the carry's leak on its linear chart is retired (hnn-field-v14t): its states are receipts only"),
            (Some("hnn-field-v13"), 11) => (None, 0, 0, false, false, false, false),
            _ => return refuse("a field's head line that is not hnn-field-v14"),
        };
        let d = Self { alphabet: n(words[1])?, width: n(words[2])?, heads: n(words[3])?, modes: n(words[4])?, still: n(words[5])?, contacts: n(words[6])?, ticks: n(words[7])?, frames: n(words[8])?, reach: n(words[9])?, lanes: n(words[10])?, depth: depth_word.map(n).transpose()?.unwrap_or(0), carry, triads, opening, junction, mark, loud, crossing, closed };
        d.admit()?;
        Ok(d)
    }
}

/// The material's families in order: each family's first entry, the material's length, and
/// each family as `(start, len, grain)`. A realization reads the material through it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Loci {
    pub enc: usize,
    pub before: usize,
    pub after: usize,
    pub q: usize,
    pub q_bias: usize,
    pub v: usize,
    pub v_bias: usize,
    pub out: usize,
    pub out_bias: usize,
    pub a: usize,
    pub a_bias: usize,
    pub b: usize,
    pub b_bias: usize,
    pub w: usize,
    pub w_bias: usize,
    /// The readout's lift `R` (`D × D`, §16.26) and the class bias `c` (`A`): a site's face reads each class through the
    /// encoding that encodes it, `z(a) = release(⟨E(a), R r̂ + b_R⟩, 16) + c_a`.
    pub read: usize,
    pub read_bias: usize,
    /// The strands' moment encodings (§15.1), `(A + 1) × 2T` each over the turned modes that carry a
    /// moment ([`Declaration::moment_modes`]), real parts then imaginary; founded at zero.
    pub moment_before: usize,
    pub moment_after: usize,
    /// The locks' temperatures (§15.10), one a head and receiver kind, `[h][kind]` (kind 0 a class
    /// receiver, 1 a listener), on the material's grain.
    pub temper: usize,
    /// The probe chart and its bias (§16.19): every receiver probes with its own probe, its sources
    /// answer with their keys (the chart `q`).
    pub probe: usize,
    pub probe_bias: usize,
    /// A turned head's pace (§16, Law 1): its clock's rate `κ_h(t) = 1 + ⟨c_h, x⁰_t⟩` reads the opening face
    /// through one row `c_h` of `D` a turned head (`[pace index][D]`, the index its moment
    /// index over the modes), on the material's grain; founded at zero, so the clock is the strand's own place.
    pub pace: usize,
    /// The moment's chart into the face and its bias (§16.22): `x⁰_t += C s_t + b`, `C` of `D × 2M` reading a site's
    /// moments `[t][2M]` (real parts then imaginary). A still mode carries no moment, so its column reads zero, its
    /// covector is zero, and it is founded at zero and stays there.
    pub moment_face: usize,
    pub moment_face_bias: usize,
    /// The lift's bias `b_R` (`D`, §16.26).
    pub lift_bias: usize,
    /// [definition; theory, November 11 17:25] **The carry circles' charts** ([`Declaration::carry`]), after every other family and present only
    /// where `C > 0` (else at the end, zero long, and in no family): `carry`, `2C` rows of `D` on the material's grain, rows `0..C` the turn chart `Q`
    /// and rows `C..2C` the leak chart `L`, row `k` (and `C + k`) carry circle `k`, complex contact `e = f/2 − C + k`; `carry_bias`, `2C` on the
    /// face's grain, `q_b` then `ℓ_b`. A site reads `q = Q r̂ + q_b` and `ℓ = L r̂ + ℓ_b` from its pair chart `r̂`, at the grains `a` and `b` read
    /// at, and its friction on the leak's log chart, `d = d₀ 2^ℓ` ([`carry_friction`]). Real charts: the turn is a phase, the friction a modulus
    /// and its chart a logarithm.
    pub carry: usize,
    pub carry_bias: usize,
    /// [definition; theory, November 12, the triad record §4] **The triads' families** ([`Declaration::triads`]), after the carry circles' and
    /// present only where `J > 0` (else each at the end, zero long, and in no family, as the circles' are; every other offset is unchanged):
    /// `triad`, `6J` rows of `D` on the material's grain, rows `0..2J` the chart `A`, `2J..4J` the chart `B` and `4J..6J` the chart `G`, within each
    /// row `k` the real part and row `J + k` the imaginary part of triad `k`; `triad_bias`, `6J` on the face's grain, in the rows' order; `w_triad`,
    /// the return `W_T`, `D` rows of `2J` columns on the material's grain, entry `(o, j)` at `w_triad + o·2J + j` as `W`'s are, column `k` reading
    /// `c^T_k`'s real part and `J + k` its imaginary part, with no bias of its own (the pair's `b_c` is the one sum's).
    pub triad: usize,
    pub triad_bias: usize,
    pub w_triad: usize,
    /// [definition; theory, November 13, §4.4a] **The opening's lift** ([`Declaration::opening`]): `R⁰`, `D` rows of `D` columns on the
    /// material's grain, entry `(o, i)` at `opening + o·D + i` as the readout's lift `read` is laid, and its bias `b⁰`, `D` on the face's grain at
    /// `opening_bias`; the last families, zero long where the opening is not compared.
    pub opening: usize,
    pub opening_bias: usize,
    /// [definition; theory, November 13, the junction record §7] **The junction's chart** ([`Declaration::junction`]): `L`, one row of `D` on
    /// the material's grain at `junction`, and `ℓ_b`, one entry on the face's grain at `junction_bias`, so `ℓ = L r̂ + ℓ_b` on `2^(−16)` as the carry's
    /// leak is read; the last families, zero long where the tick has no return.
    pub junction: usize,
    pub junction_bias: usize,
    /// [definition; agent-inferred, November 14, the ring record §4] **The mark's strengths** ([`Declaration::mark`]): `α_b`, one entry an
    /// encoding (`enc`, `before`, `after`, in that order) on the material's grain, so `α_b = 2^24` marks a site's row at its whole face; the last
    /// family, zero long where the field reads once.
    pub mark: usize,
    /// [definition; Brandon, November 15 02:06Z] **The face's loudness** ([`Declaration::loud`]): `κ_ℓ`, one entry a lane, then `b`, on the
    /// face's grain, so `β = 2^16 + release(Σ_ℓ κ_ℓ λ_ℓ, 16) + b`; the last family, zero long where the face does not read its sites' loudness.
    pub loud: usize,
    /// The closed characters' keys (`A × 2E`: a class's `E` real parts, then its `E` imaginary parts, on `2^(−16)`) and the odds each head's
    /// ring face is mixed at (`heads` rows of `D` on `2^(−24)`, then a bias a head on `2^(−16)`), zero long where the field has none
    /// ([`Declaration::closed`]).
    pub closed_key: usize,
    pub closed_odds: usize,
    pub closed_odds_bias: usize,
    pub len: usize,
    pub families: Vec<(usize, usize, u32)>,
}

/// The encodings a mark's strengths are read in, in [`Loci::mark`]'s order.
pub const MARK_BASES: usize = 3;

impl Loci {
    pub(crate) fn new(d: &Declaration) -> Self {
        let (dw, m2, f, a) = (d.width, 2 * d.complex(), d.contacts, d.alphabet);
        let mut families = Vec::new();
        let mut at = 0usize;
        let mut push = |len: usize, grain: u32| -> usize {
            families.push((at, len, grain));
            at += len;
            at - len
        };
        let enc = push((a + 1) * dw, FACE_BITS);
        let before = push((a + 1) * dw, FACE_BITS);
        let after = push((a + 1) * dw, FACE_BITS);
        let q = push(m2 * dw, MATERIAL_BITS);
        let q_bias = push(m2, FACE_BITS);
        let v = push(m2 * dw, MATERIAL_BITS);
        let v_bias = push(m2, FACE_BITS);
        let out = push(dw * m2, MATERIAL_BITS);
        let out_bias = push(dw, FACE_BITS);
        let a_ = push(f * dw, MATERIAL_BITS);
        let a_bias = push(f, FACE_BITS);
        let b = push(f * dw, MATERIAL_BITS);
        let b_bias = push(f, FACE_BITS);
        let w = push(dw * f, MATERIAL_BITS);
        let w_bias = push(dw, FACE_BITS);
        let read = push(dw * dw, MATERIAL_BITS);
        let read_bias = push(a, FACE_BITS);
        let moment_before = push((a + 1) * 2 * d.moment_modes(), FACE_BITS);
        let moment_after = push((a + 1) * 2 * d.moment_modes(), FACE_BITS);
        let temper = push(2 * d.heads, MATERIAL_BITS);
        let probe = push(m2 * dw, MATERIAL_BITS);
        let probe_bias = push(m2, FACE_BITS);
        // The paces (§16.16): one rate a class (and the unresolved row) a paced head, on the class sheet.
        let pace = push(d.paced_heads() * (a + 1), MATERIAL_BITS);
        let moment_face = push(dw * m2, MATERIAL_BITS);
        let moment_face_bias = push(dw, FACE_BITS);
        let lift_bias = push(dw, FACE_BITS);
        // The families present only where their count is not zero (the carry circles', then the triads'): where it is zero each stands at the end,
        // zero long and in no family, so the families before it, their offsets and the family list are the line's without it.
        let mut tail = |len: usize, grain: u32| -> usize {
            if len > 0 {
                families.push((at, len, grain));
            }
            at += len;
            at - len
        };
        let (carry, carry_bias) = (tail(2 * d.carry * dw, MATERIAL_BITS), tail(2 * d.carry, FACE_BITS));
        let (triad, triad_bias, w_triad) = (tail(6 * d.triads * dw, MATERIAL_BITS), tail(6 * d.triads, FACE_BITS), tail(dw * 2 * d.triads, MATERIAL_BITS));
        let opened = usize::from(d.opening);
        let (opening, opening_bias) = (tail(opened * dw * dw, MATERIAL_BITS), tail(opened * dw, FACE_BITS));
        let joined = usize::from(d.junction);
        let (junction, junction_bias) = (tail(joined * dw, MATERIAL_BITS), tail(joined, FACE_BITS));
        let mark = tail(usize::from(d.mark) * MARK_BASES, MATERIAL_BITS);
        let loud = tail(usize::from(d.loud) * (d.lanes + 1), FACE_BITS);
        let has = usize::from(d.closed > 0);
        let closed_key = tail(a * 2 * d.closed, FACE_BITS);
        let (closed_odds, closed_odds_bias) = (tail(has * d.heads * dw, MATERIAL_BITS), tail(has * d.heads, FACE_BITS));
        Self { enc, before, after, q, q_bias, v, v_bias, out, out_bias, a: a_, a_bias, b, b_bias, w, w_bias, read, read_bias, moment_before, moment_after, temper, probe, probe_bias, pace, moment_face, moment_face_bias, lift_bias, carry, carry_bias, triad, triad_bias, w_triad, opening, opening_bias, junction, junction_bias, mark, loud, closed_key, closed_odds, closed_odds_bias, len: at, families }
    }
}
