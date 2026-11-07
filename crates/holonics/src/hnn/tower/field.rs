//! **The field: a problem is one relatively complete region, and one constitution is iterated over
//! all of its sites at once** (#404, #406; records
//! `2026-11-01_THE_PROBLEM_IS_ONE_FIELD_EVERY_SITE_READS_EVERY_OTHER_AND_THE_ANSWER_IS_REFINED_NOT_SPOKEN`
//! and `2026-11-01_THE_FIELD_DISPERSES_A_SITE_MEETS_ITS_RESONANCE_CLASS_AT_ITS_FALLOFF_AND_THE_ANSWER_LOCKS_UNDER_THE_PUMP`,
//! which replaced the contact where every site weighed every other, the surest-first release and its
//! training regions).
//!
//! [definition; agent-inferred, November 1] Why it is built. The tower hears a passage one class
//! after another through a clocked scan: a site reads the past through its modes' running state,
//! the release speaks one class a pass, and on the card each stream is one serial, latency-bound
//! scan. Read on GSM8K, an answer's digit could not reach the question's number a median 190
//! bytes back (no built level gives a fine site full reach), the founded units spelled the same
//! number differently in the question and in its calculation, and nothing refined an answer
//! before it was released. The generation law asks for a joint field that is refined and whose
//! boundary is released. This owner is that law on one problem.
//!
//! **The object.** A problem is one relatively complete region: its question's sites are resolved
//! (their classes arrived), its answer's are unresolved (a held operand, the encoding's last row).
//! Each site carries a face `x_t` on `2^(−16)` and is framed by its place. The heads come in ring
//! sets: a **still** set's modes carry `U = 1` and read a site's content wherever it stands (the
//! word), a **turned** set's mode `m` carries the ring phasor `U_(t,m) = e^(2πi (t mod n_m)/n_m)`,
//! `n_m` a closure of the solenoid's dyadic or triadic tower ([`ring_periods`]: each ring reads the
//! finer ring's residue and its whole winding, and the top rings span the region), and reads
//! content with its place (the helix). One constitution `F_Θ` is iterated `K` ticks,
//! `x^(k+1) = F_Θ(x^k)`:
//!
//! ```text
//! moment     s_t = Σ_k ζ^(k−t) D(|t−k|) E±(u_k) at a turned mode              a site carries its moment (§15.1)
//! open       x⁰_t = E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1)) + C s_t + b_s,   u = ∗ where a site is unresolved; a carried
//!            site opens on its mixture Σ_a p(a) E(a), and so for its strand rows   it opens on its moment (§16.22)
//! chart      r̂_t = x_t / ‖x_t‖_rms,   k_t = W_k r̂_t + b_k,   p_t = W_p r̂_t + b_p,   v_t = V r̂_t + b_v   a key and a probe a head
//! classes    K_h(t), P'_h(t) = Σ_l 3^l σ_l, σ_l ∈ {0, 1, 2} the shell of k_t's, p_t's mode l   first b = min(n, ⌈½ log₃ reach⌉)
//! support    S_i^h = { j keyed : 0 < |i − j| < 6 } ∪ { j far, definite : K_h(j) ∈ {P'_h(i)} ∪ P_h(i) } for a definite i, every definite j far for an open i
//! frame      k̃_t = U_t ⊙ k_t,   p̃_t = U_t ⊙ p_t,   ṽ_t = U_t ⊙ v_t              complex modes, by head
//! skin       D_m(d) = e^(−2π d/n_m) on a turned mode's ring, 1 on a still one    one e-fold a radian
//! values     v_t += s_t, p_t += s_t at a turned mode                         linear in the moment (§15.1, §16.20)
//! contact    z_ij = 2^(−β) Σ_m [D_m Re(conj(p̃_im) k̃_jm) − D_m² |k̃_jm|²/2] − ⌊log₂ |i − j|⌋   the head's lock, j ∈ S_i^h
//! weights    e_ij = 2^(z_ij), each term keeping its own exponent, zero outside S_i^h   the Gibbs face, in bits
//! current    y_i = conj(U_i) ⊙ Σ_(j∈S_i) e_ij D(|i−j|) ṽ_j / Σ_(j∈S_i) e_ij (one series, released once),   x ← x + O y + b_o
//! pair       r̂'_t = x_t / ‖x_t‖_rms,   a_t = W_a r̂'_t + b_a,   b_t = W_b r̂'_t + b_b,   x_t ← x_t + W_c (a_t · b_(s(t))) + b_c
//!            s(t) the site's strand mate, t − 1 at an even contact and t + 1 at an odd (§16.34)   complex pairs along the strand
//! face       z_t(a) = ⟨E(a), R r̂(x^K_t) + b_R⟩ + c_a,   p̂_t(a) = 2^(z_a) / Σ_b 2^(z_b)   at the unresolved sites; read through the encoding (§16.26)
//! ```
//!
//! [definition; agent-inferred, November 1] **The field disperses** (the dispersing field's record,
//! §2). Each head reads a receiver's probe against each source's key, so a key fits its lock exactly
//! where the two agree: the contact is the receiver's lock against the source as it arrives (§15.2, [`lock`]),
//! whose pairing part is the real part of a Hermitian form and whose power part keeps a louder key from
//! outscoring the equal one. A
//! head's unframed key and probe each sit in `b` shells, a trit a mode (§12: the sky plate, the ground
//! plate or the bridge between them, split by the mode's light cone), read as an address: a receiver
//! meets a source through the head only where its probe's class is the source's key's or they stand in each other's near field
//! (`0 < |i − j| < lcm(2, 3)`, the solenoid's finest joint closure, [`NEAR`]). A source `d` sites
//! away pays `⌊log₂ d⌋` bits, the octave ladder of matched frictions read in bits, the power a wave
//! spreading on the strand's ring-wound tube surface (two dimensions, amplitude `1/√d`) carries, and
//! the two-part code's cost of naming one site among the `2^⌊log₂ d⌋` at its octave: a far site is
//! met only where its resonance pays for its address. A turned mode of ring period `n` is carried
//! across `d` sites with its skin decay `e^(−2π d/n)`, one e-fold a radian of turn (the skin effect of
//! a diffusive medium), so fine place is heard only near and coarse rings and the word reach far. In one tick a site meets its near
//! field and its classes; a change anywhere else reaches it hop by hop across the ticks and the
//! release's sweeps, fainter at each hop. Why (the eighth reading and Brandon's lens, November 1):
//! every site reread beside every other in one tick, normalized over the whole region, is a global
//! pass, the transformer's pattern and not a medium; it cost the square of the region, 31.0 × 10⁹
//! pairs a lap.
//!
//! [definition; agent-inferred, November 1] **The opening carries the site's strand contacts.** A
//! site is a ring of the strand, joined to the sites before and after it by pair contacts, so its
//! opening face is its own class's row with its two neighbours' rows of the contact encodings
//! `E₋` and `E₊` (founded with the encoding since the seventh reading, below).
//! The face of a site is then its word, the address the navigator reads it by: two sites whose
//! neighbours agree share every class and meet through their charts in one tick, so a site can find,
//! anywhere in the region, the site whose word continues its own, and gather what stands there. Why (the sixth
//! reading, November 1): after thirteen laps the held answers coded within 0.01 bits a digit
//! alike beside their own question and beside another problem's, so the field read nothing of
//! the question; with only its own class at the opening, a site's word reaches its charts only
//! through a first tick's contact with its neighbours, and finding a site by its word is then a
//! composition of two learned contacts, which thirteen laps did not form.
//!
//! [definition; agent-inferred, November 3, §16.24] **An answer port is compared through its coupling.** Where a region
//! declares its port ([`Region::port`]), every site from its start is compared with the answer's cells by the coupling at
//! temperature one ([`crate::receiver::coupling::coupling_code`]): an unused place writes the void, and the covector is
//! the face less the target the coupling places there ([`port_reading`]).
//!
//! [definition; agent-inferred, November 2, §16.22] **A site opens on its moment.** The source enters as phase-carried
//! moments (the retention law), and the opening's three rows are only the moment's three nearest terms: a site
//! whose face held its own byte and its two neighbours' could be found by its key, at any head, only as that
//! trigram, so a question site could not be told by the word or the passage it stands in. Its whole moment now
//! enters its face through the chart `C` (`D × 2M`, a read of the turned modes' moments, drawn at the founding; the
//! moment encodings open at zero, so the founding's faces are as before), and every chart (key, probe and value, still
//! heads and turned alike) reads it: fine rings carry the word a site stands in, coarse rings the passage. Why (§16.21,
//! measured on §16.20's run): the far current an answer row gathered changed by a third of itself between its own
//! question and a foil, enough to move the code 0.680 bits a site were it aligned with the code's covector, and the
//! face used 0.000039 of it: a share-weighted sum of trigram faces carries which bytes the question holds, not what
//! the answer site asks for.
//!
//! [definition; agent-inferred, November 2, §16.19] **A receiver's probe meets the sources' keys, and the
//! founding makes neither the other.** A contact is between two sites, so no site meets itself (`e_ii =
//! 0`; a lone site's slip with itself is zero and carries nothing). Every head has a key chart and a probe
//! chart, founded as independent keyed draws, and every receiver probes with its own probe, a definite site
//! as an open one; a site is listed in its key's class and reads the classes of its probe. The strand
//! contacts are founded with the encoding (each row a keyed draw, so every site has a word from the
//! founding), and a site whose class has not arrived opens on nothing (the unresolved rows of `E`, `E₋`,
//! `E₊` founded at zero: it has no key to be met by, only a probe). [§16.20] So it is no source: a site that is
//! unresolved and carries no face leaves every receiver's support, its near field's included (the lock would score
//! its silent key above every real one), and every receiver's probe reads its helical moment at the turned modes,
//! so an open site asks with what its strand has brought to its place. The still and turned modes are separate
//! ring sets: a still set compares a probe and a key at any distance, a turned set compares them with
//! their place. **The contact pairs at unit power**: within its head each framed probe and key is read as a
//! ratio to its own power (the chart's law, `ratio_to_power`, over the head's `2n` reals), so the pairing
//! of a probe and a key is `2n` times their cosine, at most `2n` where they are equal, and a key fits its
//! lock exactly where the two agree. The contact's gain covers the falloff: `β` is the largest shift,
//! negative where it amplifies, with `2^(−β)·2n ≥ 2⌈log₂ reach⌉`, so in a still head a key that fits the
//! probe at the reach still outweighs the rest of its support together wherever their keys stand
//! orthogonal or opposed to it (a turned head carries it by its skin decay, fainter with distance)
//! ([`FieldDeclaration::score_shift`]; the share is the gaps', `p_* = (1 + Σ_(j≠*) 2^(−(z_* − z_j)))^(−1)`,
//! so near-equal keys share its weight). Why the unit power (measured November 1, at a GSM8K region's 450
//! sites and the seventh reading's declaration, founded on a mixed key stream): with the probe and key at
//! the chart's scale alone, a site whose whole word recurs once peaked at its counterpart in 20 of 32 rows,
//! its score 12 to 31 against the region's next 9 to 22: a probe's power varies with its word (a sum of
//! `2n` squares), so a louder key outscored the equal one.
//!
//! The pairing `Re(conj(p̃_i) k̃_j) = Re(conj(p_i) U_i^* U_j k_j)` turns mode `m` by
//! `2π (j − i)/n_m`: a turned mode reads the relative place modulo its ring, a still mode reads the
//! contents alone, at any distance its class reaches. The current is the phase-carried moment
//! `y_i = Σ_(j∈S_i) p_ij U_i^* U_j v_j`: what a site gathers carries where each source stood relative
//! to it, so place is content after the read, not only the choice of what is read. There is no clock between sites and no carry across problems:
//! the region is the whole terrain the constitution meets, so the transferred response a scan's
//! carried state would owe is absent by construction.
//!
//! **Learning.** The comparison is completion, read as the joint code: any subset of the region is unresolved, its
//! targets the classes that arrived there, and a region drawn as a state of `K` open sites among `m` codes
//! `(m/K) Σ −log₂ p̂_t(u_t)` (§16.23, [`Region::weight`]); an answer port is compared through its coupling (§16.24,
//! [`Region::port`]). The covector (`p̂ − q` weighed, or `p̂ − r` at a port) returns exactly through the `K` ticks (the
//! operands that produced each carrier, held from the forward). The deposit is the tower's: the covector's two moments,
//! the step `m/(√v + 2^(−32))` at `2^(−k)`, certified on the section's own regions (by the products of their faces where
//! every weight is one, by partition of their readings where one is not, on the codes' grain where a port is read),
//! halved until it is certified or moves nothing; then held and read on the next section's regions, which it was not fit
//! on, and halved again or refused where it codes them higher (the tower's acceptance 77, [`FieldLearner`]).
//!
//! [definition; agent-inferred, November 3, §16.27] **The writer is the training clock run backwards**
//! ([`Field::sample_realized`]): training reads a region whose open sites are a uniform state of a random reading
//! order; the writer opens every answer place beside the known question and resolves them in one keyed random order,
//! each drawn from its own face at temperature one on the read of the region as it stands, every place resolved before it
//! known. Every place is written; a place drawn as the void is the answer's boundary, and every place past it is the void
//! (§16.35: the void is the class past an answer's end, as training's states and the codec read it). Why (the field's code read end to end,
//! November 3): the release before it locked a place only where one class held a majority of its face and moved its front
//! only past locked places; text is uncertain at most places under any model, so it wrote the classes it was surest of
//! (runs of `0`, `<<`, `=`, `####`), each lock making its neighbour's lock likelier, and left the rest open.
//!
//! **Integers at declared grains.** Faces, charts, framed charts and currents on `2^(−16)`;
//! material on `2^(−24)`; frames and skins on `2^(−30)`; each row a series of its terms'
//! exponential faces on `2^(−62)` (§14.11, [`SeriesRow`]), its current released once and its shares
//! on `2^(−63)`; covectors on `2^(−24)`, the contact's on `2^(−40)`. Every product's
//! remainder below its grain is released to the nearest numerator and every sum is an integer
//! sum, so the sites, heads and regions summed in any order give the same bits: the host and any
//! partition of the card agree bit for bit.
//!
//! [definition] The computational object is the helical pair interaction: a site meets its support
//! through its framed modes' lock at its falloff, the ring
//! phasors carry the helix (a tower's residues are each finer ring's residue with its whole winding),
//! and the pair contact `a · b` (complex, so two ring faces compose by adding their phases) is the
//! bilinear contact between a site's read and its strand mate's (the merge, §16.34): the strand's own pair contact, so a
//! rule over a site's neighbours forms in the first tick and its reach grows a site a tick.
//! Of the winding guide's six general objects it touches the **helix** (the ring phasors, the
//! carry), the **pair** (site contacts as locks and the bilinear merge), **faces and placement**
//! (the shells as addresses, the Gibbs face, the release's lock) and the **tube** (the `K` ticks and
//! the release's sweeps); the **cell holonomy** (the release's circulation receipt) and the **tower
//! thread** (the octave falloff) stay attached.

use super::{affine, covector, deposit_step, div_nearest, exp_series, fewer_bits_weighed, fit32, fit64, half_turn, on_step_grain, outer_sum, ratio_adjoint, ratio_to_power, reach, refuse, release, toward, transposed, weighed_code, Result, TowerError, TowerFace, FACE_BITS, FIRST_RATE, MATERIAL_BITS, MOVE_BITS, SECOND_RATE};
use crate::hnn::keyed_modes::{ln2_face, Exponential};
use rayon::prelude::*;

/// [agent-inferred, November 1] **A term's share of its row's mass** on `2^(−63)` (§14.11): formed
/// once, by one division of the series, for the return; the declared crossing into the step,
/// whose own release is to the material's grain.
pub const SHARE_BITS: u32 = 63;
/// A key's return past its 128-bit carrier, refused on the host and the card alike.
const KEY_RETURN: &str = "a contact's key return past its 128-bit carrier";
/// The contact covector's grain, `2^(−40)` (`δz` and `δs`).
const CONTACT_BITS: u32 = 40;
/// A face carried as a site's state, each class's share on `2^(−16)` ([`shares`]); its opening
/// `Σ_a w_a E(a)` releases the shares' grain to the encoding's own.
pub const STATE_BITS: u32 = 16;
/// [definition; agent-inferred, November 1] **The near field**: sites closer than the solenoid's
/// finest joint closure, `0 < |i − j| < lcm(2, 3) = 6`, meet through every head whatever their
/// classes (the dispersing field's §2.4: over six sites the finest dyadic and triadic rings resolve
/// place without winding, and four bytes before a site code it at 1.98 bits, so a byte's own
/// spelling context lies inside it).
pub const NEAR: usize = 6;
/// The most shells a head's classes may carry (`3^7 = 2,187` classes, within the card's `2^12`
/// buckets a head and region).
pub const MAX_CLASS_TRITS: usize = 7;

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
pub struct FieldDeclaration {
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
    /// [definition; the unified-theory reading of November 6, 22:52] **The faces are one stored energy's forces**
    /// ([`energy`]): each tick descends one energy `Φ` of the region's state and letters, and a site's face is the energy's
    /// force on its letter. The value chart `V`, the current's return `O` and its bias, and the pair's return `W_c` and its
    /// bias leave (founded at zero and never read); the pair contact is read through its own contraction `c`.
    pub energy: bool,
}

impl FieldDeclaration {
    /// Whether head `h` is a depth ring ([`FieldDeclaration::depth`]).
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
    fn reach_bits(&self) -> usize {
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
    /// a listener hears every definite site. The temperature is deposited from there ([`Field::temper`]).
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

    /// The key draws a growth by `factor` reads ([`Field::growth_draws`]): `f − 1` parts of each chart entry and of
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

    /// [definition; agent-inferred, November 4, §16.40] The declaration with one more lane ([`Field::laned`]): the width
    /// grows by a lane's coordinates; the heads, contacts and reach are kept.
    pub fn laned(&self) -> Result<Self> {
        let width = self.width.checked_add(self.lane_width()).ok_or(TowerError::Refused("a laned width outgrew its carrier"))?;
        Ok(Self { width, lanes: self.lanes + 1, ..*self })
    }

    /// The key draws a lane's founding reads ([`Field::laned`]): the encoding's and the strand contacts' rows of every
    /// class over the lane, and the moment's chart into the lane at the modes that carry a moment.
    pub fn lane_draws(&self) -> usize {
        let w = self.lane_width();
        3 * self.alphabet * w + 2 * self.moment_modes() * w
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

    fn admit(&self) -> Result<()> {
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
        // [agent-inferred, November 6] The energy's first build reads no depth ring: a depth ring's rate is read from the
        // arriving classes, so its letters would enter the energy through its frames, whose force is not built.
        if self.energy && self.depth > 0 {
            return refuse("a field read as one energy's forces with depth rings (their letters' force through the frames is not built)");
        }
        // The score is released `16 + β` bits from its products' grain, and a head's classes are
        // listed on the card in at most `2^12` buckets.
        if (FACE_BITS as i32) + self.score_shift() < 0 || self.class_trits() > MAX_CLASS_TRITS {
            return refuse("a field whose gain passes the face's grain or whose classes pass 3^7 a head");
        }
        Ok(())
    }

    fn to_text(self) -> String {
        format!("hnn-field-v15 {} {} {} {} {} {} {} {} {} {} {} {}", self.alphabet, self.width, self.heads, self.modes, self.still, self.contacts, self.ticks, self.frames, self.reach, self.lanes, self.depth, u8::from(self.energy))
    }

    fn from_text(line: &str) -> Result<Self> {
        let words: Vec<&str> = line.split(' ').collect();
        // A v13 head line is a field with no depth ring (the line before the depth rings, its states the line's own), and a
        // v14 one a field whose faces are read through the readout (the line before the energy, its states the line's own).
        let (depth_word, energy_word) = match (words.first().copied(), words.len()) {
            (Some("hnn-field-v15"), 13) => (Some(words[11]), Some(words[12])),
            (Some("hnn-field-v14"), 12) => (Some(words[11]), None),
            (Some("hnn-field-v13"), 11) => (None, None),
            _ => return refuse("a field's head line that is not hnn-field-v15"),
        };
        let energy = match energy_word {
            None | Some("0") => false,
            Some("1") => true,
            Some(_) => return refuse("a field's energy word that is not 0 or 1"),
        };
        let n = |w: &str| w.parse::<usize>().map_err(|_| TowerError::Refused("a field's declaration that is not a count"));
        let d = Self { alphabet: n(words[1])?, width: n(words[2])?, heads: n(words[3])?, modes: n(words[4])?, still: n(words[5])?, contacts: n(words[6])?, ticks: n(words[7])?, frames: n(words[8])?, reach: n(words[9])?, lanes: n(words[10])?, depth: depth_word.map(n).transpose()?.unwrap_or(0), energy };
        d.admit()?;
        Ok(d)
    }
}

/// The material's families in order: each family's first entry, the material's length, and
/// each family as `(start, len, grain)`. A realization reads the material through it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldLayout {
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
    /// moment ([`FieldDeclaration::moment_modes`]), real parts then imaginary; founded at zero.
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
    /// [definition; the unified-theory reading of November 6, 22:52] The pair contact's contraction `c` (`f`, the contacts' real
    /// parts then imaginary, on the material's grain) in an energy field ([`FieldDeclaration::energy`]): the strand pair's
    /// energy is `−Re⟨c, a_t · b_(s(t))⟩`. Absent (zero long) otherwise.
    pub pair_c: usize,
    /// [definition; the unified-theory reading of November 7, 01:37] **The letters read the energy at one temperature**: an
    /// energy field's face is `z_t(a) = −(1/T) dG/de_t(a)`, one `T` for the whole field, held as `log₂ T` (one entry on the
    /// material's grain). Absent (zero long) otherwise.
    pub face_temper: usize,
    pub len: usize,
    pub families: Vec<(usize, usize, u32)>,
}

impl FieldLayout {
    fn new(d: &FieldDeclaration) -> Self {
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
        let (pair_c, face_temper) = if d.energy { (push(f, MATERIAL_BITS), push(1, MATERIAL_BITS)) } else { (at, at) };
        Self { enc, before, after, q, q_bias, v, v_bias, out, out_bias, a: a_, a_bias, b, b_bias, w, w_bias, read, read_bias, moment_before, moment_after, temper, probe, probe_bias, pace, moment_face, moment_face_bias, lift_bias, pair_c, face_temper, len: at, families }
    }
}

/// A prime's tower of closures from `p` to the first power that spans `reach` sites.
fn tower(p: usize, reach: usize) -> Vec<usize> {
    let mut out = vec![p];
    while let Some(&top) = out.last() {
        if top >= reach {
            break;
        }
        match top.checked_mul(p) {
            Some(next) => out.push(next),
            None => break,
        }
    }
    out
}

/// [definition; agent-inferred, November 1] **The turned slots' ring periods**: the solenoid's two
/// coprime towers, the dyadic `2, 4, 8, …` and the triadic `3, 9, 27, …`, each from its finest
/// closure to the first that spans the reach. A tower's ring `p^(k+1)` reads the residue of ring
/// `p^k` and its whole winding, so a tower read together is a place's residue and its windings at
/// every scale, and its top ring turns less than once across any region (a distance, not only a
/// residue). The slots take `⌈S/2⌉` rings of the dyadic tower and `⌊S/2⌋` of the triadic, each
/// spread evenly from the finest to the top (a lone slot takes the top; more slots than closures
/// cycle the tower), merged in ascending period. Slot `s` of [`FieldDeclaration::turned_slots`]
/// is turned ring set `still + s mod (frames − still)`'s local mode `s / (frames − still)`, so every
/// turned set spans fine to coarse. Two sites that agree modulo every ring are at least the top dyadic closure apart,
/// beyond the reach: no two sites of an admitted region share every frame.
///
/// (The prime powers `2, 3, 4, 5, 7, 8, …` of the first draft closed every ring within a few
/// tens of sites and aliased sites `lcm` apart, 840 for six rings: the review of November 1.)
pub fn ring_periods(slots: usize, reach: usize) -> Vec<usize> {
    let sample = |tower: &[usize], count: usize| -> Vec<usize> {
        (0..count)
            .map(|k| match count {
                1 => tower[tower.len() - 1],
                _ if count <= tower.len() => tower[k * (tower.len() - 1) / (count - 1)],
                _ => tower[k % tower.len()],
            })
            .collect()
    };
    let mut out = sample(&tower(2, reach), slots.div_ceil(2));
    out.extend(sample(&tower(3, reach), slots / 2));
    out.sort_unstable();
    out
}

/// [definition; agent-inferred, November 1] **The skin decay** `e^(−2π d/n)` on `2^(−30)` (the
/// dispersing field's §12): a diffusive medium carries spatial period `n` with one e-fold of decay a
/// radian of turn (`J ∝ e^(−(1+i)x/δ)`, the skin effect), read as `2^(−x)` with
/// `x = 2π d/(n ln 2)` bits on `2^(−16)` through the exponential's face on `2^(−62)` and released
/// to the frames' grain: `1` at `d = 0` exactly, and zero where it falls below the grain, so a fine
/// ring is heard only a few sites away.
fn skin_decay(d: usize, n: usize, pi: i128, exponential: &Exponential) -> i64 {
    skin_of((d as i128) << PACE_BITS, n, pi, exponential)
}

/// [definition; agent-inferred, November 2] **The skin across a turn's variation** `s` on `2^(−24)` (§16, Law 1):
/// `e^(−2π |s|/n)`, one e-fold a radian of turn, read as [`skin_decay`] reads a whole distance (the same bits at a
/// whole `s`), so a head whose clock is its own decays by the turn it makes between two sites, not by their bytes.
pub(crate) fn skin_of(s: i128, n: usize, pi: i128, exponential: &Exponential) -> i64 {
    let bits = div_nearest(2 * pi * s.abs(), (n as i128 * ln2_face()) << PACE_BITS);
    release(exponential.below_one(-bits) as i128, 62 - MOVE_BITS) as i64
}

/// The grain of `ln 2`'s face ([`ln2_face`]), `2^(−30)`.
const LN2_FACE_BITS: u32 = 30;

/// [§16.44] The bits a blank's return through its face is held finer than the readout's, from its lift's covector to
/// the state's (`2^16`, the face's own grain), so a small covector reaches the state rather than rounding away.
const BLANK_HELD: u32 = STATE_BITS;

/// The temperature's carrier in its chart: `⌈log₂ T⌉ ≤ 7`, the reach its additive chart held on 32 bits, and
/// `T ≥ 2^(−23)`, above the material's grain.
const TEMPER_TOP: i128 = 7;

/// [definition; agent-inferred, November 2] **A temperature is a scale, carried in the ratio law's logarithmic
/// chart** (§16.12, §15.10): the material holds `ℓ = log₂ T` on `2^(−24)`, so a step multiplies the temperature
/// (`ℓ = log R`, the ratio of two scales), and the lock's sharpness moves by octaves however far it has come. `T =
/// 2^c · 2^(ℓ − c)` with `c = ⌈ℓ⌉`, the fraction read through the exponential's navigator at `ℓ`'s own grain
/// (`fine`, whose first sixteen roots are the resident face's), released to `2^(−24)`; no partition of `ℓ` hides
/// beneath its step. Past its carrier (`c > 7` or `c < −23`)
/// a temperature is refused, never clipped. Why: in the additive chart a step moved `T` by the same amount at 1 as at
/// 100, so crib13's learned temperatures moved about ±10 % in ten laps where the copy needs them 4 to 12 times
/// higher (§16.12).
pub(crate) fn temperature_of(ell: i32, fine: &Exponential) -> Result<i128> {
    let c = temper_octave(ell)?;
    let face = fine.below_one(ell as i128 - (c << MATERIAL_BITS));
    Ok(release(face as i128, (62 - MATERIAL_BITS as i128 - c) as u32))
}

/// A temperature's ceiling octave `c = ⌈ℓ⌉` from its logarithm on `2^(−24)`, refused past the carrier.
fn temper_octave(ell: i32) -> Result<i128> {
    let c = (ell as i128 + (1i128 << MATERIAL_BITS) - 1) >> MATERIAL_BITS;
    if c > TEMPER_TOP || c < 1 - MATERIAL_BITS as i128 {
        return refuse("a temperature past its carrier (2^(−23) to 2^7)");
    }
    Ok(c)
}

/// [definition; agent-inferred, November 2] **A row's temperature covector in its own chart** (§16.12): the row's
/// `δT = Σ release(δz S, 16)` over its sources and crowds, carried into `ℓ = log₂ T` as `δℓ = δT T ln 2`, on the same
/// scale: `release(δT · release(T ln 2, 30), 24)`, one a receiver's row, so the rows' covectors sum in any order to
/// the same bits (the card's `temper_chain`).
fn temperature_chain(temper: i128, dt: i128) -> Result<i128> {
    let rate = release(temper * ln2_face(), LN2_FACE_BITS);
    Ok(release(dt.checked_mul(rate).ok_or(TowerError::Refused("a temperature's covector past its 128-bit carrier"))?, MATERIAL_BITS))
}

/// The refusal of a clock's covector past its 128-bit carrier.
const PACE_RETURN: &str = "a clock's covector past its 128-bit carrier";

/// [definition; agent-inferred, November 2] The lock's covector `δs` read as `2^40 ∂/∂D` of the code over a skin `D`
/// (§16): the probe's return reads `δs D ŵ_j / 2^(40 + 16 + g − 24)` as the covector of the word, and the base is the
/// lock released `16 + 2g + 1` bits, so `∂code/∂base = δs / 2^56` and `2^40 ∂code/∂D = δs (∂lock/∂D on 2^(−g))
/// / 2^(2·16 + 2g + 1 − 30)`: `LOCK_BACK_BITS + 2g − 30` bits with `LOCK_BACK_BITS = 2·16 + 1`.
const LOCK_BACK_BITS: u32 = 2 * FACE_BITS + 1;

/// `release(b · (a_i z_r − a_r z_i), 46)`: the turn's covector `2^24 b Re(conj(a) i z)` on `2^(−24)` of a quantity `z`
/// on `2^(−16)` with covector `a` on `2^(−24)`, turned at the rate `b` on `2^(−30)` (§16).
fn turned_back(b: i128, a: (i128, i128), z: (i128, i128)) -> Result<i128> {
    let cross = a.1.checked_mul(z.0).zip(a.0.checked_mul(z.1)).and_then(|(x, y)| x.checked_sub(y)).ok_or(TowerError::Refused(PACE_RETURN))?;
    Ok(release(b.checked_mul(cross).ok_or(TowerError::Refused(PACE_RETURN))?, MOVE_BITS + FACE_BITS))
}

/// The skin's covector on the variation: `2^24 ∂/∂σ = 2^24 (E/2^40) b D` for `E = 2^40 ∂/∂D`, `b` and `D` on
/// `2^(−30)`, each product released once in that order (§16); its sign is the caller's.
fn skin_back(b: i128, decay: i128, e: i128) -> Result<i128> {
    let at = release(e.checked_mul(decay).ok_or(TowerError::Refused(PACE_RETURN))?, MOVE_BITS);
    Ok(release(release(at.checked_mul(b).ok_or(TowerError::Refused(PACE_RETURN))?, MOVE_BITS), 16))
}

/// [definition; agent-inferred, November 2] **The pace's grain**: a clock's rate `κ`, the clock `τ` and its
/// variation `σ` are on `2^(−24)`, the material's grain, so the rate is `1` plus a material row's pairing with the
/// opening face released once.
pub const PACE_BITS: u32 = MATERIAL_BITS;

/// [definition; agent-inferred, November 2] **A turned head's own clock over a region** (§16, Law 1): for each head
/// that reads a pace ([`FieldDeclaration::paced_heads`], its index `row[h]`), the rate `κ_h(t) = 1 + ⟨c_h, x⁰_t⟩`,
/// the clock `τ_h(t) = Σ_(0<k≤t) κ_h(k)` (an integer prefix sum: `τ_h(0) = 0`, each step into a site ticked by that
/// site's face) and the turn's variation `σ_h(t) = Σ_(0<k≤t) |κ_h(k)|`, on `2^(−24)`; `plain[p]` where every rate
/// is `1` exactly (the founding), so the clock is the byte place and the field reads its resident faces.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Paces {
    row: Vec<Option<usize>>,
    kappa: Vec<Vec<i64>>,
    tau: Vec<Vec<i64>>,
    sigma: Vec<Vec<i64>>,
    plain: Vec<bool>,
}

/// `e^(2πi r/n)` on `2^(−30)`, `r` taken in `(−n/2, n/2]`, from the half turn on `2^(−46)` by the
/// exponential's series: the ring's navigator face, read once and held resident. The four quarter
/// points are the turn's own constraint identities (`1`, `i`, `−1`, `−i`) and are held exactly; only
/// the faces between them are the series' attained faces.
fn ring_phasor(r: usize, n: usize, pi: i128) -> (i64, i64) {
    turn_phasor((r as i128) << PACE_BITS, n, pi)
}

/// [definition; agent-inferred, November 2] **The turn's face at a clock** `ρ` on `2^(−24)` (§16, Law 1):
/// `e^(2πi ρ/n)`, `ρ` taken in `(−n/2, n/2]`, by [`ring_phasor`]'s series (the same bits at a whole `ρ`), the
/// four quarter points held exactly.
pub(crate) fn turn_phasor(rho: i128, n: usize, pi: i128) -> (i64, i64) {
    let one = 1i64 << MOVE_BITS;
    let period = (n as i128) << PACE_BITS;
    let r = rho.rem_euclid(period);
    let c = if 2 * r > period { r - period } else { r };
    match (c, 2 * c == period, 4 * c == period, 4 * c == -period) {
        (0, ..) => return (one, 0),
        (_, true, ..) => return (-one, 0),
        (_, _, true, _) => return (0, one),
        (_, _, _, true) => return (0, -one),
        _ => {}
    }
    let theta = div_nearest(2 * pi * c, period);
    let (re, im) = exp_series(0, release(theta, 16));
    (re as i64, im as i64)
}

/// [definition; agent-inferred, November 1] **The field**: its declaration, its material `Θ`
/// (one vector, the families of [`FieldLayout`] in order), the rings' resident faces and the
/// exponential's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Field {
    pub declaration: FieldDeclaration,
    pub theta: Vec<i32>,
    layout: FieldLayout,
    /// Each turned slot's period and its ring's phasors on `2^(−30)` (the residues a region within
    /// the reach reads).
    rings: Vec<(usize, Vec<(i64, i64)>)>,
    /// Each turned slot's skin decay `e^(−2π d/n)` on `2^(−30)` at every distance `d` within the
    /// reach ([`skin_decay`]).
    decays: Vec<Vec<i64>>,
    exponential: Exponential,
    /// The exponential's navigator at the material's grain (`2^(−24)`), the temperatures' face (§16.12): its
    /// first sixteen roots are [`Field::exponential`]'s.
    fine: Exponential,
    /// The half turn on `2^(−46)`, the turn's faces' navigator.
    pi: i128,
    /// The packets' level of a tower of scales ([`Field::scaled_up`]), none for a field on one scale.
    pub scale: Option<Box<Scale>>,
    /// [measurement; agent-inferred, November 6] Where set, every silent place runs its own per-blank rate past the last arrival
    /// too (the clock before §16.47's one-rate stretch), a declared comparison; not part of the state.
    pub per_blank_clock: bool,
    /// [definition; agent-inferred, November 6, the unified-theory reading of 10:31] Where set, **past the last arrival a silent
    /// place runs at the bare rate** (`κ = 1`, §16.28) and returns nothing: nothing arrives there, so no guessed duration
    /// drives its clock; between arrivals each blank keeps its expected duration (§16.44). Not part of the state.
    pub bare_stretch: bool,
}

/// [definition; agent-inferred, November 1] A region: each site's class, whether it is
/// unresolved (read, and compared with its class), and the sites carried as faces. A site carried as
/// a face (`faces[t]`, its classes' shares on `2^(−16)`, [`shares`]) opens on the mixture of its
/// classes' rows, `Σ_a w_a E(a)`, and so for its strand neighbours' rows (`E₋`, `E₊`), and holds no
/// class for the closure; an unresolved site carried so is read and compared there (the release's
/// sweeps and training's front regions, the dispersing field's §4, §14.3 and §14.6). An unresolved
/// site not carried opens on the encoding's last row; a resolved one on its class's. `faces` is empty
/// where no site is carried so. A carried site may be `locked` (a foil): with the known sites
/// (resolved, carrying nothing) it is definite (§14.1), and only definite sources are heard past the
/// near field. `locked` is empty where no site is locked.
#[derive(Clone, Copy, Debug)]
pub struct Region<'a> {
    pub classes: &'a [usize],
    pub unresolved: &'a [bool],
    pub faces: &'a [Option<Shares>],
    pub locked: &'a [bool],
    /// Each carried site's echo (§15.3, [`Echo`]); empty where no site carries one.
    pub echo: &'a [Option<Echo>],
    /// [definition; agent-inferred, November 2, §16.23] **The sites the open ones were drawn from**: `m` where the
    /// region's `K` unresolved sites are a state of a reading order of `m` sites, so its code is weighed `m/K`
    /// ([`Region::weight`]); `None` where the open sites are the whole of what is read (weight one).
    pub domain: Option<usize>,
    /// [definition; agent-inferred, November 3, §16.24] **The answer port**, where one is compared through its coupling:
    /// every site from `start` to the region's end is open, and their faces are compared with `target` (the answer's
    /// cells, never the void) by the coupling at temperature one ([`crate::receiver::coupling::coupling_code`]), an
    /// unused place writing `void`. `None` where every open site is compared at its own place.
    pub port: Option<Port<'a>>,
}

/// [definition; agent-inferred, November 3, §16.24] **An answer port** ([`Region::port`]): the place its open strand
/// starts, the void class an unused place writes, and the cells it is compared with; [§16.47] compared through the
/// coupling, or at its boundary (`boundary`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Port<'a> {
    pub start: usize,
    pub void: usize,
    pub target: &'a [usize],
    pub boundary: bool,
    /// [§16.47] Where its comparison stops (none: the region's end): a place from here on is read and not compared, and
    /// takes no covector (the near field's margin a writer's state keeps past its front, so the faces before it are the
    /// whole room's).
    pub stop: Option<usize>,
    /// [definition; agent-inferred, November 5, the unified-theory reading of 23:26] **Which of its places are heard** (none:
    /// every place before the stop), indexed by the region's sites: a place not heard is read and not compared, and takes no
    /// covector, as one past the stop. A writer's state compares its front octave whole and, past it, one keyed place an
    /// octave (b2's far share), the places between read on the one-rate clock and not compared.
    pub heard: Option<&'a [bool]>,
    /// [definition; agent-inferred, November 6, the unified-theory reading of 06:50, E] **The room is cut to its windows**
    /// ([`Region::window`]): where set, a receiver's row is met only at the question's sites, the silent stretch's first
    /// place and the places within `(NEAR − 1)·ticks` of a heard one; every other receiver meets no source that tick.
    pub window: bool,
    /// [definition; agent-inferred, November 6, the unified-theory reading of 11:49] **Compared on its letters off the void**: each
    /// open place of the port on its target's class within the letters, `−log₂(m_a/(T − m_∅))`, the release's own draw where the
    /// end is given (a place before the end draws from its face restricted to the letters), so the void logit takes no covector
    /// there; a resolved place carries no face and is not compared ([`letters_reading`]).
    pub letters: bool,
    /// [definition; agent-inferred, November 6, the unified-theory reading of 18:28] **A declared pull** `(a, b, w)` at the
    /// port's first place ([`pull_reading`]): the code `w (c(b) − c(a))` on its face, `c` the classes' codes and `w` on the
    /// codes' `2^(−20)` bits, and its covector `w (e_a − e_b)`; every other place of the port is not compared.
    pub pull: Option<(usize, usize, i64)>,
}

/// [definition; agent-inferred, November 3, §16.24] **A port's reading**: its coupling code on `2^(−20)` bits and each
/// place's covector `p̂_i − r_i` on the face covector's `2^(−24)` (the face's own shares less the target the coupling
/// places there), from the faces at its places (each `(masses, total)`). The host's return and the card's read the same
/// rows from the same faces.
pub fn port_reading(faces: &[(&[u128], u128)], port: &Port) -> Result<(Vec<Vec<i64>>, i64)> {
    use crate::receiver::coupling::TemperatureRefusal as Why;
    if let Some(pull) = port.pull {
        return pull_reading(faces, pull);
    }
    if port.boundary {
        return boundary_reading(faces, port);
    }
    if port.letters {
        return letters_reading(faces, port);
    }
    let read = crate::receiver::coupling::coupling_code(faces, port.void, port.target, None).map_err(|why| {
        TowerError::Refused(match why {
            Why::Short { .. } => "a port with more target cells than places",
            Why::VoidCell => "a port whose target holds the void",
            Why::Face => "a port's face that is empty or misses a class",
            Why::Released { .. } => "a port whose coupling's mass released to zero",
        })
    })?;
    let mut rows = Vec::with_capacity(faces.len());
    for ((masses, total), placed) in faces.iter().zip(&read.placed) {
        let mut row: Vec<i64> = masses.iter().map(|&m| (((m << super::COVECTOR_BITS) + total / 2) / total) as i64).collect();
        for &(c, share) in placed {
            row[c] -= share as i64;
        }
        rows.push(row);
    }
    Ok((rows, read.code))
}

/// [definition; agent-inferred, November 5, §16.47] **A port compared at its boundary**: each place is compared with
/// whether the answer has ended there, never with which letter it holds. Where the target holds a letter (a place before
/// `target.len()`) the event is a letter, coded `−log₂(1 − p̂_void)`, and its covector `p̂ − r` takes `r` as the face's
/// own letter shares renormalized off the void, `r_void = 0` and `r_a = p̂_a / (1 − p̂_void)`: the void's entry is
/// `p̂_void` and each letter's `−p̂_a p̂_void / (1 − p̂_void)`, so no letter's content is compared. Where it holds the
/// void (a place past the target), the place is compared with the void, `p̂ − e_void` and `−log₂ p̂_void`. Its minimizer
/// is the answer's length law given what the face reads, the writer's opening's own boundary (the unified-theory reading
/// of November 5, 08:09: the writer fixes its length in its first reads and never undoes a letter past the true end, so
/// the opening's void mass past the end is what a release pays in places). On the face covector's `2^(−24)` and the codes'
/// `2^(−20)` bits, read alike by the host's return and the card's. A resolved place (`(∅, 0)`, a state of the writer's
/// path) is not compared: its row is empty and it adds no code.
/// [`Port::pull`]'s reading: at the port's first place (its face `(m, T)`), the covector `w (e_a − e_b)` on the face covector's
/// `2^(−24)` and the code `w (c(b) − c(a))` released to the nearest on `2^(−20)` bits, each code `−log₂ m/T`
/// ([`super::face_code`]); `w (c(b) − c(a))` is a ratio of two classes' masses on one face, so its covector holds no
/// face's shares. Every later place's row is empty; a first place with no face is not compared.
fn pull_reading(faces: &[(&[u128], u128)], (a, b, w): (usize, usize, i64)) -> Result<(Vec<Vec<i64>>, i64)> {
    let mut rows: Vec<Vec<i64>> = vec![Vec::new(); faces.len()];
    let Some(&(masses, total)) = faces.first() else { return Ok((rows, 0)) };
    if total == 0 && masses.is_empty() {
        return Ok((rows, 0));
    }
    if a >= masses.len() || b >= masses.len() || a == b || masses[a] == 0 || masses[b] == 0 {
        return refuse("a pull between two classes the face does not both hold");
    }
    let step = w << (super::COVECTOR_BITS - 20);
    let mut row = vec![0i64; masses.len()];
    row[a] += step;
    row[b] -= step;
    rows[0] = row;
    let gap = super::face_code(masses[b], total) as i128 - super::face_code(masses[a], total) as i128;
    Ok((rows, fit64(div_nearest(w as i128 * gap, 1 << 20))?))
}

/// [`Port::letters`]'s reading: at each open place `i` (within the target) the covector `p̂_a/(1 − p̂_∅) − [a = target_i]` over the
/// letters on the face covector's `2^(−24)`, zero at the void, and the code `−log₂(m_(target_i)/(T − m_∅))` on `2^(−20)` bits; a
/// resolved place (an empty face) is not compared.
fn letters_reading(faces: &[(&[u128], u128)], port: &Port) -> Result<(Vec<Vec<i64>>, i64)> {
    let one = 1i64 << super::COVECTOR_BITS;
    let mut rows = Vec::with_capacity(faces.len());
    let mut code = 0i64;
    for (i, &(masses, total)) in faces.iter().enumerate() {
        if (total == 0 && masses.is_empty()) || i >= port.target.len() {
            rows.push(Vec::new());
            continue;
        }
        if total == 0 || port.void >= masses.len() || masses[port.void] >= total {
            return refuse("a port's face that is empty, misses a class or holds no letter");
        }
        let rest = total - masses[port.void];
        let mut row: Vec<i64> = masses.iter().map(|&m| (((m << super::COVECTOR_BITS) + rest / 2) / rest) as i64).collect();
        row[port.void] = 0;
        row[port.target[i]] -= one;
        code += crate::hnn::tower::face_code(masses[port.target[i]], rest);
        rows.push(row);
    }
    Ok((rows, code))
}

fn boundary_reading(faces: &[(&[u128], u128)], port: &Port) -> Result<(Vec<Vec<i64>>, i64)> {
    let one = 1i128 << super::COVECTOR_BITS;
    let mut rows = Vec::with_capacity(faces.len());
    let mut code = 0i64;
    for (i, &(masses, total)) in faces.iter().enumerate() {
        // A resolved place (a state of the writer's path, §16.47) carries no face and is not compared.
        if total == 0 && masses.is_empty() {
            rows.push(Vec::new());
            continue;
        }
        if total == 0 || port.void >= masses.len() {
            return refuse("a port's face that is empty or misses a class");
        }
        let mut row: Vec<i64> = masses.iter().map(|&m| (((m << super::COVECTOR_BITS) + total / 2) / total) as i64).collect();
        let void = row[port.void] as i128;
        if i < port.target.len() {
            let rest = one - void;
            for (a, slot) in row.iter_mut().enumerate() {
                if a != port.void {
                    *slot = if rest == 0 { 0 } else { fit64(-div_nearest(*slot as i128 * void, rest))? };
                }
            }
            code += crate::hnn::tower::face_code(total - masses[port.void], total);
        } else {
            row[port.void] -= one as i64;
            code += crate::hnn::tower::face_code(masses[port.void], total);
        }
        rows.push(row);
    }
    Ok((rows, code))
}

impl Region<'_> {
    /// [definition; agent-inferred, November 6, the unified-theory reading of 06:50, E] **The windows a cut room computes**
    /// ([`Port::window`]): every site before the port, the silent stretch's first place ([`Field::silent_stretch`]) and each
    /// heard open place, each with the `(NEAR − 1)·ticks` places on either side; none where the port does not cut its room.
    /// Why the same bits (the unified-theory reading of 06:50): a silent place is no one's far source, so in one tick a receiver hears
    /// past its near field only definite sources (the question, whole) and its crowds of them, and the near field and the
    /// strand's pair contact carry a place's state at most `NEAR − 1` places a tick. A heard place's face after `ticks` ticks
    /// therefore reads only its window, and a receiver outside every window reads, at worst, its window's edge, which is
    /// `(NEAR − 1)·ticks` places from it; the stretch's clock past its first place runs at that place's rate (one passage), so
    /// the clock at every far place is `τ_front + (t − front)κ` from a computed face. Backward, the covector of a heard face
    /// reaches at most `(NEAR − 1)` places a tick, so it meets no receiver outside its window, and the clock's return reaches
    /// the stretch's first place, whose window is computed. Not the same bits where blanks sit between arrivals (masks, writer
    /// states), whose clocks read each blank's own face: those regions keep their room whole.
    pub fn window(&self, ticks: usize) -> Option<Vec<bool>> {
        let port = self.port.filter(|p| p.window)?;
        let sites = self.classes.len();
        let reach = (NEAR - 1) * ticks;
        let mut out: Vec<bool> = (0..sites).map(|t| t < port.start).collect();
        let stretch = Field::silent_stretch(self);
        let centres = std::iter::once(stretch).chain((port.start..port.stop.unwrap_or(sites).min(sites)).filter(|&t| self.unresolved[t] && port.heard.is_none_or(|h| h[t])));
        for c in centres.filter(|&c| c < sites) {
            for slot in &mut out[c.saturating_sub(reach)..(c + reach + 1).min(sites)] {
                *slot = true;
            }
        }
        Some(out)
    }

    /// [definition; agent-inferred, November 2, §16.23] **A state's weight in the joint code**, `(m, K)`: of the `m`
    /// sites of its domain `K` are open, so the region's code `Σ_open −log₂ p̂` read at `m/K` is an unbiased reading of
    /// the order-averaged joint code `E_σ L_σ` when `K` is uniform on `1..m` and the open set uniform given `K` (the
    /// order-agnostic bound). `(K, K)` where no domain is declared, and `(1, 1)` with nothing open. A port's sites are
    /// compared by its coupling and are not among the `K` (§16.24).
    pub fn weight(&self) -> (u64, u64) {
        let open = self.unresolved[..self.port.map_or(self.unresolved.len(), |p| p.start)].iter().filter(|&&u| u).count() as u64;
        if open == 0 {
            return (1, 1);
        }
        (self.domain.map_or(open, |m| m as u64), open)
    }
}

/// [definition; agent-inferred, November 1] **A read leaves its own echo out** (the dispersing field's
/// §15.3): a site carried as a face is read through contacts both ways, so its face returns to it a
/// round trip later; the read it meets is its cavity field, `z ← z − B ℓ`, with `ℓ` the logits its
/// carried face was formed from and `B` its echo on `2^(−63)`, the round trip's share read on the read
/// that formed `ℓ` ([`FieldRead::echo`]). Both are data: no covector passes through them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Echo {
    pub b: u64,
    pub logits: Vec<i64>,
}

/// [definition; agent-inferred, November 1] **A read's logits and its echoes** (§15.3): each unresolved
/// site's readout logits on `2^(−16)` bits (its cavity field where it carries an [`Echo`]) and every
/// site's echo `B_i` on `2^(−63)`: the mean over the heads and the consecutive ticks of the round
/// trip `Σ_j p_ji^(t) p_ij^(t+1)`, `j` reading `i` at one tick and `i` reading `j` at the next. That is
/// the reaction term of the cavity method (TAP's Onsager term, `Σ_j J_ij J_ji` at the order where the
/// read's currents are their shares' averages, the material's gains at the founding's identity): the
/// share of a site's own signal the contacts return to it within one read.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FieldRead {
    pub logits: Vec<Option<Vec<i64>>>,
    pub echo: Vec<u64>,
}

/// A face carried as a site's state: each class with its share on `2^(−16)` ([`shares`]).
pub type Shares = Vec<(u32, u32)>;

/// [definition; agent-inferred, November 1] **A face as a state** (§21): each class's share of
/// the face, `w_a = m_a 2^16 / Σ m` to the nearest numerator on `2^(−16)` ([`STATE_BITS`]), the
/// classes whose share releases to zero left out. A site carried so opens on `Σ_a w_a E(a)`.
pub fn shares(face: &TowerFace) -> Shares {
    if face.total == 0 {
        return Vec::new();
    }
    face.masses
        .iter()
        .enumerate()
        .filter_map(|(c, &m)| {
            let w = ((m << STATE_BITS) + face.total / 2) / face.total;
            (w > 0).then_some((c as u32, w as u32))
        })
        .collect()
}

/// [§16.44] One clock's covectors in the reverse: `δτ`, `δσ` `[pace index][t]` and the moments' `[t][2M]`.
struct ClockReturn {
    gtau: Vec<Vec<i128>>,
    gsig: Vec<Vec<i128>>,
    dm: Vec<i128>,
}

impl ClockReturn {
    fn new(paced: usize, sites: usize, m2: usize) -> Self {
        Self { gtau: vec![vec![0i128; sites]; paced], gsig: vec![vec![0i128; sites]; paced], dm: vec![0i128; sites * m2] }
    }
}

/// [definition; §16.44] A tick's own clocks where they are not the pass's: the clocks with its blanks at the faces the tick
/// before gave them, the moments read on those clocks, those faces' shares, and each blank's read (the return runs
/// through it).
#[derive(Clone, Debug, Default)]
struct TickClock {
    paces: Paces,
    moment: Vec<i64>,
    blank: Vec<Option<Shares>>,
    reads: Vec<Option<BlankRead>>,
}

/// [measurement; agent-inferred, November 5, §16.47] **One read of the release** ([`Field::sample_observed`]): its index
/// (sweeps first, then the refine steps), its pass (zero for the sweeps, `p` for the `p`-th refine pass), and every
/// problem's classes, open places and faces as the read meets them (no faces at the release's end).
pub struct ReleaseRead<'a> {
    pub read: usize,
    pub pass: usize,
    pub classes: &'a [Vec<usize>],
    pub open: &'a [Vec<bool>],
    pub faces: Option<&'a [Vec<Option<TowerFace>>]>,
    /// [measurement; §16.47] The read's runs' certificate ([`Field::sample_runs`]): the entropies past each run's first place
    /// summed over the problems, read on this read's own faces, on the codes' `2^(−20)` bits (zero, one place a read), and
    /// the problems whose sum reached the run's bound (a refine run is chosen on its places' last draws, and passes the bound
    /// where a redraw moved a context).
    pub bound: i128,
    pub passed: usize,
    /// Each answer's refine passes so far, one a pass it was redrawn in ([`PassDrive`]).
    pub drives: &'a [Vec<PassDrive>],
}

/// [measurement; agent-inferred, November 6, the unified-theory reading of 21:14] **The order a refine pass walks an answer
/// in**: a fresh keyed order each pass (the release's law), place order, or reversed place order. Consistent faces walk every
/// scan to the same joint; where the faces curl, a scan's direction moves the walk's law, which a declared scan reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RefineOrder {
    Keyed,
    Place,
    Reversed,
}

/// [measurement; agent-inferred, November 6, the unified-theory reading of 17:38] **One answer's refine pass**: the places
/// it redrew, and over them on the faces they were redrawn from (the whole face, or its letters where the draw removes the
/// void's mass, [`letters_face`]; a place whose standing letter has no mass there, or whose face has no letter, is left out): the standing letters' codes `S = Σ −log₂ p(standing)` and
/// the faces' entropies `H = Σ H(face)` on `2^(−20)` bits, their varentropies `C` on `2^(−40)` bits², the places whose
/// letter changed, and `K = Σ (1 − Σ_a p(a)²)` on `2^(−20)`, the changes a walk at equilibrium keeps. The drive `D = S − H`
/// sums the face temperature covector at the standing letters, the code's derivative in the face's temperature at `τ = 1`,
/// and `C` its curvature, the Fisher term (atlas `ratio.face-temperature-covector`, Lean `HNN/FaceCovectors`:
/// `tiltedCode_deriv_one`, `tiltedCode_second_deriv`); under the faces' own conditional the drive has mean zero
/// (`surprise_mean_zero`), the plateau. Positive: the write is hotter than its faces (standing letters in their tails);
/// negative, colder; in bits, the row's nats over `ln 2`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PassDrive {
    pub redrawn: usize,
    pub standing: i128,
    pub entropy: i128,
    pub varentropy: i128,
    pub changes: usize,
    pub equilibrium: i128,
}

impl PassDrive {
    /// The drive `D = S − H`.
    pub fn drive(&self) -> i128 {
        self.standing - self.entropy
    }

    /// Whether the answer rests after this pass ([`Field::release`]): `D ≤ √C`, or `D_(p−1) − D ≤ √C` after a pass `p − 1`.
    pub fn rests(&self, before: Option<i128>) -> bool {
        let within = |d: i128| d <= 0 || d * d <= self.varentropy;
        within(self.drive()) || before.is_some_and(|b| within(b - self.drive()))
    }

    fn add(&mut self, face: &TowerFace, standing: usize) {
        let unit = 1u128 << 20;
        let square: u128 = face.masses.iter().map(|&m| ((m << 20) / face.total).pow(2)).sum::<u128>() / unit;
        self.redrawn += 1;
        self.standing += face.code(standing) as i128;
        self.entropy += entropy(face);
        self.varentropy += varentropy(face);
        self.equilibrium += unit as i128 - square as i128;
    }
}

/// [§16.44] A blank's read of its face off a state: the chart `r̂` and its scales, the lift `R r̂ + b_R`, and the face.
#[derive(Clone, Debug, Default)]
struct BlankRead {
    read: Vec<i32>,
    scale: Vec<i128>,
    lift: Vec<i64>,
    face: TowerFace,
}

/// One tick's forward temporaries over a region.
#[derive(Clone, Debug, Default)]
struct TickCell {
    /// The tick's own clocks (§16.44), `None` where they are the pass's (the first tick, or a region with no blank).
    clock: Option<Box<TickClock>>,
    read: Vec<i32>,
    scale: Vec<i128>,
    /// The unframed key word `[t][2M]`, and the unframed value and probe (the clock's covector reads them, §16).
    word: Vec<i64>,
    vword: Vec<i64>,
    probe: Vec<i64>,
    /// The framed keys and values by head: `[h][t][2n]`, the real parts then the imaginary; the
    /// key as a ratio to its own power within its head (on `2^(−16)`), its powers `[h][t]` beside it.
    q: Vec<i64>,
    v: Vec<i64>,
    qscale: Vec<i128>,
    /// Every receiver's probe, framed and at unit power by head (`[h][t][2n]`), and its powers (§16.19).
    pq: Vec<i64>,
    pscale: Vec<i128>,
    /// Each head's resonance classes and their lists ([`ClassLists`]).
    classes: Vec<ClassLists>,
    /// Each head's and receiving site's support `[h][i]`, each source with its weight and each mode's
    /// share of its row ([`Source`]).
    rows: Vec<Vec<Source>>,
    /// Each head's and receiving site's crowds `[h][i]` and each head's prefix sums of the definite
    /// words and values ([`Sums`], §14.10).
    crowds: Vec<Vec<Crowd>>,
    sums: Vec<Sums>,
    /// The current `[t][2M]`, back in each site's own frame.
    y: Vec<i64>,
    read2: Vec<i32>,
    scale2: Vec<i128>,
    a: Vec<i64>,
    b: Vec<i64>,
    c: Vec<i64>,
}

/// [definition; agent-inferred, November 1] **A head's resonance classes over a region** (the
/// dispersing field's §2.2, §6 and §12): each site's class `B_h(t) = Σ_l 3^l (s_l + 1)`, `s_l` the
/// shell trit of its unframed word's mode `l` ([`shell`]), and the lists by one stable counting sort:
/// class `c`'s members are the definite sites first (known or locked, §14.1), then the rest, each in
/// ascending place, class `c`'s definite members `members[off[2c]..off[2c + 1]]` and its others
/// `members[off[2c + 1]..off[2c + 2]]`. The card lists them alike.
///
/// [definition; agent-inferred, November 1] **Only the plates radiate far** (the dispersing field's
/// §14.1): past the near field a source is heard only where it is definite, known (the question, or the
/// truth in a training region) or locked (a foil); a soft or unreached site is heard only in its near
/// field. The support is directional: a receiver of any state reads the definite run of its class. No
/// clique can form, since unresolved and soft sources are never met far. (This replaces the build's
/// bipartite rule, under which an open answer site met the question only through the class of the
/// unresolved row or of a near-flat mixture: on GSM8K the class of the space.)
///
/// [measurement, November 1] **The address is sharp and a class member is heard whole** (§15.2's
/// memberships were built, measured and retired): a mode's membership split across its cone within a
/// band `ε` of it, as amplitudes whose squares are a partition of unity, with the far weight their
/// overlap, kept the code continuous across every seam, and its covector matched the code's difference
/// across the far support; but on the learned fixtures (one row a head) it coded the cue's successor
/// at 3.307, 2.935, 3.224 and 0.599 bits and the recall at 2.461, 1.679, 0.862 and under its bar at
/// bands `2^(−3)`, `2^(−5)`, `2^(−8)` and `2^(−12)`, where the sharp address passes both bars; and
/// §15.2's `½(1 ± λ)` everywhere would give every site a share of the all-bridge class (the bridge
/// borders both plates), so every far row would be dense. §14.2's least hold had coded the cue at 2.12
/// bits. A seam is crossed at a jump; the held step's certificate reads the code exactly, so a step
/// across one is certified or refused on what it does. (The cue and recall fixtures these reads used are
/// retired as copy-shaped acceptances, §16.19; the reads stand as history.)
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ClassLists {
    /// Each site's class as a source, read from its key word: the class whose run lists it.
    pub class: Vec<u32>,
    /// Each receiver's own probed class, read from its probe word (§16.19).
    pub probe_class: Vec<u32>,
    pub definite: Vec<bool>,
    /// Each site's key: known, or carrying a face (§16.20). A site that carries neither has no word to be met
    /// by and is no receiver's source, its near field's included.
    pub keyed: Vec<bool>,
    pub off: Vec<u32>,
    pub members: Vec<u32>,
    /// Each receiver's other probed classes (§15.2's multi-probe, [`probes`]), empty where none.
    pub probes: Vec<Vec<u32>>,
}

impl ClassLists {
    /// The lists of the classes `class` over `buckets` classes, each class's `definite` sites first.
    pub fn of(class: Vec<u32>, definite: Vec<bool>, buckets: usize) -> Self {
        let key = |t: usize| 2 * class[t] as usize + usize::from(!definite[t]);
        let mut off = vec![0u32; 2 * buckets + 1];
        for t in 0..class.len() {
            off[key(t) + 1] += 1;
        }
        for k in 0..2 * buckets {
            off[k + 1] += off[k];
        }
        let mut filled = off.clone();
        let mut members = vec![0u32; class.len()];
        for t in 0..class.len() {
            members[filled[key(t)] as usize] = t as u32;
            filled[key(t)] += 1;
        }
        let probes = vec![Vec::new(); class.len()];
        let probe_class = class.clone();
        let keyed = vec![true; class.len()];
        Self { class, probe_class, definite, keyed, off, members, probes }
    }

    /// The lists with each site's key (§16.20): the sources a near field holds.
    pub fn keyed(mut self, keyed: Vec<bool>) -> Self {
        self.keyed = keyed;
        self
    }

    /// The lists with each receiver's own probed class and its other probed classes.
    pub fn probing(mut self, probe_class: Vec<u32>, probes: Vec<Vec<u32>>) -> Self {
        self.probe_class = probe_class;
        self.probes = probes;
        self
    }

    /// [definition; agent-inferred, November 1] **Site `i`'s support** (§2.5, §14.1, §15.9, §16.20): its near
    /// field's keyed sites (`0 < |i − j| < NEAR`, nearest first, before then after) and, past it, the definite sites
    /// it hears sharply, each site once: a definite receiver the definite members of its probe's class
    /// and of the classes it probes across its seams, an open receiver (not definite) every definite site. The
    /// support is directional: only definite sources are heard far.
    pub fn support(&self, i: usize) -> impl Iterator<Item = usize> + '_ {
        let sites = self.class.len();
        let near = (1..NEAR).flat_map(move |d| [i.checked_sub(d), Some(i + d).filter(|&j| j < sites)]).flatten().filter(move |&j| self.keyed[j]);
        let open = !self.definite[i];
        let runs = std::iter::once(self.probe_class[i]).chain(self.probes.get(i).into_iter().flatten().copied()).filter(move |_| !open);
        let far = runs.flat_map(move |c| self.members[self.off[2 * c as usize] as usize..self.off[2 * c as usize + 1] as usize].iter().map(|&j| j as usize).filter(move |&j| j.abs_diff(i) >= NEAR));
        let listened = (0..sites).filter(move |&j| open && self.definite[j] && j.abs_diff(i) >= NEAR);
        near.chain(far).chain(listened)
    }

    /// Whether receiver `i` listens to every definite site (it is open, §15.9).
    pub fn listens(&self, i: usize) -> bool {
        !self.definite[i]
    }
}

/// [definition; agent-inferred, November 1] **A receiver's probes across its seams** (§15.2's
/// multi-probe): for each address mode whose word lies within the band `ε = 2^(−k)` of its light cone,
/// `|re² − im²| 2^k < re² + im²` exactly, the shell across that cone (a plate's is the bridge, the
/// bridge's the plate on its in-phase side), and the classes every combination of those crossings
/// reaches, the receiver's own excluded. Sources stay in their own class alone and enter a probed
/// run at their full score: nothing is weighted by membership, the lock decides. Why (measured
/// November 1): with the sharp address the cue fixture's held successor codes 0.177 bits, 80 % of it in
/// 5 of its 64 problems, where the successor's earlier site shared the reader's class in at most one
/// of its four head and tick rows and was heard only blurred through its octave's crowd; with the
/// probes it codes 0.022 bits, and over six further foundings 0.026 to 0.060 bits (0.021 to 0.212
/// without), every one inside the fixture's bar of 0.0625. (That fixture is retired, a far-copy recall met
/// only through the founding's equal-word concentration; under the honest founding it coded 3.312 bits at
/// 600 sections, §16.19.)
pub fn probes(modes: impl Iterator<Item = (i64, i64)>, band: u32) -> Vec<u32> {
    let mut out = vec![0u32];
    let mut own = 0u32;
    for (l, (re, im)) in modes.enumerate() {
        let place = 3u32.pow(l as u32);
        let s = shell(re, im);
        own += place * s;
        let (rr, ii) = (re as i128 * re as i128, im as i128 * im as i128);
        let near_cone = rr + ii > 0 && ((rr - ii).abs() << band) < rr + ii;
        let across = if s != 1 { 1 } else if re >= 0 { 2 } else { 0 };
        out = out.iter().flat_map(|&c| std::iter::once(c + place * s).chain(near_cone.then_some(c + place * across))).collect();
    }
    out.retain(|&c| c != own);
    out
}

/// [agent-inferred, November 1] **The probes' band** `ε = 2^(−k)`, `k = ⌈log₂ b⌉` over a head's `b`
/// address modes: at the founding's random phases a mode lies within `ε` of its cone with probability
/// `(2/π) arcsin ε ≤ ε`, so over its `b` modes a receiver expects fewer than one crossing (`b ε ≤ 1`)
/// and reads about two runs.
pub fn band_bits(trits: usize) -> u32 {
    usize::BITS - trits.max(1).saturating_sub(1).leading_zeros()
}

/// [definition; agent-inferred, November 1] **A mode's shell** (§12) as its class digit `s + 1`:
/// the sky plate `2` where `Re > |Im|`, the ground plate `0` where `Re < −|Im|`, the bridge `1` where
/// `|Re| ≤ |Im|` (its light cone on the bridge).
pub fn shell(re: i64, im: i64) -> u32 {
    let quadrature = im.unsigned_abs();
    if re > 0 && re.unsigned_abs() > quadrature {
        2
    } else if re < 0 && re.unsigned_abs() > quadrature {
        0
    } else {
        1
    }
}

/// A source's and a crowd's value multiplier, `1` on `2^(−62)`; a crowd's mass multiplier is its count.
pub const WEIGHT_BITS: u32 = 62;

/// [definition; agent-inferred, November 1] **A mode's lock against the source that arrives** (§15.2):
/// with the receiver's mode `a` and a source `b` (a crowd's summed word over its `count`) carried by the
/// skin `(D, g)`, the receiver's power less its slip against the arriving face, `(|a|² − |a − D b|²)/2 =
/// D Re(conj(a) b) − D²|b|²/2` up to the receiver's own `|a|²/2`, which every term of its row shares and
/// so leaves its shares unchanged; returned as the integer `2·count·D·Re(conj(a) b)·2^g − D²|b|²` on
/// `2^(−(2g + 32))` (over `2 count²` for a crowd). It is greatest exactly where the arriving face equals
/// the receiver's: a key fits its lock where the two words agree, mode by mode. Why not the pairing alone
/// (`D Re(conj(a) b)`, §15.2's first statement): a mode's power is not held to one, so a louder key would
/// outscore the equal one in its mode's row, the cause the head's unit power repaired (the module doc,
/// measured November 1: the equal word peaked in 20 of 32 rows), returned mode by mode. The lock is the
/// pair contact's own slip, `Q = ⟨Δ|Δ⟩` with `Δ = a − D b`; summed over a still head's modes at unit power
/// it is the head's pairing less a constant.
fn lock(a: (i128, i128), b: (i128, i128), count: i128, (decay, grain): (i128, u32)) -> Result<i128> {
    let carried = |v: Option<i128>| v.ok_or(TowerError::Refused("a lock past its 128-bit carrier"));
    let pairing = carried((a.0 * b.0).checked_add(a.1 * b.1).and_then(|p| p.checked_mul(2 * count * decay)).and_then(|p| p.checked_mul(1i128 << grain)))?;
    let power = carried((b.0 * b.0).checked_add(b.1 * b.1).and_then(|p| p.checked_mul(decay * decay)))?;
    carried(pairing.checked_sub(power))
}

/// A value carried across a pair by its skin decay `(D, grain)`: `release(D v, grain)` (a still
/// head's `(1, 0)` is the value itself).
fn decayed((decay, grain): (i128, u32), v: i64) -> i128 {
    release(decay * v as i128, grain)
}

/// [definition; agent-inferred, November 1] **A contact row as a series** (the dispersing field's
/// §14.11; one row a head, §15.2): each term `2^z · μ` (its face and whole bits from [`Field::face`], `μ`
/// its multiplier on `2^(−62)`: `2^62` in the near field, a far source's weight, a crowd's count `· 2^62`
/// in the mass with `2^62` against its value sum) keeps its own exponent; the terms are summed whole,
/// shifted from the row's least exponent, in a carrier as wide as the row's own exponents need (never
/// past [`FieldDeclaration::row_bits`]); the current `ỹ = Σ e v / Σ e` is released once, to the nearest
/// numerator on the value's grain; and each term's share of the mass is formed once on `2^(−63)`. No
/// peak is subtracted and no term is released before the current: a source outscored by any number of
/// bits still enters the sums. Integer sums, so any order gives the same bits.
pub struct SeriesRow {
    span: usize,
    terms: Vec<(i64, u128, u128, u128, Vec<i128>)>,
}

impl SeriesRow {
    pub fn new(span: usize) -> Self {
        Self { span, terms: Vec::new() }
    }

    /// A term: its score's `(a, face)`, its mass multiplier, its value multiplier and its values.
    pub fn push(&mut self, (a, face): (i64, u128), mass: u128, value_mult: u128, value: &[i128]) {
        self.terms.push((a, face, mass, value_mult, value.to_vec()));
    }

    /// The released current (each value entry `div_nearest(Σ 2^(a − a₀) face μ_v v, Σ 2^(a − a₀) face
    /// μ)`) and each term's share `div_nearest(2^(a − a₀) face μ 2^63, Σ …)`.
    pub fn release(&self) -> (Vec<i128>, Vec<u64>) {
        use num_bigint::BigInt;
        // A receiver whose support holds no keyed source (§16.20) gathers nothing.
        if self.terms.is_empty() {
            return (vec![0; self.span], Vec::new());
        }
        let a0 = self.terms.iter().map(|t| t.0).min().unwrap_or(0);
        let mass_of = |t: &(i64, u128, u128, u128, Vec<i128>)| (BigInt::from(t.1) * BigInt::from(t.2)) << ((t.0 - a0) as usize);
        let mass: BigInt = self.terms.iter().map(mass_of).sum();
        let nearest = |x: BigInt| -> BigInt {
            let half: BigInt = &mass / 2;
            let negative = x < BigInt::from(0);
            let q: BigInt = (if negative { -x } else { x } + half) / &mass;
            if negative { -q } else { q }
        };
        let current = (0..self.span)
            .map(|r| {
                let sum: BigInt = self.terms.iter().map(|t| ((BigInt::from(t.1) * BigInt::from(t.3)) << ((t.0 - a0) as usize)) * BigInt::from(t.4[r])).sum();
                i128::try_from(nearest(sum)).unwrap_or(0)
            })
            .collect();
        let shares = self.terms.iter().map(|t| u64::try_from(nearest(mass_of(t) << SHARE_BITS as usize)).unwrap_or(u64::MAX)).collect();
        (current, shares)
    }
}

/// [definition; agent-inferred, November 1] **An octave's crowd** heard by a receiver (§14.10): the
/// definite sources at places `lo..=hi` (one side, `⌊log₂ |i − j|⌋ = level`, `|i − j| ≥ NEAR`), their
/// count, the crowd's score and its share of the row on `2^(−63)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Crowd {
    pub lo: usize,
    pub hi: usize,
    pub level: u32,
    pub count: u64,
    pub z: i64,
    pub e: u64,
    /// Its lock at unit gain on `2^(−16)` (before the temperature, §15.10).
    pub s: i64,
}

/// [measurement] Rows read by where their mass lies ([`Field::row_shares`]): `[0]` the open receivers,
/// `[1]` the definite ones.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RowShares {
    pub rows: [u64; 2],
    pub far_sources: [u64; 2],
    pub near: [u128; 2],
    pub far: [u128; 2],
    pub crowd: [u128; 2],
    /// Each row's largest share summed (its peak), on `2^(−63)`.
    pub peak: [u128; 2],
}

/// [measurement; agent-inferred, November 2] **A held read's rows at the answer sites by where their mass
/// lies** ([`Field::held_rows`]), one cell a tick and head, over the unresolved sites of the regions read:
/// the rows, and the shares (on `2^(−63)`, summed) of the sources of three groups: `question`, the definite
/// sites before the region's answer start; `soft_near`, the near field's sources that are not definite
/// (unresolved or soft answer neighbours); `other`, everything else (the far definite sites, the near
/// definite sites at or past the answer start, the crowds). `question_current` is the current's part from the
/// question group, `Σ p · Σ_x |D ṽ_x|` over its sources (each source's `release(p Σ_x |D ṽ_x|, 63)`, on the
/// value's grain).
/// [measurement; agent-inferred, November 2] The question's far part (§16.19's far-contact review): `question_far`, the
/// shares of the question sources past the near field (`|i − j| ≥ NEAR`); per row its collision
/// `C = Σ release(p², 63)` over them, and where `C > 0` its effective count of far sources, the Rényi-2 count
/// `(Σ p)² / Σ p²` (a lower bound of `2^H`), on `2^(−8)`, summed in `far_effective` over the `far_rows` rows
/// counted. Region-level groups only: no source is paired with a receiver by its class.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HeldRows {
    pub rows: u64,
    pub question: u128,
    pub soft_near: u128,
    pub other: u128,
    pub question_current: i128,
    pub question_far: u128,
    pub far_effective: u128,
    pub far_rows: u64,
    /// [measurement; agent-inferred, November 3, §16.31] The shares of the near field's definite sources at or past the
    /// answer start (the answer's own resolved neighbours, `|i − j| < NEAR`), taken out of `other`.
    pub near_definite: u128,
}

/// [measurement; agent-inferred, November 5, §16.44] **A blank's clocks by tick** ([`Field::blank_clocks`]): at each tick
/// whose clocks the blanks set (`None` at a tick that reads the pass's), each paced head's rate `κ` at the site on
/// `2^(−24)` and the face the clock read there.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BlankClocks {
    pub ticks: Vec<Option<(Vec<i64>, TowerFace)>>,
}

/// [measurement; agent-inferred, November 4, §16.42] **A receiver's near field by offset** ([`Field::near_offsets`]): at
/// each tick and head (`[tick · heads + head]`), the share on `2^(−63)` of the source `d` sites before the receiver
/// (`before[d − 1]`) and `d` sites after it (`after[d − 1]`), `0 < d < NEAR`, zero where that source is not met; and the
/// receiver's readout logits on `2^(−16)` bits where it is unresolved. Two shares of one row compare as their locks do:
/// `log₂(e_ij / e_ik) = z_ij − z_ik` bits.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct NearOffsets {
    pub before: Vec<[u64; NEAR - 1]>,
    pub after: Vec<[u64; NEAR - 1]>,
    pub logits: Option<Vec<i64>>,
}

/// [measurement; agent-inferred, November 2] **A held answer row's current by where it comes from** (§16.21,
/// [`Field::row_currents`]): one row (a tick, a head and an unresolved site), its framed current's part from the
/// question past the near field (`far`, the definite sites before the answer start at `|i − j| ≥ NEAR`) and its part
/// from the near field (`near`, every source at `|i − j| < NEAR`) and from every other source (`rest`: the answer's own
/// sites past the near field and any site after the answer start), each `Σ release(p D ṽ_j, 63)` entry by entry on the
/// value's grain over the head's `2n` reals, so `far + near + rest` is the row's current; the row's largest share on `2^(−63)`; and, where read with its return,
/// the code's covector of the row's framed current `δỹ` (the reverse's, on the covector's grain). Region-level groups
/// only: no source is paired with a receiver by its class.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RowCurrent {
    pub tick: u32,
    pub head: u32,
    pub site: u32,
    pub far: Vec<i128>,
    pub near: Vec<i128>,
    pub rest: Vec<i128>,
    pub top: u64,
    pub covector: Vec<i64>,
}

/// A met source of a receiver's row: its place and its share of the row on `2^(−63)`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Source {
    pub j: u32,
    pub p: u64,
    /// Its lock at unit gain on `2^(−16)` (before the temperature, §15.10).
    pub s: i64,
}

/// The crowds' ranges of receiver `i` in a region of `sites`: each octave `level ≥ 2` with
/// `2^level < sites`, on each side, the places `|i − j| ∈ [max(2^level, NEAR), 2^(level+1) − 1]`
/// within the region, the nearer side first.
pub fn crowd_ranges(i: usize, sites: usize) -> Vec<(usize, usize, u32)> {
    let mut out = Vec::new();
    let mut level = 2u32;
    while (1usize << level) < sites {
        let (near, far) = ((1usize << level).max(NEAR), (1usize << (level + 1)) - 1);
        if i >= near {
            out.push((i.saturating_sub(far), i - near, level));
        }
        if i + near < sites {
            out.push((i + near, (i + far).min(sites - 1), level));
        }
        level += 1;
    }
    out
}

/// [definition; agent-inferred, November 1] **The definite words' and values' prefix sums** over a
/// region, one head (§14.10): `words[t]`, `values[t]` the sums of the definite sites' framed unit words
/// and framed values before place `t` (the span's entries), `counts[t]` their number, so a crowd's sums
/// are two reads.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Sums {
    pub words: Vec<i128>,
    pub values: Vec<i128>,
    pub counts: Vec<u64>,
    pub span: usize,
}

impl Sums {
    pub fn of(words: &[i64], values: &[i64], definite: &[bool], span: usize) -> Self {
        let sites = definite.len();
        let (mut w, mut v, mut c) = (vec![0i128; (sites + 1) * span], vec![0i128; (sites + 1) * span], vec![0u64; sites + 1]);
        for t in 0..sites {
            for r in 0..span {
                let on = i128::from(definite[t]);
                w[(t + 1) * span + r] = w[t * span + r] + on * words[t * span + r] as i128;
                v[(t + 1) * span + r] = v[t * span + r] + on * values[t * span + r] as i128;
            }
            c[t + 1] = c[t] + u64::from(definite[t]);
        }
        Self { words: w, values: v, counts: c, span }
    }

    fn count(&self, lo: usize, hi: usize) -> u64 {
        self.counts[hi + 1] - self.counts[lo]
    }

    fn words(&self, lo: usize, hi: usize) -> Vec<i128> {
        (0..self.span).map(|r| self.words[(hi + 1) * self.span + r] - self.words[lo * self.span + r]).collect()
    }

    fn value(&self, lo: usize, hi: usize, r: usize) -> i128 {
        self.values[(hi + 1) * self.span + r] - self.values[lo * self.span + r]
    }
}

/// A wide value carried by a skin decay `(D, grain)`: `release(D v, grain)`.
fn decayed_wide((decay, grain): (i128, u32), v: i128) -> i128 {
    release(decay * v, grain)
}

/// `⌊log₂ d⌋` for `d ≥ 1`, the falloff's octave in bits (§2.3).
pub fn octave(d: usize) -> u32 {
    usize::BITS - 1 - d.leading_zeros()
}


impl FieldPass {
    /// The clocks a tick read (§16.44): its own, or the pass's.
    fn paces_at<'a>(&'a self, cell: &'a TickCell) -> &'a Paces {
        cell.clock.as_ref().map_or(&self.paces, |c| &c.paces)
    }
}

/// A region's forward: each tick's temporaries (held when the reverse will read them), the last
/// read, and each unresolved site's face.
#[derive(Clone, Debug, Default)]
struct FieldPass {
    ticks: Vec<TickCell>,
    read: Vec<i32>,
    scale: Vec<i128>,
    /// Each unresolved site's lift `R r̂ + b_R` on `2^(−16)` (§16.26), which its face reads through the encoding.
    lift: Vec<i64>,
    faces: Vec<Option<TowerFace>>,
    /// Each unresolved site's readout logits `z_t` on `2^(−16)` bits (the face is `2^(z − peak)`).
    logits: Vec<Option<Vec<i64>>>,
    /// The site pairs the contact met, `Σ_(h, tick, i) |S_i^h|`.
    pairs: u64,
    /// Each site's echo on `2^(−63)` ([`FieldRead`]).
    echo: Vec<u64>,
    /// The turned heads' clocks over the region (§16, Law 1).
    paces: Paces,
    /// The region's moments `[t][2M]` (§15.1), which the opening reads (§16.22).
    moment: Vec<i64>,
    /// A tower's forward at its split, for the reverse.
    tower: Option<scale::ScalePass>,
}

/// The round trips `Σ_j p_ji^(t) p_ij^(t+1)` of each site over consecutive ticks' rows (`[h][i]`), each
/// product released to `2^(−63)`, added into `trips`.
fn round_trips(before: &[Vec<Source>], after: &[Vec<Source>], sites: usize, trips: &mut [u128]) {
    for (hi, row) in after.iter().enumerate() {
        let (h, i) = (hi / sites, hi % sites);
        for src in row {
            let Some(back) = before[h * sites + src.j as usize].iter().find(|b| b.j as usize == i) else { continue };
            trips[i] += (src.p as u128 * back.p as u128 + (1u128 << (SHARE_BITS - 1))) >> SHARE_BITS;
        }
    }
}

/// Each family's `max |w|`, read once a pass.
struct Reaches {
    probe: u64,
    q: u64,
    v: u64,
    out: u64,
    a: u64,
    b: u64,
    w: u64,
    read: u64,
    moment_face: u64,
}

impl Field {
    /// **The founding configuration** (agent-inferred, November 1), read from a declared exterior
    /// key stream (four bytes a key, a signed 32-bit integer read as a uniform draw on `[−1, 1)`):
    /// the encoding and both strand contacts uniform on `[−1, 1)` at every class, their unresolved
    /// rows at zero (a site whose class has not arrived carries no word); the key chart `W_k`, the
    /// value chart `V`, both pair drives `W_a, W_b` and the probe chart `W_p` uniform on `±√(3/D)`,
    /// each its own keyed draw, so each read of a unit-power face opens at unit power and a probe is
    /// founded apart from the key it meets (the module doc); the moment's chart into the face `C` uniform on `±√(3/2T)`
    /// at the turned modes (§16.22), drawn last; the current's return `O`, the contact's return `W_c`, the
    /// readout and every bias at zero, so the field opens on the flat face and each tick on the
    /// identity.
    pub fn found(declaration: FieldDeclaration, keys: &[u8]) -> Result<Self> {
        declaration.admit()?;
        let layout = FieldLayout::new(&declaration);
        let mut theta = vec![0i32; layout.len];
        let mut cursor = 0usize;
        let mut draw = || -> Result<i64> {
            let word = keys.get(cursor..cursor + 4).ok_or(TowerError::Refused("fewer key bytes than the field's founding reads"))?;
            cursor += 4;
            Ok(i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i64)
        };
        let mut uniform = |slice: &mut [i32], num: u128, den: u128, bits: u32| -> Result<()> {
            for v in slice.iter_mut() {
                let k = draw()? as i128;
                let scaled = (k * ((num << bits) / den) as i128) >> 31;
                *v = fit32(scaled, "a founded value outgrew its 32-bit carrier")?;
            }
            Ok(())
        };
        let (dw, a) = (declaration.width, declaration.alphabet);
        let m2 = 2 * declaration.complex();
        let f = declaration.contacts;
        for start in [layout.enc, layout.before, layout.after] {
            uniform(&mut theta[start..start + a * dw], 1, 1, FACE_BITS)?;
        }
        // √(3/D) as (√3·2^16)/(√D·2^16), each square root on 2^(−16).
        let (three, dd) = chart_scale(dw);
        for start in [layout.q, layout.v] {
            uniform(&mut theta[start..start + m2 * dw], three, dd, MATERIAL_BITS)?;
        }
        for start in [layout.a, layout.b] {
            uniform(&mut theta[start..start + f * dw], three, dd, MATERIAL_BITS)?;
        }
        // [agent-inferred, November 2, §16.19] Every receiver's probe is its own keyed draw, after the key's, the value's
        // and the pair drives' (so their draws stand as before). Why not the key itself (the founding until
        // November 2): a probe equal to its key meets, from the founding, the sites whose word is its own, and so
        // the crowned contact was handed to the field rather than located by it.
        uniform(&mut theta[layout.probe..layout.probe + m2 * dw], three, dd, MATERIAL_BITS)?;
        // [agent-inferred, November 2, §16.22] The moment's chart into the face is a read of the moments, drawn last (so
        // every earlier draw stands) at `±√(3/2T)` over its `2T` moment reals, so a moment at unit power opens a unit-power
        // term; a still mode's column carries no moment and opens at zero. The moment encodings open at zero, so the
        // founding's faces are as before, and the chart gives the encodings a covector from the face's first deposit.
        let tm = declaration.moment_modes();
        if tm > 0 {
            let (three_m, dd_m) = chart_scale(2 * tm);
            let n = declaration.modes;
            let carries: Vec<bool> = (0..m2).map(|k| declaration.carries_moment((k % declaration.complex()) / n)).collect();
            for o in 0..dw {
                for (k, &on) in carries.iter().enumerate() {
                    if on {
                        uniform(&mut theta[layout.moment_face + o * m2 + k..layout.moment_face + o * m2 + k + 1], three_m, dd_m, MATERIAL_BITS)?;
                    }
                }
            }
        }
        // [definition; the unified-theory reading of November 6, 22:52] In an energy field the value chart leaves: it is drawn
        // (so every later draw stands as the line's founding draws it) and set to zero, never read. The pair's contraction `c`
        // opens at zero as the pair's return did, so each pair contact opens on no energy.
        if declaration.energy {
            theta[layout.v..layout.v + m2 * dw].fill(0);
        }
        // The temperatures open at their derived gains (§15.10), `T = 2^(−β)`, held as `log₂ T = −β` (§16.12).
        for h in 0..declaration.heads {
            for (kind, beta) in [(0usize, declaration.score_shift()), (1, declaration.listen_shift())] {
                theta[layout.temper + 2 * h + kind] = fit32((-beta as i128) << MATERIAL_BITS, "a founded temperature outgrew its 32-bit carrier")?;
            }
        }
        Ok(Self::with_theta(declaration, theta))
    }

    /// A head's temperature for a receiver of `kind` (0 a class receiver, 1 a listener) on `2^(−24)`, read from
    /// its logarithm ([`temperature_of`]).
    pub fn temper(&self, h: usize, listens: bool) -> Result<i128> {
        temperature_of(self.theta[self.layout.temper + 2 * h + usize::from(listens)], &self.fine)
    }

    /// Every head's two temperatures on `2^(−24)`, `[h][kind]` flat, refused past their carrier: the reference the
    /// card's own face (`temper_of` in `field.cu`) is checked against.
    pub fn temperatures(&self) -> Result<Vec<i128>> {
        (0..2 * self.declaration.heads).map(|k| temperature_of(self.theta[self.layout.temper + k], &self.fine)).collect()
    }


    /// [definition; agent-inferred, November 2] **A row's gain bound from its temperatures' octaves** (§16.12): `4n T
    /// + 1` bits with `T ≤ 2^c`, `c` the largest `⌈log₂ T⌉` the material holds, read from `ℓ` alone (no face), so the
    /// card's launch shape needs nothing of the forward; equal to the gain itself at a whole octave (the founding's).
    pub fn row_gain(&self) -> Result<u64> {
        let mut top = i128::MIN;
        for k in 0..2 * self.declaration.heads {
            top = top.max(temper_octave(self.theta[self.layout.temper + k])?);
        }
        let reals = 4 * self.declaration.modes as u64;
        Ok(if top >= 0 { reals << top } else { reals >> -top } + 1)
    }

    /// [definition; agent-inferred, November 2] **A row's bound as the material stands** (§14.11,
    /// §15.10): [`FieldDeclaration::row_bits`] with the gain read from the largest temperature the
    /// material holds, since the temperatures are deposited.
    pub fn row_bits(&self) -> Result<u32> {
        let d = &self.declaration;
        let gain = self.row_gain()? as u32;
        let reach_bits = d.reach_bits() as u32;
        let spread = gain + (usize::BITS - 1 - d.reach.leading_zeros()) + 2;
        let terms = (usize::BITS - (d.reach + 2 * reach_bits as usize).leading_zeros()) as u32;
        Ok(62 + WEIGHT_BITS + reach_bits + spread + terms + 64 + reach_bits + 1)
    }

    fn with_theta(declaration: FieldDeclaration, theta: Vec<i32>) -> Self {
        let layout = FieldLayout::new(&declaration);
        let pi = half_turn(MOVE_BITS + 16);
        let rings: Vec<(usize, Vec<(i64, i64)>)> = ring_periods(declaration.turned_slots(), declaration.reach).into_iter().map(|n| (n, (0..n.min(declaration.reach)).map(|r| ring_phasor(r, n, pi)).collect())).collect();
        let exponential = Exponential::new(FACE_BITS);
        let decays = rings.iter().map(|&(n, _)| (0..declaration.reach).map(|d| skin_decay(d, n, pi, &exponential)).collect()).collect();
        Self { declaration, theta, layout, rings, decays, exponential, fine: Exponential::new(MATERIAL_BITS), pi, scale: None, per_blank_clock: false, bare_stretch: false }
    }

    /// Each turned slot's skin decay on `2^(−30)` at every distance within the reach (a
    /// realization's resident face).
    pub fn decays(&self) -> &[Vec<i64>] {
        &self.decays
    }

    /// [definition; agent-inferred, November 1] **The skin decay of local mode `l` of head `h` across
    /// `d` sites** (the dispersing field's §12) and the bits it is carried on: `e^(−2π d/n_m)` on
    /// `2^(−30)` in a turned head, one e-fold a radian of turn; in a still head (period infinite) the
    /// the `1` itself, carried on no bits, so a still head's sums are the bare ones (the same integers a
    /// `2^30` on `2^(−30)` would release to).
    fn decay(&self, h: usize, l: usize, d: usize) -> (i128, u32) {
        let dd = &self.declaration;
        let set = h % dd.frames;
        if set < dd.still || dd.is_depth(h) {
            return (1, 0);
        }
        (self.decays[l * (dd.frames - dd.still) + set - dd.still][d] as i128, MOVE_BITS)
    }

    /// [definition; agent-inferred, November 2] **The skin across a pair** (§16, Law 1): local mode `l` of head
    /// `h` between sites `i` and `j`, `e^(−2π |σ_h(i) − σ_h(j)|/n)` on a head that reads a pace (its byte distance's
    /// [`Field::decay`] where the pace is plain), the `1` itself on a still head.
    fn pair_decay(&self, paces: &Paces, h: usize, l: usize, i: usize, j: usize) -> (i128, u32) {
        match paces.row.get(h).copied().flatten() {
            Some(p) if !paces.plain[p] && !self.declaration.is_depth(h) => (self.skin(self.slot(h, l), paces.sigma[p][i] as i128 - paces.sigma[p][j] as i128) as i128, MOVE_BITS),
            _ => self.decay(h, l, i.abs_diff(j)),
        }
    }

    /// The skin of an octave's crowd from site `i` (§14.10, §16): its byte distance `2^ℓ`'s, or on a paced head
    /// the skin to the place `2^ℓ` away on the crowd's side (inside the region wherever the octave is).
    fn octave_decay(&self, paces: &Paces, h: usize, l: usize, i: usize, level: u32, right: bool) -> (i128, u32) {
        match paces.row.get(h).copied().flatten() {
            Some(p) if !paces.plain[p] && !self.declaration.is_depth(h) => {
                let k = if right { i + (1 << level) } else { i - (1 << level) };
                (self.skin(self.slot(h, l), paces.sigma[p][i] as i128 - paces.sigma[p][k] as i128) as i128, MOVE_BITS)
            }
            _ => self.decay(h, l, 1 << level),
        }
    }

    /// The skin of turned slot `slot` across a variation `s` on `2^(−24)`: the resident decay at a whole distance
    /// within the reach, [`skin_of`] otherwise (the same bits).
    fn skin(&self, slot: usize, s: i128) -> i64 {
        let s = s.abs();
        if s & ((1i128 << PACE_BITS) - 1) == 0 {
            if let Some(&dv) = self.decays[slot].get((s >> PACE_BITS) as usize) {
                return dv;
            }
        }
        skin_of(s, self.rings[slot].0, self.pi, &self.exponential)
    }

    /// The face of turned slot `slot` at a clock `ρ` on `2^(−24)`: the resident ring at a whole place it holds,
    /// [`turn_phasor`] otherwise (the same bits).
    fn turn(&self, slot: usize, rho: i128) -> (i64, i64) {
        let (n, ring) = &self.rings[slot];
        if rho & ((1i128 << PACE_BITS) - 1) == 0 {
            if let Some(&p) = ring.get((rho >> PACE_BITS).rem_euclid(*n as i128) as usize) {
                return p;
            }
        }
        turn_phasor(rho, *n, self.pi)
    }

    /// [definition; agent-inferred, November 2] **The turned heads' clocks over a region** ([`Paces`]), read on the
    /// class sheet (§16.16): a site's rate is its own class's, `κ = 1 + c_h[u_t]` on `2^(−24)` (one at a silent open
    /// site, §16.28; a carried face's mixture `release(Σ_a w_a c_h[a], 16)`), one rate a codec cell, a navigator's
    /// resident face beside `E(u)`, opening at `κ ≡ 1` and deposited by the covector like every other parameter
    /// (§16.19). The neighbours' rows of the opening do not enter: a copy's turn is
    /// the sum of its span's rates, and the loop law reads only the span's classes.
    fn paces(&self, region: &Region) -> Result<Paces> {
        self.paces_with(region, &[])
    }

    /// [definition; agent-inferred, November 4, §16.44] **A blank place runs at its expected duration**: the clocks
    /// ([`Field::paces`]) with each silent open site `t` that `blank` gives a face `p_t` running at
    /// `κ_h(t) = 1 + Σ_a p_t(a) c_h[a]`, the duration a written byte there would take in expectation, `release(Σ_a w_a c_h[a],
    /// 24)` as a carried face's mixture; every other site as in [`Field::paces`]. Why (the unified-theory reading of
    /// November 4, `a_blank_place_is_a_potential` §4, and §16.42): a turned head reads a source across `τ_t − τ_s = Σ_(u∈(s,t])
    /// κ_u`, and a blank at the bare rate makes a gap read `1/1.62` and `1/1.91` of its written length on the two clocks, so a
    /// restated result drawn into a blank surround lands one place off; at its expected duration the gap's clock has the
    /// expectation it will have once written, and only its spread remains. The blank carries nothing else: its rows at its
    /// own place would be a self-energy, and as a source it costs the trained field 0.87 bits a class (that reading, §5).
    fn paces_with(&self, region: &Region, blank: &[Option<Shares>]) -> Result<Paces> {
        let d = &self.declaration;
        let sites = region.classes.len();
        let width = d.alphabet + 1;
        let one = 1i128 << PACE_BITS;
        let stretch = if self.per_blank_clock { sites } else { Self::silent_stretch(region) };
        let mut out = Paces { row: vec![None; d.heads], ..Default::default() };
        for h in (0..d.heads).filter(|&h| d.carries_moment(h)) {
            let p = out.kappa.len();
            out.row[h] = Some(p);
            let base = self.layout.pace + p * width;
            let (mut kappa, mut tau, mut sigma) = (Vec::with_capacity(sites), Vec::with_capacity(sites), Vec::with_capacity(sites));
            let (mut clock, mut variation) = (0i128, 0i128);
            for t in 0..sites {
                // [§16.47] Past the last arrival every silent place runs at the first one's rate (one passage); under
                // `bare_stretch` at its own place, which reads no face there, so at the bare rate.
                let at = if t > stretch && !self.bare_stretch { stretch } else { t };
                // [the unified-theory reading of November 6, 05:45] A depth ring takes no blank face: a silent site runs at
                // rate zero every tick (true to what arrived; an expected increment `ζ^E[r]` would read a blank at full
                // coherence and turn a closer's frame by its own guess).
                let rate = match blank.get(at).and_then(Option::as_ref).filter(|_| Self::silent(region, at) && !d.is_depth(h)) {
                    Some(face) => release(face.iter().map(|&(c, w)| w as i128 * self.theta[base + c as usize] as i128).sum(), STATE_BITS),
                    None => self.strand_row(region, base, 1, at)[0] as i128,
                };
                // A depth ring's rate is its located increment alone (base zero, [`FieldDeclaration::depth`]).
                let k = if d.is_depth(h) { rate } else { one + rate };
                if t > 0 {
                    clock += k;
                    variation += k.abs();
                }
                kappa.push(fit64(k)?);
                tau.push(fit64(clock)?);
                sigma.push(fit64(variation)?);
            }
            let rest = if d.is_depth(h) { 0 } else { one };
            out.plain.push(kappa.iter().all(|&k| k as i128 == rest));
            out.kappa.push(kappa);
            out.tau.push(tau);
            out.sigma.push(sigma);
        }
        Ok(out)
    }

    /// The material's families, each `(start, len, grain)`.
    pub fn families(&self) -> &[(usize, usize, u32)] {
        &self.layout.families
    }

    /// The material's layout.
    pub fn layout(&self) -> &FieldLayout {
        &self.layout
    }

    /// Each turned slot's period and its ring's phasors on `2^(−30)` (a realization's resident
    /// frames).
    pub fn rings(&self) -> &[(usize, Vec<(i64, i64)>)] {
        &self.rings
    }

    /// The exponential's resident face (the Gibbs weights' navigator).
    pub fn exponential(&self) -> &Exponential {
        &self.exponential
    }

    /// The temperatures' exponential at the material's grain (§16.12), whose roots past the sixteenth the card
    /// multiplies after its resident face.
    pub fn fine_exponential(&self) -> &Exponential {
        &self.fine
    }

    /// [definition; agent-inferred, November 1] **A score's term** (§14.11): `2^z` for `z` on
    /// `2^(−16)` bits, as its whole bits `a = ⌊z⌋` and its fraction's face `2^(f − 1)` on `2^(−62)`
    /// (in `[2^61, 2^62)`), so a term is `face · 2^(a − 61)` and keeps its own exponent.
    pub fn face(&self, z: i64) -> (i64, u128) {
        (z >> FACE_BITS, self.exponential.below_one((z & ((1 << FACE_BITS) - 1)) as i128 - (1i128 << FACE_BITS)))
    }

    /// [measurement] The rates of a region's paced heads (§16): their least and greatest `κ` on `2^(−24)`, a reading
    /// for the receipts (`None` where the field reads no pace).
    pub fn pace_range(&self, region: &Region) -> Result<Option<(i64, i64)>> {
        self.admit_region(region)?;
        let paces = self.paces(region)?;
        let all = paces.kappa.iter().flatten().copied();
        Ok(all.clone().min().zip(all.max()))
    }

    /// [measurement] A region's opening faces `x⁰` (`[t][D]` on `2^(−16)`), a reading for the receipts.
    pub fn opening(&self, region: &Region) -> Result<Vec<i64>> {
        self.admit_region(region)?;
        let paces = self.paces(region)?;
        let moment = self.moments_of(region, &paces)?;
        self.open(region, &moment)
    }

    /// [measurement] Each paced head's rates `κ` over a region on `2^(−24)` (§16), a reading for the receipts.
    pub fn pace_rates(&self, region: &Region) -> Result<Vec<(usize, Vec<i64>)>> {
        self.admit_region(region)?;
        let paces = self.paces(region)?;
        Ok((0..self.declaration.heads).filter_map(|h| paces.row[h].map(|p| (h, paces.kappa[p].clone()))).collect())
    }

    /// The turn's face `e^(2πi ρ/n)` on `2^(−30)` at a clock `ρ` on `2^(−24)` ([`turn_phasor`]), for a reading's or a
    /// fixture's hand-set charts.
    pub fn turn_face(&self, rho: i128, n: usize) -> (i64, i64) {
        turn_phasor(rho, n, self.pi)
    }

    /// The half turn on `2^(−46)`, the turn's faces' navigator (§16; the card reads it).
    pub fn half_turn(&self) -> i128 {
        self.pi
    }

    /// `ln 2` on `2^(−30)`, the weights' return reads it.
    pub fn ln2(&self) -> i128 {
        ln2_face()
    }

    /// The frame of local mode `l` of head `h` at site `t`, on `2^(−30)`: the identity in a head of
    /// a still ring set, the mode's ring in a turned one.
    fn frame(&self, paces: &Paces, t: usize, h: usize, l: usize) -> (i64, i64) {
        let d = &self.declaration;
        let set = h % d.frames;
        if set < d.still {
            return (1i64 << MOVE_BITS, 0);
        }
        let slot = l * (d.frames - d.still) + set - d.still;
        let (n, ring) = &self.rings[slot];
        // A turned head's frame is its own clock's (§16, Law 1): the byte place where its pace is plain.
        match paces.row.get(h).copied().flatten() {
            Some(p) if !paces.plain[p] || d.is_depth(h) => self.turn(slot, paces.tau[p][t] as i128),
            _ => ring[t % n],
        }
    }

    fn reaches(&self) -> Reaches {
        let (dw, m2, f) = (self.declaration.width, 2 * self.declaration.complex(), self.declaration.contacts);
        let l = &self.layout;
        let r = |start: usize, len: usize| reach(&self.theta[start..start + len]);
        Reaches { probe: r(l.probe, m2 * dw), q: r(l.q, m2 * dw), v: r(l.v, m2 * dw), out: r(l.out, dw * m2), a: r(l.a, f * dw), b: r(l.b, f * dw), w: r(l.w, dw * f), read: r(l.read, dw * dw), moment_face: r(l.moment_face, dw * m2) }
    }

    fn admit_region(&self, region: &Region) -> Result<()> {
        if region.classes.len() != region.unresolved.len() || region.classes.len() < 2 {
            return refuse("a region needs one class and one resolution a site, and two sites to meet");
        }
        if region.classes.len() > self.declaration.reach {
            return refuse("a region past the field's reach, where its frames would repeat");
        }
        if region.classes.iter().any(|&c| c >= self.declaration.alphabet) {
            return refuse("a region's class outside the field's alphabet");
        }
        if !region.faces.is_empty() && region.faces.len() != region.classes.len() {
            return refuse("a region's carried faces that are not one a site");
        }
        for face in region.faces.iter().flatten() {
            if face.is_empty() || face.iter().any(|&(c, w)| c as usize >= self.declaration.alphabet || w > 1 << STATE_BITS) {
                return refuse("a carried face that is empty, or whose class is outside the alphabet or share past one");
            }
        }
        if !region.echo.is_empty() && region.echo.len() != region.classes.len() {
            return refuse("a region's echoes that are not one a site");
        }
        if region.echo.iter().flatten().any(|e| e.logits.len() != self.declaration.alphabet) {
            return refuse("an echo whose logits are not one a class");
        }
        if !region.locked.is_empty() && (region.locked.len() != region.classes.len() || (0..region.classes.len()).any(|t| region.locked[t] && Self::carried(region, t).is_none())) {
            return refuse("a region's locks that are not one a site, or a lock on a site that carries no face");
        }
        if let Some(port) = region.port {
            // [§16.47] A port at its boundary may hold resolved places (a state of the writer's path); it compares its open ones.
            // A pull compares its first place alone, and the places past it may stand resolved.
            if port.start > region.classes.len() || (!port.boundary && !port.letters && port.pull.is_none() && region.unresolved[port.start..].iter().any(|&u| !u)) || (port.start..region.classes.len()).any(|t| region.locked.get(t).copied().unwrap_or(false)) {
                return refuse("a port whose places are not every open, unlocked site to the region's end");
            }
            if port.void >= self.declaration.alphabet || port.target.iter().any(|&c| c == port.void || c >= self.declaration.alphabet) {
                return refuse("a port's void or target outside the alphabet, or a target cell that is the void");
            }
            if port.target.len() > region.classes.len() - port.start {
                return refuse("a port with more target cells than places");
            }
        }
        Ok(())
    }

    /// [definition; agent-inferred, November 1] **A definite site** (§14.1): known (resolved and
    /// carrying no mixture) or locked (a foil). Only definite sources are heard past the near field.
    fn definite(region: &Region, t: usize) -> bool {
        (!region.unresolved[t] && Self::carried(region, t).is_none()) || region.locked.get(t).copied().unwrap_or(false)
    }

    /// The face a site is carried as, if any.
    fn carried<'r>(region: &'r Region, t: usize) -> Option<&'r Shares> {
        region.faces.get(t).and_then(Option::as_ref)
    }

    /// Site `s`'s opening term in the encoding at `base`: its row, or the superposition of its
    /// carried face's rows, `release(Σ_a w_a E(a), 16)`, added into `x`.
    fn opening_term(&self, region: &Region, base: usize, s: usize, x: &mut [i64]) {
        let dw = self.declaration.width;
        match Self::carried(region, s) {
            None => {
                let start = base + self.row(region, s) * dw;
                for (slot, &e) in x.iter_mut().zip(&self.theta[start..start + dw]) {
                    *slot += e as i64;
                }
            }
            Some(face) => {
                for (i, slot) in x.iter_mut().enumerate() {
                    let sum: i128 = face.iter().map(|&(c, w)| w as i128 * self.theta[base + c as usize * dw + i] as i128).sum();
                    *slot += release(sum, STATE_BITS) as i64;
                }
            }
        }
    }

    /// The opening term's return: `dx` into site `s`'s row, or each carried class's row by its
    /// share, `release(w_a dx, 16)` a term.
    fn opening_return(&self, region: &Region, base: usize, s: usize, dx: &[i64], g: &mut [i128]) {
        let dw = self.declaration.width;
        match Self::carried(region, s) {
            None => {
                let start = base + self.row(region, s) * dw;
                for i in 0..dw {
                    g[start + i] += dx[i] as i128;
                }
            }
            Some(face) => {
                for &(c, w) in face {
                    for i in 0..dw {
                        g[base + c as usize * dw + i] += release(w as i128 * dx[i] as i128, STATE_BITS);
                    }
                }
            }
        }
    }

    /// A site's encoding row: its class, or the unresolved row.
    fn row(&self, region: &Region, t: usize) -> usize {
        if region.unresolved[t] { self.declaration.alphabet } else { region.classes[t] }
    }

    /// [definition; agent-inferred, November 3, §16.28] **An open site is silent on the strand**: unresolved and carrying
    /// no face, nothing has arrived there, so it adds nothing to any site's moment and its clock runs at the strand's own
    /// place (`κ = 1`). Its own opening (`E(∗)` with its neighbours' contact rows) is its own and stays.
    fn silent(region: &Region, t: usize) -> bool {
        region.unresolved[t] && Self::carried(region, t).is_none()
    }

    /// [definition; agent-inferred, November 5, the unified-theory reading of 21:07] **A silent stretch past the last arrival
    /// is one passage**: the first silent place past a region's last arrival (its last site that is not silent), or the
    /// region's length where none is. Past it every place runs the free clock at that place's rate (its expected duration
    /// from the tick before's face there, bare at the first tick), so a place `D` past the last arrival reads the clock
    /// `c_f + D κ₁`: nothing arrives there, and a per-blank rate would be the field's guesses about the stretch driving its
    /// own clock (near an uncertain end the faces split between the void and a byte and the clock races, §16.28). Stretches
    /// between two arrivals keep their per-blank rates.
    fn silent_stretch(region: &Region) -> usize {
        let sites = region.classes.len();
        (0..sites).rev().find(|&t| !Self::silent(region, t)).map_or(0, |last| last + 1)
    }

    /// Site `s`'s row of a family at `base` of `width` a class (its class's row, or its carried face's mixture
    /// `release(Σ_a w_a E(a), 16)`; zero at a silent site, [`Field::silent`]).
    fn strand_row(&self, region: &Region, base: usize, width: usize, s: usize) -> Vec<i64> {
        if Self::silent(region, s) {
            return vec![0; width];
        }
        match Self::carried(region, s) {
            None => self.theta[base + self.row(region, s) * width..base + (self.row(region, s) + 1) * width].iter().map(|&e| e as i64).collect(),
            Some(face) => (0..width).map(|i| release(face.iter().map(|&(c, w)| w as i128 * self.theta[base + c as usize * width + i] as i128).sum(), STATE_BITS) as i64).collect(),
        }
    }

    /// A strand row's return: `d` (on `2^(−24)`) into site `s`'s row, or each carried class's row by
    /// its share; nothing at a silent site.
    fn strand_return(&self, region: &Region, base: usize, width: usize, s: usize, d: &[i128], g: &mut [i128]) {
        if Self::silent(region, s) {
            return;
        }
        match Self::carried(region, s) {
            None => {
                let start = base + self.row(region, s) * width;
                for i in 0..width {
                    g[start + i] += d[i];
                }
            }
            Some(face) => {
                for &(c, w) in face {
                    for i in 0..width {
                        g[base + c as usize * width + i] += release(w as i128 * d[i], STATE_BITS);
                    }
                }
            }
        }
    }

    /// A turned slot's rate of turn `b = 2π/n` per unit of its clock, on `2^(−30)`.
    fn turn_rate(&self, slot: usize) -> i128 {
        release(div_nearest(2 * self.pi, self.rings[slot].0 as i128), FACE_BITS)
    }

    /// [definition; agent-inferred, November 6] **A field's last `depth` turned ring sets become depth rings**
    /// ([`FieldDeclaration::depth`]): their increments founded at zero (the rings plain, each a still head's reading with
    /// frames that can turn), every other parameter kept; a turned head that becomes a ring gives up its clock and its moment.
    pub fn with_depth(mut self, depth: usize) -> Result<Self> {
        let declaration = FieldDeclaration { depth, ..self.declaration };
        declaration.admit()?;
        let width = declaration.alphabet + 1;
        for (p, h) in (0..declaration.heads).filter(|&h| declaration.carries_moment(h)).enumerate() {
            if declaration.is_depth(h) && !self.declaration.is_depth(h) {
                let base = self.layout.pace + p * width;
                for v in &mut self.theta[base..base + width] {
                    *v = 0;
                }
            }
        }
        self.declaration = declaration;
        Ok(self)
    }

    /// Head `h`'s clock as the moment reads it ([`moment::Pace`]): none where its pace is plain (the byte place).
    fn pace_of<'a>(&self, paces: &'a Paces, h: usize, turn: &'a dyn Fn(i128) -> (i64, i64), skin: &'a dyn Fn(i128) -> i64) -> Option<moment::Pace<'a>> {
        let p = paces.row.get(h).copied().flatten()?;
        (!paces.plain[p]).then(|| moment::Pace { tau: &paces.tau[p], sigma: &paces.sigma[p], turn, skin })
    }

    /// The (slot, period) of head `h`'s local mode `l` among the turned rings.
    fn slot(&self, h: usize, l: usize) -> usize {
        let d = &self.declaration;
        l * (d.frames - d.still) + h % d.frames - d.still
    }

    /// [definition; agent-inferred, November 1] **Each site's moments** (§15.1, [`moment::moments`]),
    /// `[t][2M]` on `2^(−16)`, nonzero only at the modes that carry one: mode `l` of a turned head reads
    /// the strands' moment encodings `E⁺`, `E⁻` (a site's class row or its carried mixture; nothing from a silent
    /// open site, §16.28) on its own ring and skin.
    fn moments_of(&self, region: &Region, paces: &Paces) -> Result<Vec<i64>> {
        let d = &self.declaration;
        let (m, n, sites, tm) = (d.complex(), d.modes, region.classes.len(), d.moment_modes());
        let mut out = vec![0i64; sites * 2 * m];
        if tm == 0 {
            return Ok(out);
        }
        let l = &self.layout;
        let rows = |base: usize| -> Vec<Vec<i64>> { (0..sites).map(|t| self.strand_row(region, base, 2 * tm, t)).collect() };
        let (eb, ea) = (rows(l.moment_before), rows(l.moment_after));
        for h in (0..d.heads).filter(|&h| d.carries_moment(h) && !d.is_depth(h)) {
            for li in 0..n {
                let idx = d.moment_index(h) + li;
                let slot = self.slot(h, li);
                let (period, ring) = &self.rings[slot];
                let pick = |e: &[Vec<i64>]| -> Vec<(i64, i64)> { e.iter().map(|r| (r[idx], r[tm + idx])).collect() };
                let (turn, skin) = (|r: i128| self.turn(slot, r), |s: i128| self.skin(slot, s));
                let pace = self.pace_of(paces, h, &turn, &skin);
                let s = moment::moments(&pick(&eb), &pick(&ea), ring, *period, &self.decays[slot], pace.as_ref())?;
                for (t, &(re, im)) in s.iter().enumerate() {
                    out[t * 2 * m + h * n + li] = re;
                    out[t * 2 * m + m + h * n + li] = im;
                }
            }
        }
        Ok(out)
    }

    /// The moments' return (§15.1, [`moment::moments_return`]): each moment mode's value covector summed
    /// over the ticks, `dm` (`[t][2M]` on `2^(−24)`), back to the strands' encodings.
    fn moments_return(&self, region: &Region, paces: &Paces, dm: &[i128], g: &mut [i128], gtau: &mut [Vec<i128>], gsig: &mut [Vec<i128>]) -> Result<()> {
        let d = &self.declaration;
        let (m, n, sites, tm) = (d.complex(), d.modes, region.classes.len(), d.moment_modes());
        if tm == 0 {
            return Ok(());
        }
        let l = &self.layout;
        let rows = |base: usize| -> Vec<Vec<i64>> { (0..sites).map(|t| self.strand_row(region, base, 2 * tm, t)).collect() };
        let (eb, ea) = (rows(l.moment_before), rows(l.moment_after));
        let (mut db, mut da) = (vec![vec![0i128; 2 * tm]; sites], vec![vec![0i128; 2 * tm]; sites]);
        for h in (0..d.heads).filter(|&h| d.carries_moment(h) && !d.is_depth(h)) {
            for li in 0..n {
                let idx = d.moment_index(h) + li;
                let slot = self.slot(h, li);
                let (period, ring) = &self.rings[slot];
                let ds: Vec<(i64, i64)> = (0..sites).map(|t| Ok((fit64(dm[t * 2 * m + h * n + li])?, fit64(dm[t * 2 * m + m + h * n + li])?))).collect::<Result<_>>()?;
                let (turn, skin) = (|r: i128| self.turn(slot, r), |s: i128| self.skin(slot, s));
                let pace = self.pace_of(paces, h, &turn, &skin);
                let (back_b, back_a) = moment::moments_return(&ds, ring, *period, &self.decays[slot], pace.as_ref())?;
                // A paced head's moments turn and decay by its clock (§16): their covector returns to it.
                if let Some(p) = paces.row[h] {
                    let full = moment::Pace { tau: &paces.tau[p], sigma: &paces.sigma[p], turn: &turn, skin: &skin };
                    let pick = |e: &[Vec<i64>]| -> Vec<(i64, i64)> { e.iter().map(|r| (r[idx], r[tm + idx])).collect() };
                    let (before, after) = (pick(&eb), pick(&ea));
                    let s = moment::moments(&before, &after, ring, *period, &self.decays[slot], pace.as_ref())?;
                    let (dt, dsg) = moment::pace_return(&before, &after, &s, &ds, &back_b, &back_a, ring, *period, &self.decays[slot], &full, self.turn_rate(slot))?;
                    for t in 0..sites {
                        gtau[p][t] += dt[t];
                        gsig[p][t] += dsg[t];
                    }
                }
                for t in 0..sites {
                    (db[t][idx], db[t][tm + idx]) = back_b[t];
                    (da[t][idx], da[t][tm + idx]) = back_a[t];
                }
            }
        }
        for t in 0..sites {
            self.strand_return(region, l.moment_before, 2 * tm, t, &db[t], g);
            self.strand_return(region, l.moment_after, 2 * tm, t, &da[t], g);
        }
        Ok(())
    }

    /// The region's opening faces `x⁰`: each site's row of the encoding with its strand
    /// neighbours' rows of their own encodings and its moment read through its chart,
    /// `x⁰_t = E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1)) + release(C s_t + b, 24)` (§16.22; a region's first site has no
    /// site before it, its last none after), `moment` the region's moments `[t][2M]` ([`Field::moments_of`]).
    fn open(&self, region: &Region, moment: &[i64]) -> Result<Vec<i64>> {
        let d = &self.declaration;
        let (dw, m2) = (d.width, 2 * d.complex());
        let sites = region.classes.len();
        let l = &self.layout;
        let reach_c = reach(&self.theta[l.moment_face..l.moment_face + dw * m2]);
        let mut x = vec![0i64; sites * dw];
        let mut term = vec![0i64; dw];
        for (t, xt) in x.chunks_exact_mut(dw).enumerate() {
            self.opening_term(region, l.enc, t, xt);
            if t > 0 {
                self.opening_term(region, l.before, t - 1, xt);
            }
            if t + 1 < sites {
                self.opening_term(region, l.after, t + 1, xt);
            }
            affine(&self.theta[l.moment_face..l.moment_face + dw * m2], reach_c, m2, &moment[t * m2..(t + 1) * m2], Some(&self.theta[l.moment_face_bias..l.moment_face_bias + dw]), MATERIAL_BITS, MATERIAL_BITS, &mut term)?;
            for (slot, &v) in xt.iter_mut().zip(&term) {
                *slot = fit64(*slot as i128 + v as i128)?;
            }
        }
        Ok(x)
    }

    /// One tick of the constitution over the region's faces `x` (`[t][D]`), its temporaries
    /// written to `cell`.
    #[allow(clippy::too_many_arguments)]
    fn tick(&self, x: &mut [i64], definite: &[bool], keyed: &[bool], paces: &Paces, moment: &[i64], reaches: &Reaches, window: Option<&[bool]>, cell: &mut TickCell) -> Result<()> {
        let d = &self.declaration;
        let (dw, m, n, f, heads) = (d.width, d.complex(), d.modes, d.contacts, d.heads);
        let m2 = 2 * m;
        let sites = x.len() / dw;
        let l = &self.layout;
        let (trits, buckets) = (d.class_trits(), d.classes());
        // The chart, lane by lane.
        cell.read = Vec::with_capacity(sites * dw);
        cell.scale = Vec::with_capacity(sites * d.lanes);
        for xt in x.chunks_exact(dw) {
            lane_chart(xt, d.lanes, &mut cell.read, &mut cell.scale)?;
        }
        // The key word a head, and the value.
        let mut q = vec![0i64; sites * m2];
        let mut v = vec![0i64; sites * m2];
        for t in 0..sites {
            let rt = &cell.read[t * dw..(t + 1) * dw];
            affine(&self.theta[l.q..l.q + m2 * dw], reaches.q, dw, rt, Some(&self.theta[l.q_bias..l.q_bias + m2]), MATERIAL_BITS, MATERIAL_BITS, &mut q[t * m2..(t + 1) * m2])?;
            affine(&self.theta[l.v..l.v + m2 * dw], reaches.v, dw, rt, Some(&self.theta[l.v_bias..l.v_bias + m2]), MATERIAL_BITS, MATERIAL_BITS, &mut v[t * m2..(t + 1) * m2])?;
            // A value is linear in its site's moment (§15.1), never normalized before it.
            for (vv, &mv) in v[t * m2..(t + 1) * m2].iter_mut().zip(&moment[t * m2..(t + 1) * m2]) {
                *vv = fit64(*vv as i128 + mv as i128)?;
            }
        }
        // Every receiver's probe (§16.19): its own chart of the same read.
        let mut pr = vec![0i64; sites * m2];
        for t in 0..sites {
            let rt = &cell.read[t * dw..(t + 1) * dw];
            affine(&self.theta[l.probe..l.probe + m2 * dw], reaches.probe, dw, rt, Some(&self.theta[l.probe_bias..l.probe_bias + m2]), MATERIAL_BITS, MATERIAL_BITS, &mut pr[t * m2..(t + 1) * m2])?;
            // [definition; §16.20] A receiver asks with what has reached its place: its probe reads its moment at the
            // turned modes, the moment its value carries (§15.1), so an open site probes by its strand's sources.
            for (pp, &mv) in pr[t * m2..(t + 1) * m2].iter_mut().zip(&moment[t * m2..(t + 1) * m2]) {
                *pp = fit64(*pp as i128 + mv as i128)?;
            }
        }
        // The resonance classes, head by head (§12, §16.19): a source's the shells of its unframed key word (the
        // class it is met in), a receiver's the shells of its unframed probe word and the classes it probes
        // across their seams (the classes it meets).
        let class_of = |word: &[i64], t: usize, h: usize| (0..trits).rev().fold(0u32, |c, li| 3 * c + shell(word[t * m2 + h * n + li], word[t * m2 + m + h * n + li]));
        cell.classes = (0..heads)
            .map(|h| {
                let class = (0..sites).map(|t| class_of(&q, t, h)).collect();
                let probe_class = (0..sites).map(|t| class_of(&pr, t, h)).collect();
                let probed = (0..sites).map(|t| probes((0..trits).map(|li| (pr[t * m2 + h * n + li], pr[t * m2 + m + h * n + li])), band_bits(trits))).collect();
                ClassLists::of(class, definite.to_vec(), buckets).probing(probe_class, probed).keyed(keyed.to_vec())
            })
            .collect();
        cell.word = q.clone();
        cell.vword = v.clone();
        cell.probe = pr.clone();
        // The frame, by head: [h][t][2n], real parts then imaginary.
        let span = 2 * n;
        cell.q = vec![0i64; heads * sites * span];
        cell.v = vec![0i64; heads * sites * span];
        for h in 0..heads {
            for t in 0..sites {
                let at = (h * sites + t) * span;
                for li in 0..n {
                    let c = h * n + li;
                    let (ur, ui) = self.frame(paces, t, h, li);
                    let (ur, ui) = (ur as i128, ui as i128);
                    let (qr, qi) = (q[t * m2 + c] as i128, q[t * m2 + m + c] as i128);
                    let (vr, vi) = (v[t * m2 + c] as i128, v[t * m2 + m + c] as i128);
                    cell.q[at + li] = fit64(release(ur * qr - ui * qi, MOVE_BITS))?;
                    cell.q[at + n + li] = fit64(release(ui * qr + ur * qi, MOVE_BITS))?;
                    cell.v[at + li] = fit64(release(ur * vr - ui * vi, MOVE_BITS))?;
                    cell.v[at + n + li] = fit64(release(ui * vr + ur * vi, MOVE_BITS))?;
                }
            }
        }
        // The contact pairs words at unit power: each head's framed word read as a ratio to its own
        // power (`ratio_to_power` over the head's `2n` reals), so a word's contact with an equal word
        // is `2n`, the most any pair reaches, and a pair's is `2n` times its cosine.
        cell.qscale = vec![0i128; heads * sites];
        for hs in 0..heads * sites {
            let slice = &mut cell.q[hs * span..(hs + 1) * span];
            let (r, s) = ratio_to_power(slice)?;
            for (slot, v) in slice.iter_mut().zip(r) {
                *slot = v as i64;
            }
            cell.qscale[hs] = s;
        }
        // The probe framed and at unit power alike.
        cell.pq = vec![0i64; heads * sites * span];
        cell.pscale = vec![0i128; heads * sites];
        for h in 0..heads {
            for t in 0..sites {
                let at = (h * sites + t) * span;
                for li in 0..n {
                    let c = h * n + li;
                    let (ur, ui) = self.frame(paces, t, h, li);
                    let (ur, ui) = (ur as i128, ui as i128);
                    let (qr, qi) = (pr[t * m2 + c] as i128, pr[t * m2 + m + c] as i128);
                    cell.pq[at + li] = fit64(release(ur * qr - ui * qi, MOVE_BITS))?;
                    cell.pq[at + n + li] = fit64(release(ui * qr + ur * qi, MOVE_BITS))?;
                }
                let slice = &mut cell.pq[at..at + span];
                let (r, s) = ratio_to_power(slice)?;
                for (slot, v) in slice.iter_mut().zip(r) {
                    *slot = v as i64;
                }
                cell.pscale[h * sites + t] = s;
            }
        }
        // The contact and the current over each site's support, head by head (§2.5, §14.10, §14.11,
        // §15.2): `z_ij = 2^(−β) Σ_m lock_m(ŵ_i, ŵ_j) − ⌊log₂ |i − j|⌋` on `2^(−16)` bits for a met source
        // (each mode's [`lock`] carried by its skin decay), and for each octave's crowd of definite
        // sources its mean word at the octave's falloff. The row is a series ([`SeriesRow`]): each term
        // `2^z` times its multiplier (a crowd's count) keeps its own exponent, the terms are summed whole,
        // and the current `ỹ_i = Σ_k e_k ṽ_k / Σ_k e_k` is released once; each term's share of the row is
        // formed once for the return. The current returns to the receiving site's own frame,
        // `y_i = conj(U_i) ỹ_i`.
        cell.rows = Vec::with_capacity(heads * sites);
        cell.y = vec![0i64; sites * m2];
        let one = 1u128 << WEIGHT_BITS;
        let carried = |v: Option<i128>| v.ok_or(TowerError::Refused("a lock past its 128-bit carrier"));
        cell.crowds = Vec::with_capacity(heads * sites);
        cell.sums = Vec::with_capacity(heads);
        for h in 0..heads {
            let lists = &cell.classes[h];
            let sums = Sums::of(&cell.q[h * sites * span..(h + 1) * sites * span], &cell.v[h * sites * span..(h + 1) * sites * span], definite, span);
            // [definition; agent-inferred, November 3, §16.38] **Conservation of faces**: a still head reads content
            // alone, so the definite sources of one resonance class are one face to it, and that face's mass is shared
            // among them: each source's score is lowered by the octave of its class's definite count, `⌊log₂ c⌋`, as
            // the falloff lowers it by the octave of its distance. A turned head reads place as well, and to it every
            // place is its own face.
            // [definition; agent-inferred, November 3, §16.38] A still head reads content at any distance, so its source is
            // weighed by its face's multiplicity and not by its distance; the octave of distance is a turned head's, which
            // reads place.
            let shared = !d.carries_moment(h);
            let falloff = |gap: usize, j: usize| -> i128 {
                if !shared {
                    return octave(gap) as i128;
                }
                let c = lists.class[j] as usize;
                octave(((lists.off[2 * c + 1] - lists.off[2 * c]) as usize).max(1)) as i128
            };
            for i in 0..sites {
                // [E] A receiver outside every window of a cut room meets no source this tick: its current is zero.
                if window.is_some_and(|w| !w[i]) {
                    cell.rows.push(Vec::new());
                    cell.crowds.push(Vec::new());
                    continue;
                }
                // Every receiver probes with its own probe word (§16.19), against each source's key.
                let wi = &cell.pq[(h * sites + i) * span..(h * sites + i + 1) * span];
                // The lock's temperature for this receiver's kind (§15.10).
                let temper = self.temper(h, lists.listens(i))?;
                let mut series = SeriesRow::new(span);
                let mut row: Vec<Source> = Vec::new();
                for j in lists.support(i) {
                    let wj = &cell.q[(h * sites + j) * span..(h * sites + j + 1) * span];
                    let vj = &cell.v[(h * sites + j) * span..(h * sites + j + 1) * span];
                    // Each mode's lock carried by its skin decay across the pair's distance, summed
                    // whole and released once (a still head's `D = 1` reads the bare lock exactly).
                    let d = i.abs_diff(j);
                    let mut s = 0i128;
                    let mut value = vec![0i128; span];
                    for li in 0..n {
                        let decay = self.pair_decay(paces, h, li, i, j);
                        s = carried(s.checked_add(lock((wi[li] as i128, wi[n + li] as i128), (wj[li] as i128, wj[n + li] as i128), 1, decay)?))?;
                        (value[li], value[n + li]) = (decayed(decay, vj[li]), decayed(decay, vj[n + li]));
                    }
                    let base = fit64(release(s, FACE_BITS + 2 * self.decay(h, 0, d).1 + 1))?;
                    let z = fit64(release(temper * base as i128, MATERIAL_BITS) - (falloff(d, j) << FACE_BITS))?;
                    series.push(self.face(z), one, one, &value);
                    row.push(Source { j: j as u32, p: 0, s: base });
                }
                // The far field blurred (§14.10): each octave's crowd of definite sources on each side,
                // heard as `|C|` sources at the mean of their words at the octave's falloff; its value
                // term is its decayed value sum, its mass term `|C|` times its face.
                let mut crowds: Vec<Crowd> = Vec::new();
                // An open receiver hears every definite source sharply (§15.9), so no crowd of them.
                for (lo, hi_, level) in crowd_ranges(i, sites).into_iter().filter(|_| !lists.listens(i)) {
                    let count = sums.count(lo, hi_);
                    if count == 0 {
                        continue;
                    }
                    let word = sums.words(lo, hi_);
                    let mut score = 0i128;
                    let mut value = vec![0i128; span];
                    for li in 0..n {
                        let decay = self.octave_decay(paces, h, li, i, level, lo > i);
                        score = carried(score.checked_add(lock((wi[li] as i128, wi[n + li] as i128), (word[li], word[n + li]), count as i128, decay)?))?;
                        (value[li], value[n + li]) = (decayed_wide(decay, sums.value(lo, hi_, li)), decayed_wide(decay, sums.value(lo, hi_, n + li)));
                    }
                    let base = fit64(div_nearest(score, ((count * count) as i128) << (FACE_BITS + 2 * self.decay(h, 0, 1 << level).1 + 1)))?;
                    let z = fit64(release(temper * base as i128, MATERIAL_BITS) - ((level as i128) << FACE_BITS))?;
                    series.push(self.face(z), (count as u128) << WEIGHT_BITS, one, &value);
                    crowds.push(Crowd { lo, hi: hi_, level, count, z, e: 0, s: base });
                }
                let (framed, shares) = series.release();
                for (src, &share) in row.iter_mut().zip(&shares) {
                    src.p = share;
                }
                for (c, &share) in crowds.iter_mut().zip(&shares[row.len()..]) {
                    c.e = share;
                }
                for li in 0..n {
                    let (ur, ui) = self.frame(paces, i, h, li);
                    let (ur, ui) = (ur as i128, ui as i128);
                    let (yr, yi) = (fit64(framed[li])? as i128, fit64(framed[n + li])? as i128);
                    let c = h * n + li;
                    cell.y[i * m2 + c] = fit64(release(ur * yr + ui * yi, MOVE_BITS))?;
                    cell.y[i * m2 + m + c] = fit64(release(ur * yi - ui * yr, MOVE_BITS))?;
                }
                cell.rows.push(row);
                cell.crowds.push(crowds);
            }
            cell.sums.push(sums);
        }
        let mut o = vec![0i64; dw];
        for t in 0..sites {
            affine(&self.theta[l.out..l.out + dw * m2], reaches.out, m2, &cell.y[t * m2..(t + 1) * m2], Some(&self.theta[l.out_bias..l.out_bias + dw]), MATERIAL_BITS, MATERIAL_BITS, &mut o)?;
            for (xv, ov) in x[t * dw..(t + 1) * dw].iter_mut().zip(&o) {
                *xv = fit64(*xv as i128 + *ov as i128)?;
            }
        }
        // The pair contact.
        cell.read2 = Vec::with_capacity(sites * dw);
        cell.scale2 = Vec::with_capacity(sites * d.lanes);
        for xt in x.chunks_exact(dw) {
            lane_chart(xt, d.lanes, &mut cell.read2, &mut cell.scale2)?;
        }
        cell.a = vec![0i64; sites * f];
        cell.b = vec![0i64; sites * f];
        cell.c = vec![0i64; sites * f];
        for t in 0..sites {
            let rt = &cell.read2[t * dw..(t + 1) * dw];
            affine(&self.theta[l.a..l.a + f * dw], reaches.a, dw, rt, Some(&self.theta[l.a_bias..l.a_bias + f]), MATERIAL_BITS, MATERIAL_BITS, &mut cell.a[t * f..(t + 1) * f])?;
            affine(&self.theta[l.b..l.b + f * dw], reaches.b, dw, rt, Some(&self.theta[l.b_bias..l.b_bias + f]), MATERIAL_BITS, MATERIAL_BITS, &mut cell.b[t * f..(t + 1) * f])?;
        }
        for t in 0..sites {
            // [definition; agent-inferred, November 3, §16.34] The complex product a contact (§15.1) is a pair contact along
            // the strand: contact `e < f/2` is `a_e + i a_(f/2+e)` at the site against its strand neighbour's `b`, the one
            // before it at an even `e` and the one after at an odd ([`strand_mate`]), so two ring faces compose by adding
            // their phases, `q(x + y) = q(x) q(y)`, across the strand's contact; none past the region's ends.
            let half = f / 2;
            for e in 0..half {
                let (ar, ai) = (cell.a[t * f + e] as i128, cell.a[t * f + half + e] as i128);
                let (br, bi) = match strand_mate(t, e, sites) {
                    Some(s) => (cell.b[s * f + e] as i128, cell.b[s * f + half + e] as i128),
                    None => (0, 0),
                };
                cell.c[t * f + e] = fit64(release(ar * br - ai * bi, FACE_BITS))?;
                cell.c[t * f + half + e] = fit64(release(ar * bi + ai * br, FACE_BITS))?;
            }
            affine(&self.theta[l.w..l.w + dw * f], reaches.w, f, &cell.c[t * f..(t + 1) * f], Some(&self.theta[l.w_bias..l.w_bias + dw]), MATERIAL_BITS, MATERIAL_BITS, &mut o)?;
            for (xv, ov) in x[t * dw..(t + 1) * dw].iter_mut().zip(&o) {
                *xv = fit64(*xv as i128 + *ov as i128)?;
            }
        }
        Ok(())
    }

    /// The region's forward: `K` ticks, then each unresolved site's face. `keep` holds each tick's
    /// temporaries for the reverse.
    fn pass(&self, region: &Region, keep: bool) -> Result<FieldPass> {
        if self.declaration.energy {
            // [definition; the unified-theory reading of November 6, 22:52] An energy field's forward ([`energy`]).
            return self.energy_pass(region).map(|(pass, _)| pass);
        }
        self.admit_region(region)?;
        let d = &self.declaration;
        let dw = d.width;
        let reaches = self.reaches();
        let paces = self.paces(region)?;
        let moment = self.moments_of(region, &paces)?;
        let mut x = self.open(region, &moment)?;
        let definite: Vec<bool> = (0..region.classes.len()).map(|t| Self::definite(region, t)).collect();
        let keyed: Vec<bool> = (0..region.classes.len()).map(|t| !region.unresolved[t] || Self::carried(region, t).is_some()).collect();
        let mut out = FieldPass::default();
        let sites = region.classes.len();
        let mut trips = vec![0u128; sites];
        let mut before: Option<Vec<Vec<Source>>> = None;
        // [§16.44] The blanks run at the bare rate in the first tick, and each later tick at the faces the tick before
        // gave them, its clocks and moments read again.
        let blanks = !paces.kappa.is_empty() && (0..sites).any(|t| Self::silent(region, t));
        let window = region.window(d.ticks);
        let mut clock: Option<Box<TickClock>> = None;
        for k in 0..d.ticks {
            if let Some(s) = self.scale.as_deref().filter(|s| s.split == k) {
                out.tower = Some(self.scale_forward(s, &mut x, &definite, &keyed, keep)?);
            }
            let own = clock.take();
            let (tick_paces, tick_moment) = own.as_ref().map_or((&paces, &moment), |c| (&c.paces, &c.moment));
            let mut cell = TickCell::default();
            self.tick(&mut x, &definite, &keyed, tick_paces, tick_moment, &reaches, window.as_deref(), &mut cell)?;
            cell.clock = own;
            if blanks && k + 1 < d.ticks {
                // [the unified-theory reading of November 6, 08:16] Only the blanks a clock reads are read: every silent place up
                // to the silent stretch's first, whose rate the stretch past it runs at (every silent place under the per-blank
                // clock); a face past it is read by no clock and returns no covector (`clock_return` folds the stretch there).
                let stretch = if self.per_blank_clock { sites } else { Self::silent_stretch(region) };
                // Under `bare_stretch` no place past the last arrival reads a face, the stretch's first among them.
                let read_to = if self.bare_stretch && !self.per_blank_clock { stretch } else { stretch + 1 };
                let reads = (0..sites).map(|t| (Self::silent(region, t) && t < read_to).then(|| self.face_of(&x[t * dw..(t + 1) * dw], &reaches)).transpose()).collect::<Result<Vec<_>>>()?;
                let blank: Vec<Option<Shares>> = reads.iter().map(|r| r.as_ref().map(|r| shares(&r.face))).collect();
                let next = self.paces_with(region, &blank)?;
                let moment = self.moments_of(region, &next)?;
                clock = Some(Box::new(TickClock { paces: next, moment, blank, reads }));
            }
            out.pairs += cell.rows.iter().map(|r| r.len() as u64).sum::<u64>();
            if let Some(prev) = &before {
                round_trips(prev, &cell.rows, sites, &mut trips);
            }
            before = Some(if keep { cell.rows.clone() } else { std::mem::take(&mut cell.rows) });
            if keep {
                out.ticks.push(cell);
            }
        }
        let read = (d.ticks.saturating_sub(1) * d.heads).max(1) as u128;
        out.echo = trips.iter().map(|&t| ((t + read / 2) / read) as u64).collect();
        out.paces = paces;
        out.moment = moment;
        out.read = vec![0i32; sites * dw];
        out.lift = vec![0i64; sites * dw];
        out.scale = vec![0i128; sites * d.lanes];
        out.faces = vec![None; sites];
        out.logits = vec![None; sites];
        let l = &self.layout;
        let mut z = vec![0i64; d.alphabet];
        let (mut r, mut s) = (Vec::with_capacity(dw), Vec::with_capacity(d.lanes));
        for t in 0..sites {
            if !region.unresolved[t] {
                continue;
            }
            r.clear();
            s.clear();
            lane_chart(&x[t * dw..(t + 1) * dw], d.lanes, &mut r, &mut s)?;
            // The face reads each class through its encoding (§16.26): the lift `y = R r̂ + b_R`, then `z(a) = ⟨E(a), y⟩ + c_a`.
            let mut y = vec![0i64; dw];
            affine(&self.theta[l.read..l.read + dw * dw], reaches.read, dw, &r, Some(&self.theta[l.lift_bias..l.lift_bias + dw]), MATERIAL_BITS, MATERIAL_BITS, &mut y)?;
            self.tied(&y, &mut z)?;
            out.lift[t * dw..(t + 1) * dw].copy_from_slice(&y);
            // The cavity field (§15.3): the read less its own echo, data from the read that formed it.
            if let Some(Some(echo)) = region.echo.get(t) {
                for (zc, &lc) in z.iter_mut().zip(&echo.logits) {
                    *zc = fit64(*zc as i128 - release(echo.b as i128 * lc as i128, SHARE_BITS))?;
                }
            }
            out.faces[t] = Some(self.tempered(&z, 1));
            out.logits[t] = Some(z.clone());
            out.read[t * dw..(t + 1) * dw].copy_from_slice(&r);
            out.scale[t * d.lanes..(t + 1) * d.lanes].copy_from_slice(&s);
        }
        Ok(out)
    }

    /// [§16.44] The face a site's state `x_t` reads through the readout (the chart, the lift `R r̂ + b_R`, the encoding), at
    /// temperature one: what a blank's clock reads its expected duration from.
    fn face_of(&self, x: &[i64], reaches: &Reaches) -> Result<BlankRead> {
        let (d, l) = (&self.declaration, &self.layout);
        let dw = d.width;
        let (mut r, mut s) = (Vec::with_capacity(dw), Vec::with_capacity(d.lanes));
        lane_chart(x, d.lanes, &mut r, &mut s)?;
        let mut y = vec![0i64; dw];
        affine(&self.theta[l.read..l.read + dw * dw], reaches.read, dw, &r, Some(&self.theta[l.lift_bias..l.lift_bias + dw]), MATERIAL_BITS, MATERIAL_BITS, &mut y)?;
        let mut z = vec![0i64; d.alphabet];
        self.tied(&y, &mut z)?;
        Ok(BlankRead { read: r, scale: s, lift: y, face: self.tempered(&z, 1) })
    }

    /// [definition; agent-inferred, November 5, §16.44] **A blank's clock returns through its face**: its rate
    /// `κ = 1 + Σ_a p_a c[a]` on each paced head moves with the face, so its covector `δκ` (the clocks' suffix sums at the
    /// blank) reaches the face's logits as `δz_b = Σ_h ln 2 · p_b (c_h[b] − Σ_a p_a c_h[a]) δκ_h` (the face's own Jacobian,
    /// `z` in bits), and then the readout's reverse at the state the face was read off: the encoding's bias and rows, the
    /// lift, the chart and the lane adjoint into that state's covector `dx`. Why: the code is read at the last tick and each
    /// blank's face sets a later tick's clocks, so the face is no operand there; without this return the covector missed how
    /// a blank's clock moves with its face (the unified-theory reading of November 5).
    fn blank_return(&self, read: &BlankRead, rates: &[(usize, i128)], reaches: &Reaches, g: &mut [i128], dx: &mut [i64]) -> Result<()> {
        let (d, l) = (&self.declaration, &self.layout);
        let (dw, a) = (d.width, d.alphabet);
        let (masses, total) = (&read.face.masses, read.face.total as i128);
        if total == 0 {
            return Ok(());
        }
        // The logits' covector held `LN2_FACE_BITS` finer than the face's (`δz 2^30`), each product released once from it.
        let mut dz = vec![0i128; a];
        for &(base, dk) in rates {
            let mean = div_nearest(masses.iter().enumerate().map(|(c, &m)| m as i128 * self.theta[base + c] as i128).sum(), total);
            for (b, slot) in dz.iter_mut().enumerate() {
                let u = div_nearest(masses[b] as i128 * (self.theta[base + b] as i128 - mean), total);
                let at = dk.checked_mul(u).and_then(|x| x.checked_mul(ln2_face())).ok_or(TowerError::Refused(PACE_RETURN))?;
                *slot += release(at, PACE_BITS);
            }
        }
        for (o, &dzo) in dz.iter().enumerate() {
            g[l.read_bias + o] += release(dzo, LN2_FACE_BITS);
        }
        // The lift's covector and everything after it held `BLANK_HELD` bits finer than the readout's (`δy 2^16`), so a
        // blank's small covector is not lost to the grain before it reaches the state; each entry released once from it.
        let mut dy = vec![0i64; dw];
        for (i, slot) in dy.iter_mut().enumerate() {
            let sum = dz.iter().enumerate().try_fold(0i128, |acc, (c, &dzc)| dzc.checked_mul(self.theta[l.enc + c * dw + i] as i128).and_then(|x| acc.checked_add(x))).ok_or(TowerError::Refused(PACE_RETURN))?;
            *slot = fit64(release(sum, STATE_BITS + LN2_FACE_BITS - BLANK_HELD))?;
        }
        for (c, &dzc) in dz.iter().enumerate() {
            for (i, &yi) in read.lift.iter().enumerate() {
                g[l.enc + c * dw + i] += release(dzc.checked_mul(yi as i128).ok_or(TowerError::Refused(PACE_RETURN))?, STATE_BITS + LN2_FACE_BITS);
            }
        }
        for (i, &dyi) in dy.iter().enumerate() {
            g[l.lift_bias + i] += release(dyi as i128, BLANK_HELD);
            for (j, &rj) in read.read.iter().enumerate() {
                g[l.read + i * dw + j] += release(dyi as i128 * rj as i128, BLANK_HELD);
            }
        }
        let mut dr = vec![0i64; dw];
        transposed(&self.theta[l.read..l.read + dw * dw], reaches.read, dw, &dy, MATERIAL_BITS, &mut dr)?;
        let back = lane_adjoint(&read.read, &read.scale, &dr)?;
        for (slot, &b) in dx.iter_mut().zip(&back) {
            *slot = fit64(*slot as i128 + release(b as i128, BLANK_HELD))?;
        }
        Ok(())
    }

    /// Each unresolved site's face over the region (`None` at a resolved site).
    pub fn faces(&self, region: &Region) -> Result<Vec<Option<TowerFace>>> {
        Ok(self.pass(region, false)?.faces)
    }

    /// [measurement] **A region's rows read by where their mass lies** (§15.9's reading): over every
    /// tick, head and receiver, open receivers (`[0]`) and definite ones (`[1]`) apart: the rows, the far
    /// sources they meet, and the mass of their shares (on `2^(−63)`) on the near field, on far sources
    /// and on crowds.
    pub fn row_shares(&self, region: &Region) -> Result<RowShares> {
        let pass = self.pass(region, true)?;
        let sites = region.classes.len();
        let mut out = RowShares::default();
        for cell in &pass.ticks {
            for (hi, row) in cell.rows.iter().enumerate() {
                let i = hi % sites;
                let k = usize::from(Self::definite(region, i));
                out.rows[k] += 1;
                for src in row {
                    if (src.j as usize).abs_diff(i) < NEAR {
                        out.near[k] += src.p as u128;
                    } else {
                        out.far[k] += src.p as u128;
                        out.far_sources[k] += 1;
                    }
                }
                out.crowd[k] += cell.crowds[hi].iter().map(|c| c.e as u128).sum::<u128>();
                out.peak[k] += row.iter().map(|src| src.p).chain(cell.crowds[hi].iter().map(|c| c.e)).max().unwrap_or(0) as u128;
            }
        }
        Ok(out)
    }

    /// [measurement; agent-inferred, November 2] **A held read's rows by where their mass lies** ([`HeldRows`]):
    /// for each tick and head (`[tick · heads + head]`), over the region's unresolved sites, the shares of
    /// the question group (definite sites before `question`), of the soft near field and of the rest, and the
    /// current's part from the question group. A reading only: nothing in the law reads it.
    pub fn held_rows(&self, region: &Region, question: usize) -> Result<Vec<HeldRows>> {
        let pass = self.pass(region, true)?;
        let (sites, d) = (region.classes.len(), &self.declaration);
        let (heads, n, span) = (d.heads, d.modes, 2 * d.modes);
        let mut out = vec![HeldRows::default(); d.ticks * heads];
        for (tick, cell) in pass.ticks.iter().enumerate() {
            for h in 0..heads {
                let acc = &mut out[tick * heads + h];
                for i in (0..sites).filter(|&i| region.unresolved[i]) {
                    acc.rows += 1;
                    let hi = h * sites + i;
                    let (mut far, mut collision) = (0u128, 0u128);
                    for src in &cell.rows[hi] {
                        let j = src.j as usize;
                        let definite = Self::definite(region, j);
                        if definite && j < question {
                            acc.question += src.p as u128;
                            if i.abs_diff(j) >= NEAR {
                                far += src.p as u128;
                                collision += release(src.p as i128 * src.p as i128, SHARE_BITS) as u128;
                            }
                            let vj = &cell.v[(h * sites + j) * span..(h * sites + j + 1) * span];
                            let current: i128 = (0..span).map(|x| decayed(self.pair_decay(pass.paces_at(cell), h, x % n, i, j), vj[x]).abs()).sum();
                            acc.question_current += release(src.p as i128 * current, SHARE_BITS);
                        } else if i.abs_diff(j) < NEAR && !definite {
                            acc.soft_near += src.p as u128;
                        } else if i.abs_diff(j) < NEAR {
                            acc.near_definite += src.p as u128;
                        } else {
                            acc.other += src.p as u128;
                        }
                    }
                    acc.other += cell.crowds[hi].iter().map(|c| c.e as u128).sum::<u128>();
                    acc.question_far += far;
                    if collision > 0 {
                        acc.far_effective += ((far * far) >> (SHARE_BITS - 8)) / collision;
                        acc.far_rows += 1;
                    }
                }
            }
        }
        Ok(out)
    }

    /// [measurement; agent-inferred, November 2] **The contact covector by where its pairs lie** (§16.20): over
    /// `regions` read and returned, for each head `[near, far]`, `Σ |δs_ij|` over the near pairs (`|i − j| < NEAR`)
    /// and over the far pairs and the crowds, on the contact covector's grain. The far share, `far / (near + far)`, is
    /// the part of the probes' and keys' learning a far contact receives. A reading only.
    pub fn covector_shares(&self, regions: &[Region]) -> Result<Vec<[u128; 2]>> {
        let heads = self.declaration.heads;
        let mut out = vec![0u128; 2 * heads];
        for region in regions {
            let pass = self.pass(region, true)?;
            let mut g = vec![0i128; self.material_len()];
            self.returned_with(region, &pass, &mut g, Some(&mut out), None)?;
        }
        Ok(out.chunks_exact(2).map(|c| [c[0], c[1]]).collect())
    }

    /// [measurement; agent-inferred, November 2] **The held answer rows' currents by where they come from**
    /// ([`RowCurrent`], §16.21): for each tick, head and unresolved site of `region` in that order, the framed current's
    /// part from the question past the near field (definite sites before `question`) and from the near field, the
    /// row's largest share and, with `returning`, the code's covector of the row's framed current. A reading only.
    pub fn row_currents(&self, region: &Region, question: usize, returning: bool) -> Result<Vec<RowCurrent>> {
        let pass = self.pass(region, true)?;
        let (sites, d) = (region.classes.len(), &self.declaration);
        let (heads, n, span) = (d.heads, d.modes, 2 * d.modes);
        let mut covectors: Vec<Vec<i64>> = Vec::new();
        if returning {
            let mut g = vec![0i128; self.material_len()];
            self.returned_with(region, &pass, &mut g, None, Some(&mut covectors))?;
            covectors.reverse();
        }
        let mut out = Vec::new();
        for (tick, cell) in pass.ticks.iter().enumerate() {
            for h in 0..heads {
                for i in (0..sites).filter(|&i| region.unresolved[i]) {
                    let (mut far, mut near, mut rest) = (vec![0i128; span], vec![0i128; span], vec![0i128; span]);
                    let mut top = 0u64;
                    for src in &cell.rows[h * sites + i] {
                        let j = src.j as usize;
                        top = top.max(src.p);
                        let gap = i.abs_diff(j);
                        let into = if gap < NEAR { &mut near } else if Self::definite(region, j) && j < question { &mut far } else { &mut rest };
                        let vj = &cell.v[(h * sites + j) * span..(h * sites + j + 1) * span];
                        for (x, slot) in into.iter_mut().enumerate() {
                            *slot += release(src.p as i128 * decayed(self.pair_decay(pass.paces_at(cell), h, x % n, i, j), vj[x]), SHARE_BITS);
                        }
                    }
                    let covector = covectors.get(tick).map(|c| c[(h * sites + i) * span..(h * sites + i + 1) * span].to_vec()).unwrap_or_default();
                    out.push(RowCurrent { tick: tick as u32, head: h as u32, site: i as u32, far, near, rest, top, covector });
                }
            }
        }
        Ok(out)
    }

    /// [`Field::held_rows`] summed over `regions` (each with its own answer start `questions[r]`).
    pub fn held_rows_all(&self, regions: &[Region], questions: &[usize]) -> Result<Vec<HeldRows>> {
        if regions.len() != questions.len() {
            return refuse("a held read's answer starts that are not one a region");
        }
        let mut out = vec![HeldRows::default(); self.declaration.ticks * self.declaration.heads];
        for (region, &question) in regions.iter().zip(questions) {
            for (acc, one) in out.iter_mut().zip(self.held_rows(region, question)?) {
                acc.rows += one.rows;
                acc.question += one.question;
                acc.soft_near += one.soft_near;
                acc.other += one.other;
                acc.question_current += one.question_current;
                acc.question_far += one.question_far;
                acc.far_effective += one.far_effective;
                acc.far_rows += one.far_rows;
                acc.near_definite += one.near_definite;
            }
        }
        Ok(out)
    }

    /// Each unresolved site's readout logits over the region, on `2^(−16)` bits (`None` at a
    /// resolved site): the face at `β = 1` is [`Field::tempered`] of them.
    pub fn logits(&self, region: &Region) -> Result<Vec<Option<Vec<i64>>>> {
        Ok(self.pass(region, false)?.logits)
    }

    /// [measurement] An energy field's logits and its energy read from one forward ([`energy`]), the reference a
    /// realization's energy forward is checked against bit for bit.
    pub fn energy_logits(&self, region: &Region) -> Result<(Vec<Option<Vec<i64>>>, EnergyRead)> {
        if !self.declaration.energy {
            return refuse("an energy read of a field whose faces are not one energy's forces");
        }
        self.energy_pass(region).map(|(pass, read)| (pass.logits, read))
    }

    /// The site pairs the region's contact meets over its ticks and heads (`Σ |S_i^h|`).
    pub fn met_pairs(&self, region: &Region) -> Result<u64> {
        Ok(self.pass(region, false)?.pairs)
    }

    /// [definition; agent-inferred, November 1] **A face tempered at `β`** (the pump, §4):
    /// `p(a) = 2^(β ℓ(a)) / Σ_b 2^(β ℓ(b))` from logits `ℓ` on `2^(−16)` bits, the masses
    /// `2^(β(ℓ(a) − peak))` on the exponential's `2^(−62)`; at `β = 1` it is the field's own face.
    pub fn tempered(&self, logits: &[i64], beta: u64) -> TowerFace {
        let peak = *logits.iter().max().unwrap_or(&0);
        let masses: Vec<u128> = logits.iter().map(|&zc| self.exponential.below_one((zc as i128 - peak as i128) * beta as i128)).collect();
        let total = masses.iter().sum();
        TowerFace { masses, total }
    }

    /// The region's code on `2^(−20)` bits, and the number of sites it read: `Σ −log₂ p̂_t(u_t)` over its unresolved
    /// sites before its port, and its port's coupling code (§16.24) over the port's places.
    pub fn code(&self, region: &Region) -> Result<(i64, usize)> {
        let faces = self.faces(region)?;
        let end = region.port.map_or(region.classes.len(), |p| p.start);
        let mut code = 0i64;
        let mut count = 0usize;
        for (face, &class) in faces.iter().zip(region.classes).take(end) {
            if let Some(face) = face {
                code += face.code(class);
                count += 1;
            }
        }
        if let Some(port) = region.port {
            code += port_code(&faces, &port)?;
            let stop = port.stop.unwrap_or(region.classes.len()).min(region.classes.len());
            count += (port.start..stop).filter(|&t| region.unresolved[t] && port.heard.is_none_or(|h| h[t])).count();
        }
        Ok((code, count))
    }

    /// [definition; agent-inferred, November 3, §16.26] **The face read through the encoding**: `z(a) = release(Σ_i E(a)_i
    /// y_i, 16) + c_a` for every class `a`, `E(a)` its row of the encoding on `2^(−16)` and `y` the lift on `2^(−16)`.
    fn tied(&self, y: &[i64], z: &mut [i64]) -> Result<()> {
        let (dw, l) = (self.declaration.width, &self.layout);
        for (a, slot) in z.iter_mut().enumerate() {
            let row = &self.theta[l.enc + a * dw..l.enc + (a + 1) * dw];
            let sum: i128 = row.iter().zip(y).map(|(&e, &v)| e as i128 * v as i128).sum();
            *slot = fit64(release(sum, STATE_BITS) as i128 + self.theta[l.read_bias + a] as i128)?;
        }
        Ok(())
    }

    /// A pass's port reading ([`port_reading`]) from the faces at the port's places.
    fn port_of(&self, pass: &FieldPass, port: &Port) -> Result<(Vec<Vec<i64>>, i64)> {
        port_reading(&port_faces(&pass.faces, port)?, port)
    }

    /// The reverse of [`Field::pass`] against each unresolved site's class: the code's own covector, added
    /// into `g` on each family's natural grain (a face family's `Σ δz` on `2^(−24)`, a material family's `Σ δz x` on
    /// `2^(−40)`), which the reverse's law tests read against the code's difference.
    fn returned(&self, region: &Region, pass: &FieldPass, g: &mut [i128]) -> Result<()> {
        self.returned_with(region, pass, g, None, None)
    }

    /// [agent-inferred, November 3, §16.39] **One tick's return**: the covector `dx` of a tick's output faces carried back
    /// through its pair contact, its current and contact and its charts to the covector of its input faces, the material's
    /// covector added into `g`, the moments' into `dm` and the clocks' into `gtau` and `gsig` (with the contact covector's
    /// shares and the currents' covectors where read). A region's reverse reads its ticks through it in reverse order; a
    /// tower of scales reads each level's ticks through it.
    #[allow(clippy::too_many_arguments)]
    fn tick_return(&self, cell: &TickCell, dx: &mut [i64], g: &mut [i128], paces: &Paces, definite: &[bool], dm: &mut [i128], gtau: &mut [Vec<i128>], gsig: &mut [Vec<i128>], mut shares: Option<&mut [u128]>, mut currents: Option<&mut Vec<Vec<i64>>>) -> Result<()> {
        let d = &self.declaration;
        let (dw, m, n, f, heads, lanes) = (d.width, d.complex(), d.modes, d.contacts, d.heads, d.lanes);
        let m2 = 2 * m;
        let span = 2 * n;
        let sites = definite.len();
        let l = &self.layout;
        let reaches = self.reaches();
        let ln2 = ln2_face();
        // The pair contact: x_out = x_mid + W_c c + b_c.
        let dxs: Vec<&[i64]> = dx.chunks_exact(dw).collect();
        for dxt in &dxs {
            for (i, &v) in dxt.iter().enumerate() {
                g[l.w_bias + i] += v as i128;
            }
        }
        let cs: Vec<&[i64]> = cell.c.chunks_exact(f).collect();
        outer_sum(&mut g[l.w..l.w + dw * f], f, &dxs, &cs)?;
        let mut da = vec![0i64; sites * f];
        let mut db = vec![0i64; sites * f];
        let mut dc = vec![0i64; sites * f];
        for t in 0..sites {
            transposed(&self.theta[l.w..l.w + dw * f], reaches.w, f, dxs[t], MATERIAL_BITS, &mut dc[t * f..(t + 1) * f])?;
        }
        // `δa_t = conj(b_s) δc_t`, `δb_s = conj(a_t) δc_t` for the complex product of site `t` and its strand mate `s`
        // (§16.34); each site's `b` is one mate's, so each `δb_s` is one term.
        let half = f / 2;
        for t in 0..sites {
            for e in 0..half {
                let Some(s) = strand_mate(t, e, sites) else { continue };
                let (gr, gi) = (dc[t * f + e] as i128, dc[t * f + half + e] as i128);
                let (ar, ai) = (cell.a[t * f + e] as i128, cell.a[t * f + half + e] as i128);
                let (br, bi) = (cell.b[s * f + e] as i128, cell.b[s * f + half + e] as i128);
                da[t * f + e] = fit64(release(br * gr + bi * gi, FACE_BITS))?;
                da[t * f + half + e] = fit64(release(br * gi - bi * gr, FACE_BITS))?;
                db[s * f + e] = fit64(release(ar * gr + ai * gi, FACE_BITS))?;
                db[s * f + half + e] = fit64(release(ar * gi - ai * gr, FACE_BITS))?;
            }
        }
        let das: Vec<&[i64]> = da.chunks_exact(f).collect();
        let dbs: Vec<&[i64]> = db.chunks_exact(f).collect();
        let r2s: Vec<&[i32]> = cell.read2.chunks_exact(dw).collect();
        outer_sum(&mut g[l.a..l.a + f * dw], dw, &das, &r2s)?;
        outer_sum(&mut g[l.b..l.b + f * dw], dw, &dbs, &r2s)?;
        for t in 0..sites {
            for e in 0..f {
                g[l.a_bias + e] += das[t][e] as i128;
                g[l.b_bias + e] += dbs[t][e] as i128;
            }
        }
        let mut dmid = vec![0i64; sites * dw];
        let mut ra = vec![0i64; dw];
        let mut rb = vec![0i64; dw];
        for t in 0..sites {
            transposed(&self.theta[l.a..l.a + f * dw], reaches.a, dw, das[t], MATERIAL_BITS, &mut ra)?;
            transposed(&self.theta[l.b..l.b + f * dw], reaches.b, dw, dbs[t], MATERIAL_BITS, &mut rb)?;
            let dr: Vec<i64> = ra.iter().zip(&rb).map(|(&p, &q)| p + q).collect();
            let back = lane_adjoint(r2s[t], &cell.scale2[t * lanes..(t + 1) * lanes], &dr)?;
            for i in 0..dw {
                dmid[t * dw + i] = fit64(dx[t * dw + i] as i128 + back[i] as i128)?;
            }
        }
        // The current: x_mid = x_in + O y + b_o.
        let dms: Vec<&[i64]> = dmid.chunks_exact(dw).collect();
        for dmt in &dms {
            for (i, &v) in dmt.iter().enumerate() {
                g[l.out_bias + i] += v as i128;
            }
        }
        let ys: Vec<&[i64]> = cell.y.chunks_exact(m2).collect();
        outer_sum(&mut g[l.out..l.out + dw * m2], m2, &dms, &ys)?;
        let mut dy = vec![0i64; sites * m2];
        for t in 0..sites {
            transposed(&self.theta[l.out..l.out + dw * m2], reaches.out, m2, dms[t], MATERIAL_BITS, &mut dy[t * m2..(t + 1) * m2])?;
        }
        // The weights and the contact over each site's support, head by head.
        let mut dq = vec![0i64; sites * m2];
        let mut dv = vec![0i64; sites * m2];
        let mut dp = vec![0i64; sites * m2];
        let mut dyh = vec![0i64; sites * span];
        // The current's covectors of this tick `[h][t][2n]`, where read ([`Field::row_currents`]).
        if let Some(c) = currents.as_deref_mut() {
            c.push(vec![0i64; heads * sites * span]);
        }
        for h in 0..heads {
            // A paced head's current returns to the receiver's frame `y = conj(U) ỹ`, turned by `τ_i`:
            // `δτ_i −= b Re(conj(δy_i) i y_i)` (§16).
            if let Some(p) = paces.row[h] {
                for t in 0..sites {
                    for li in 0..n {
                        let c = h * n + li;
                        let a = (dy[t * m2 + c] as i128, dy[t * m2 + m + c] as i128);
                        let z = (cell.y[t * m2 + c] as i128, cell.y[t * m2 + m + c] as i128);
                        gtau[p][t] -= turned_back(self.turn_rate(self.slot(h, li)), a, z)?;
                    }
                }
            }
            // δỹ_i = U_i δy_i, the adjoint of the return to the receiver's frame.
            for t in 0..sites {
                for li in 0..n {
                    let c = h * n + li;
                    let (ur, ui) = self.frame(paces, t, h, li);
                    let (ur, ui) = (ur as i128, ui as i128);
                    let (gr, gi) = (dy[t * m2 + c] as i128, dy[t * m2 + m + c] as i128);
                    dyh[t * span + li] = fit64(release(ur * gr - ui * gi, MOVE_BITS))?;
                    dyh[t * span + n + li] = fit64(release(ui * gr + ur * gi, MOVE_BITS))?;
                }
            }
            if let Some(c) = currents.as_deref_mut() {
                let last = c.last_mut().expect("pushed above");
                last[h * sites * span..(h + 1) * sites * span].copy_from_slice(&dyh);
            }
            let rows = &cell.rows[h * sites..(h + 1) * sites];
            let crowds = &cell.crowds[h * sites..(h + 1) * sites];
            let sums = &cell.sums[h];
            let vh = &cell.v[h * sites * span..(h + 1) * sites * span];
            let qh = &cell.q[h * sites * span..(h + 1) * sites * span];
            let ph = &cell.pq[h * sites * span..(h + 1) * sites * span];
            // A receiver's probe word (§16.19).
            let probe_of = |i: usize, r: usize| -> i64 { ph[i * span + r] };
            let back = CONTACT_BITS + FACE_BITS + self.decay(h, 0, 0).1 - super::COVECTOR_BITS;
            // The values' return: `δṽ_jm = Σ_(i: j∈S_i) p_ij,m D_m(|i − j|) δỹ_im` with each term's
            // share `p` on `2^(−63)` (one integer sum, released once); a crowd's share is spread over
            // its members, `p_C/|C|` each, through a difference array over the places.
            let mut sv = vec![0i128; sites * span];
            let mut crowd_v = vec![0i128; (sites + 1) * span];
            for i in 0..sites {
                for src in &rows[i] {
                    let j = src.j as usize;
                    for r in 0..span {
                        sv[j * span + r] += src.p as i128 * decayed(self.pair_decay(paces, h, r % n, i, j), dyh[i * span + r]);
                    }
                }
                for c in &crowds[i] {
                    for r in 0..span {
                        let part = div_nearest(c.e as i128 * decayed(self.octave_decay(paces, h, r % n, i, c.level, c.lo > i), dyh[i * span + r]), c.count as i128);
                        crowd_v[c.lo * span + r] += part;
                        crowd_v[(c.hi + 1) * span + r] -= part;
                    }
                }
            }
            // A difference array's running prefix over the places (`[t][r]`).
            let prefixed = |diff: &[i128]| -> Vec<i128> {
                let mut out = diff[..sites * span].to_vec();
                for t in 1..sites {
                    for r in 0..span {
                        out[t * span + r] += out[(t - 1) * span + r];
                    }
                }
                out
            };
            let spread_v = prefixed(&crowd_v);
            for j in 0..sites {
                for r in 0..span {
                    // Held in the framed chart until the frame is undone below.
                    let c = h * n + r % n;
                    let slot = j * m2 + if r < n { c } else { m + c };
                    dv[slot] = fit64(release(sv[j * span + r], SHARE_BITS))?;
                    if definite[j] {
                        dv[slot] = fit64(dv[slot] as i128 + release(spread_v[j * span + r], SHARE_BITS))?;
                    }
                }
            }
            // `δz_k = ln 2 · p_k (δp_k − μ)`, `δp_k = ⟨δỹ_i, D ṽ_k⟩` on 2^(−40) (a crowd's value its decayed
            // mean), `μ = Σ_k p_k δp_k`; the falloff is the medium's constant and returns nothing. Then
            // `δs = 2^(−β) δz`.
            let mut ds: Vec<Vec<i128>> = Vec::with_capacity(sites);
            let mut dsc: Vec<Vec<i128>> = Vec::with_capacity(sites);
            for i in 0..sites {
                let (row, crowd) = (&rows[i], &crowds[i]);
                let dyi = &dyh[i * span..(i + 1) * span];
                let kind = usize::from(cell.classes[h].listens(i));
                let temper = self.temper(h, kind == 1)?;
                let dp: Vec<i128> = row
                    .iter()
                    .map(|src| {
                        let j = src.j as usize;
                        (0..n).map(|l| { let decay = self.pair_decay(paces, h, l, i, j); dyi[l] as i128 * decayed(decay, vh[j * span + l]) + dyi[n + l] as i128 * decayed(decay, vh[j * span + n + l]) }).sum()
                    })
                    .collect();
                let dpc: Vec<i128> = crowd
                    .iter()
                    .map(|c| {
                        let pairs: i128 = (0..n).map(|l| { let decay = self.octave_decay(paces, h, l, i, c.level, c.lo > i); dyi[l] as i128 * decayed_wide(decay, sums.value(c.lo, c.hi, l)) + dyi[n + l] as i128 * decayed_wide(decay, sums.value(c.lo, c.hi, n + l)) }).sum();
                        div_nearest(pairs, c.count as i128)
                    })
                    .collect();
                let mean = release(row.iter().zip(&dp).map(|(src, &dpj)| src.p as i128 * dpj).sum::<i128>() + crowd.iter().zip(&dpc).map(|(c, &dpj)| c.e as i128 * dpj).sum::<i128>(), SHARE_BITS);
                let compare = |p: i128, dpk: i128| -> i128 { release(ln2 * release(p * (dpk - mean), SHARE_BITS), MOVE_BITS) };
                let mut out = Vec::with_capacity(row.len());
                let mut dt = 0i128;
                for (src, &dpj) in row.iter().zip(&dp) {
                    let dz = compare(src.p as i128, dpj);
                    dt += release(dz * src.s as i128, FACE_BITS);
                    let dsij = release(temper * dz, MATERIAL_BITS);
                    if dsij.unsigned_abs() >> d.contact_return_bits() != 0 {
                        return refuse("a contact's covector past its return's carrier");
                    }
                    out.push(dsij);
                }
                let mut outc = Vec::with_capacity(crowd.len());
                for (c, &dpj) in crowd.iter().zip(&dpc) {
                    let dz = compare(c.e as i128, dpj);
                    dt += release(dz * c.s as i128, FACE_BITS);
                    let dsij = release(temper * dz, MATERIAL_BITS);
                    if dsij.unsigned_abs() >> d.contact_return_bits() != 0 {
                        return refuse("a contact's covector past its return's carrier");
                    }
                    outc.push(dsij);
                }
                // Into the temperature's own chart (§16.12), the row's.
                g[l.temper + 2 * h + kind] += temperature_chain(temper, dt)?;
                if let Some(sh) = shares.as_deref_mut() {
                    for (src, &v) in row.iter().zip(&out) {
                        sh[2 * h + usize::from(i.abs_diff(src.j as usize) >= NEAR)] += v.unsigned_abs();
                    }
                    sh[2 * h + 1] += outc.iter().map(|v| v.unsigned_abs()).sum::<u128>();
                }
                ds.push(out);
                dsc.push(outc);
            }
            // A paced head's skins follow its turn (§16): each pair's and crowd's `D(σ_i − σ_j)` returns to the
            // two ends of its variation, `E = 2^40 ∂/∂D` from the value (`p Re(conj(δỹ_i) D ṽ_j)/D`) and the
            // lock (`δs (2 P 2^30 − 2 D Q)` over the lock's grains), then `δσ_i −= sgn b D E`, `δσ_j += sgn b D E`.
            if let Some(p) = paces.row[h].filter(|_| !d.is_depth(h)) {
                let sigma = &paces.sigma[p];
                for i in 0..sites {
                    for (k, src) in rows[i].iter().enumerate() {
                        let j = src.j as usize;
                        let sgn = (sigma[i] - sigma[j]).signum() as i128;
                        if sgn == 0 {
                            continue;
                        }
                        for l in 0..n {
                            let (dec, g_) = self.pair_decay(paces, h, l, i, j);
                            let inner = dyh[i * span + l] as i128 * vh[j * span + l] as i128 + dyh[i * span + n + l] as i128 * vh[j * span + n + l] as i128;
                            let value = release(src.p as i128 * inner, SHARE_BITS);
                            let (wr, wi, kr, ki) = (probe_of(i, l) as i128, probe_of(i, n + l) as i128, qh[j * span + l] as i128, qh[j * span + n + l] as i128);
                            let bracket = (2 * (wr * kr + wi * ki) << g_) - 2 * dec * (kr * kr + ki * ki);
                            let lock = release(ds[i][k].checked_mul(bracket).ok_or(TowerError::Refused(PACE_RETURN))?, LOCK_BACK_BITS + 2 * g_ - MOVE_BITS);
                            let at = skin_back(self.turn_rate(self.slot(h, l)), dec, value + lock)?;
                            gsig[p][i] -= sgn * at;
                            gsig[p][j] += sgn * at;
                        }
                    }
                    for (k, c) in crowds[i].iter().enumerate() {
                        let right = c.lo > i;
                        let e = if right { i + (1 << c.level) } else { i - (1 << c.level) };
                        let sgn = (sigma[i] - sigma[e]).signum() as i128;
                        if sgn == 0 {
                            continue;
                        }
                        let count = c.count as i128;
                        for l in 0..n {
                            let (dec, g_) = self.octave_decay(paces, h, l, i, c.level, right);
                            let (vr, vi) = (sums.value(c.lo, c.hi, l), sums.value(c.lo, c.hi, n + l));
                            let inner = dyh[i * span + l] as i128 * vr + dyh[i * span + n + l] as i128 * vi;
                            let value = div_nearest(release(c.e as i128 * inner, SHARE_BITS), count);
                            let (wr, wi) = (ph[i * span + l] as i128, ph[i * span + n + l] as i128);
                            let (mr, mi) = (sums.words[(c.hi + 1) * span + l] - sums.words[c.lo * span + l], sums.words[(c.hi + 1) * span + n + l] - sums.words[c.lo * span + n + l]);
                            let bracket = div_nearest((2 * count * (wr * mr + wi * mi) << g_) - 2 * dec * (mr * mr + mi * mi), count * count);
                            let lock = release(dsc[i][k].checked_mul(bracket).ok_or(TowerError::Refused(PACE_RETURN))?, LOCK_BACK_BITS + 2 * g_ - MOVE_BITS);
                            let at = skin_back(self.turn_rate(self.slot(h, l)), dec, value + lock)?;
                            gsig[p][i] -= sgn * at;
                            gsig[p][e] += sgn * at;
                        }
                    }
                }
            }
            // Each mode's lock ([`lock`]) returns to its two words: to the receiver's probe
            // `δp̃_i += Σ_(j∈S_i) δs_ij D(|i − j|) k̃_j`, to each source's key `δk̃_j += Σ_(i: j∈S_i) δs_ij (D p̃_i − D² k̃_j)`,
            // and a crowd's `δs_C D k̄/|C|` to its receiver's probe and `δs_C (D p̃_i/|C| − D² k̄/|C|²)` to each
            // member's key; each sum released to 2^(−24).
            let mut col = vec![0i128; sites * span];
            let mut crowd_w = vec![0i128; (sites + 1) * span];
            for i in 0..sites {
                for (k, src) in rows[i].iter().enumerate() {
                    let j = src.j as usize;
                    for r in 0..span {
                        let (dec, g) = self.pair_decay(paces, h, r % n, i, j);
                        // The key's bracket `D ŵ_i − D² ŵ_j` released by the skin's bits once (a
                        // declared crossing, as the probe's `D ŵ` is), so it stands on the probe's grain.
                        let bracket = release(((dec * probe_of(i, r) as i128) << g) - dec * dec * qh[j * span + r] as i128, g);
                        col[j * span + r] = col[j * span + r].checked_add(ds[i][k].checked_mul(bracket).ok_or(TowerError::Refused(KEY_RETURN))?).ok_or(TowerError::Refused(KEY_RETURN))?;
                    }
                }
                for (k, c) in crowds[i].iter().enumerate() {
                    for r in 0..span {
                        let (dec, g) = self.octave_decay(paces, h, r % n, i, c.level, c.lo > i);
                        let mean = sums.words[(c.hi + 1) * span + r] - sums.words[c.lo * span + r];
                        let bracket = release(((dec * ph[i * span + r] as i128 * c.count as i128) << g) - dec * dec * mean, g);
                        let part = div_nearest(dsc[i][k].checked_mul(bracket).ok_or(TowerError::Refused(KEY_RETURN))?, (c.count * c.count) as i128);
                        crowd_w[c.lo * span + r] += part;
                        crowd_w[(c.hi + 1) * span + r] -= part;
                    }
                }
            }
            let spread_w = prefixed(&crowd_w);
            for i in 0..sites {
                for r in 0..span {
                    let sq: i128 = rows[i].iter().enumerate().map(|(k, src)| ds[i][k] * self.pair_decay(paces, h, r % n, i, src.j as usize).0 * qh[src.j as usize * span + r] as i128).sum::<i128>()
                        + crowds[i].iter().enumerate().map(|(k, c)| div_nearest(dsc[i][k] * self.octave_decay(paces, h, r % n, i, c.level, c.lo > i).0 * (sums.words[(c.hi + 1) * span + r] - sums.words[c.lo * span + r]), c.count as i128)).sum::<i128>();
                    // Held in the framed chart until the frame is undone below.
                    let c = h * n + r % n;
                    let slot = if r < n { c } else { m + c };
                    dp[i * m2 + slot] = fit64(release(sq, back))?;
                    dq[i * m2 + slot] = fit64(release(col[i * span + r], back))?;
                    if definite[i] {
                        dq[i * m2 + slot] = fit64(dq[i * m2 + slot] as i128 + release(spread_w[i * span + r], back))?;
                    }
                }
            }
        }
        // The word's return through its ratio to its own power, head by head:
        // `δw̃ = (δŵ − ŵ ⟨ŵ, δŵ⟩/2n) / ‖w̃‖_rms` (`ratio_adjoint`), still in the framed chart.
        for h in 0..heads {
            for t in 0..sites {
                let at = (h * sites + t) * span;
                let slot = |r: usize| t * m2 + if r < n { h * n + r } else { m + h * n + r - n };
                let unit: Vec<i32> = cell.q[at..at + span].iter().map(|&v| v as i32).collect();
                let cov: Vec<i64> = (0..span).map(|r| dq[slot(r)]).collect();
                let back = ratio_adjoint(&unit, cell.qscale[h * sites + t], &cov)?;
                for (r, b) in back.into_iter().enumerate() {
                    dq[slot(r)] = b;
                }
            }
        }
        // The probe's return through its own power, alike (§16.19).
        for h in 0..heads {
            for t in 0..sites {
                let at = (h * sites + t) * span;
                let slot = |r: usize| t * m2 + if r < n { h * n + r } else { m + h * n + r - n };
                let unit: Vec<i32> = cell.pq[at..at + span].iter().map(|&v| v as i32).collect();
                let cov: Vec<i64> = (0..span).map(|r| dp[slot(r)]).collect();
                if cov.iter().all(|&c| c == 0) {
                    continue;
                }
                let back = ratio_adjoint(&unit, cell.pscale[h * sites + t], &cov)?;
                for (r, b) in back.into_iter().enumerate() {
                    dp[slot(r)] = b;
                }
            }
        }
        // Undo the frame: δw = conj(U) δw̃, and so for the values.
        for t in 0..sites {
            for c in 0..m {
                let (ur, ui) = self.frame(paces, t, c / n, c % n);
                let (ur, ui) = (ur as i128, ui as i128);
                for chart in [&mut dq, &mut dv, &mut dp] {
                    let (gr, gi) = (chart[t * m2 + c] as i128, chart[t * m2 + m + c] as i128);
                    chart[t * m2 + c] = fit64(release(ur * gr + ui * gi, MOVE_BITS))?;
                    chart[t * m2 + m + c] = fit64(release(ur * gi - ui * gr, MOVE_BITS))?;
                }
            }
        }
        // A paced head's frames turn its word, value and probe by `τ_t` (§16): `δτ_t += b Re(conj(δw) i w)` on
        // each, read in the unframed chart (the frame is a turn, so the pairing is the framed one's).
        for h in 0..heads {
            let Some(p) = paces.row[h] else { continue };
            for t in 0..sites {
                for li in 0..n {
                    let c = h * n + li;
                    let b = self.turn_rate(self.slot(h, li));
                    for (chart, word) in [(&dq, &cell.word), (&dv, &cell.vword), (&dp, &cell.probe)] {
                        let a = (chart[t * m2 + c] as i128, chart[t * m2 + m + c] as i128);
                        let z = (word[t * m2 + c] as i128, word[t * m2 + m + c] as i128);
                        gtau[p][t] += turned_back(b, a, z)?;
                    }
                }
            }
        }
        // The values' and the probes' covectors at the moment modes, summed over the ticks (§15.1, §16.20).
        for ((slot, &v), &p) in dm.iter_mut().zip(&dv).zip(&dp) {
            *slot += v as i128 + p as i128;
        }
        let reads: Vec<&[i32]> = cell.read.chunks_exact(dw).collect();
        let mut dr_all = vec![0i64; sites * dw];
        for (w, bias, reach_w, dfam) in [(l.q, l.q_bias, reaches.q, &dq), (l.v, l.v_bias, reaches.v, &dv), (l.probe, l.probe_bias, reaches.probe, &dp)] {
            let rows: Vec<&[i64]> = dfam.chunks_exact(m2).collect();
            outer_sum(&mut g[w..w + m2 * dw], dw, &rows, &reads)?;
            let mut back = vec![0i64; dw];
            for t in 0..sites {
                for (e, &v) in rows[t].iter().enumerate() {
                    g[bias + e] += v as i128;
                }
                transposed(&self.theta[w..w + m2 * dw], reach_w, dw, rows[t], MATERIAL_BITS, &mut back)?;
                for i in 0..dw {
                    dr_all[t * dw + i] = fit64(dr_all[t * dw + i] as i128 + back[i] as i128)?;
                }
            }
        }
        for t in 0..sites {
            let back = lane_adjoint(reads[t], &cell.scale[t * lanes..(t + 1) * lanes], &dr_all[t * dw..(t + 1) * dw])?;
            for i in 0..dw {
                dx[t * dw + i] = fit64(dmid[t * dw + i] as i128 + back[i] as i128)?;
            }
        }
        Ok(())
    }

    /// [`Field::returned`], with the contact covector's magnitude by where its pairs lie added into `shares`
    /// (`[h][near, far]`, [`Field::covector_shares`]) where given.
    fn returned_with(&self, region: &Region, pass: &FieldPass, g: &mut [i128], mut shares: Option<&mut [u128]>, mut currents: Option<&mut Vec<Vec<i64>>>) -> Result<()> {
        let d = &self.declaration;
        let (dw, m, lanes) = (d.width, d.complex(), d.lanes);
        let m2 = 2 * m;
        let sites = region.classes.len();
        let l = &self.layout;
        let reaches = self.reaches();
        if d.energy {
            return refuse("an energy field's return through its ticks is not built: it is read, not trained");
        }
        if pass.ticks.len() != d.ticks {
            return refuse("a reverse reads a forward that held every tick");
        }
        let definite: Vec<bool> = (0..sites).map(|t| Self::definite(region, t)).collect();
        // The clocks' covectors (§16, Law 1): `[pace index][t]`, `2^24 ∂/∂τ_t` and `2^24 ∂/∂σ_t` on `2^(−24)`, and the
        // moments' `[t][2M]`, one set a clock (§16.44): the pass's, which the first tick and the opening read, and each
        // tick's own where its blanks ran at the faces the tick before gave them.
        let paced = pass.paces.kappa.len();
        let clocks: Vec<Option<&TickClock>> = std::iter::once(None).chain(pass.ticks.iter().map(|c| c.clock.as_deref())).collect();
        let mut returns: Vec<Option<ClockReturn>> = clocks.iter().map(|_| None).collect();
        returns[0] = Some(ClockReturn::new(paced, sites, m2));
        // The face, its covector weighed as the region's state in the joint code (§16.23): `release(δz · m/K)` on the
        // covector's grain, to the nearest, half away from zero.
        let mut dx = vec![0i64; sites * dw];
        {
            let (wm, wk) = region.weight();
            // A port's places take their coupling's covector (§16.24), every other open site its own place's.
            let ported = match region.port {
                Some(port) => Some((port.start, self.port_of(pass, &port)?.0)),
                None => None,
            };
            let mut ys: Vec<Vec<i64>> = Vec::new();
            let mut xs: Vec<&[i32]> = Vec::new();
            for t in 0..sites {
                let Some(face) = &pass.faces[t] else { continue };
                let dz = match &ported {
                    Some((start, rows)) if t >= *start => rows[t - start].clone(),
                    _ => {
                        let mut dz = covector(face, region.classes[t]);
                        if wm != wk {
                            for v in dz.iter_mut() {
                                *v = fit64(div_nearest(*v as i128 * wm as i128, wk as i128))?;
                            }
                        }
                        dz
                    }
                };
                for (o, &dzo) in dz.iter().enumerate() {
                    g[l.read_bias + o] += dzo as i128;
                }
                // Through the encoding (§16.26): `δE(a)_i += release(δz_a y_i, 16)` a term, `δy_i = release(Σ_a δz_a E(a)_i, 16)`.
                let y = &pass.lift[t * dw..(t + 1) * dw];
                let mut dy = vec![0i64; dw];
                for (i, slot) in dy.iter_mut().enumerate() {
                    let sum: i128 = dz.iter().enumerate().map(|(c, &dzc)| dzc as i128 * self.theta[l.enc + c * dw + i] as i128).sum();
                    *slot = fit64(release(sum, STATE_BITS))?;
                }
                for (c, &dzc) in dz.iter().enumerate() {
                    for (i, &yi) in y.iter().enumerate() {
                        g[l.enc + c * dw + i] += release(dzc as i128 * yi as i128, STATE_BITS);
                    }
                }
                for (i, &dyi) in dy.iter().enumerate() {
                    g[l.lift_bias + i] += dyi as i128;
                }
                let rt = &pass.read[t * dw..(t + 1) * dw];
                let mut dr = vec![0i64; dw];
                transposed(&self.theta[l.read..l.read + dw * dw], reaches.read, dw, &dy, MATERIAL_BITS, &mut dr)?;
                let back = lane_adjoint(rt, &pass.scale[t * lanes..(t + 1) * lanes], &dr)?;
                dx[t * dw..(t + 1) * dw].copy_from_slice(&back);
                ys.push(dy);
                xs.push(rt);
            }
            outer_sum(&mut g[l.read..l.read + dw * dw], dw, &ys, &xs)?;
        }
        for (k, cell) in pass.ticks.iter().enumerate().rev() {
            let at = if cell.clock.is_some() { k + 1 } else { 0 };
            let r = returns[at].get_or_insert_with(|| ClockReturn::new(paced, sites, m2));
            self.tick_return(cell, &mut dx, g, pass.paces_at(cell), &definite, &mut r.dm, &mut r.gtau, &mut r.gsig, shares.as_deref_mut(), currents.as_deref_mut())?;
            if let Some(s) = self.scale.as_deref().filter(|s| s.split == k) {
                let sp = pass.tower.as_ref().ok_or(TowerError::Refused("a tower's reverse reads a forward that held its scale"))?;
                self.scale_return(s, sp, &mut dx, g)?;
            }
            // [§16.44] A tick's own clock was read off the state this tick began from: its moments and rates return now,
            // and each blank's clock returns through its face into that state's covector.
            if let Some(c) = cell.clock.as_deref() {
                if let Some(mut r) = returns[at].take() {
                    self.clock_return(region, &c.paces, &c.blank, Some((&c.reads, &mut dx)), &mut r, g)?;
                }
            }
        }
        // The moment's chart into the face (§16.22): `δC += Σ_t δx⁰_t s_tᵀ`, `δb += Σ_t δx⁰_t`, and the moments'
        // covector `δs_t += Cᵀ δx⁰_t`, joined to the values' and the probes' before the strands' return.
        {
            let (mf, mfb) = (l.moment_face, l.moment_face_bias);
            let dxs: Vec<&[i64]> = dx.chunks_exact(dw).collect();
            let ss: Vec<&[i64]> = pass.moment.chunks_exact(m2).collect();
            outer_sum(&mut g[mf..mf + dw * m2], m2, &dxs, &ss)?;
            let mut back = vec![0i64; m2];
            let dm = &mut returns[0].as_mut().ok_or(TowerError::Refused("a reverse without the pass's clock"))?.dm;
            for t in 0..sites {
                for (o, &v) in dxs[t].iter().enumerate() {
                    g[mfb + o] += v as i128;
                }
                transposed(&self.theta[mf..mf + dw * m2], reaches.moment_face, m2, dxs[t], MATERIAL_BITS, &mut back)?;
                for (slot, &b) in dm[t * m2..(t + 1) * m2].iter_mut().zip(&back) {
                    *slot += b as i128;
                }
            }
        }
        // The pass's own clock (the first tick's and the opening's) returns last.
        if let Some(mut r) = returns[0].take() {
            self.clock_return(region, &pass.paces, &[], None, &mut r, g)?;
        }
        // The opening: each site's row of the encoding and its neighbours' rows of theirs (a carried
        // face's rows by their shares).
        for t in 0..sites {
            let dxt = &dx[t * dw..(t + 1) * dw];
            self.opening_return(region, l.enc, t, dxt, g);
            if t > 0 {
                self.opening_return(region, l.before, t - 1, dxt, g);
            }
            if t + 1 < sites {
                self.opening_return(region, l.after, t + 1, dxt, g);
            }
        }
        Ok(())
    }

    /// [§16, §16.44] **One clock's return**: the moments' covector at each moment mode through the strands, on the clock
    /// it was read on; then the clocks return to their paces: `τ_t = Σ_(0<k≤t) κ_k`, `σ_t = Σ_(0<k≤t) |κ_k|`, so `δκ_k =
    /// Σ_(t≥k) δτ_t + sgn(κ_k) Σ_(t≥k) δσ_t`; on the class sheet (§16.16) `κ_k = 1 + c[u_k]` gives `δc[u] += Σ_(k: u_k = u)
    /// δκ_k`, a carried face's classes by their shares, and a blank's by the shares of the face its clock read, on the
    /// material's covector grain (`2^(−24)` times the opening's `2^(−16)`, a whole class's share `2^16`); where the clock's
    /// blank reads are given, each blank's `δκ` also returns through its face into the state's covector
    /// ([`Field::blank_return`]). The opening takes nothing.
    #[allow(clippy::type_complexity)]
    fn clock_return(&self, region: &Region, paces: &Paces, blank: &[Option<Shares>], faces: Option<(&[Option<BlankRead>], &mut Vec<i64>)>, r: &mut ClockReturn, g: &mut [i128]) -> Result<()> {
        let d = &self.declaration;
        let (dw, m, n) = (d.width, d.complex(), d.modes);
        let m2 = 2 * m;
        let sites = region.classes.len();
        let paced = paces.kappa.len();
        let moment_modes: Vec<bool> = (0..m).map(|c| d.carries_moment(c / n) && !d.is_depth(c / n)).collect();
        for (k, slot) in r.dm.iter_mut().enumerate() {
            if !moment_modes[(k % m2) % m] {
                *slot = 0;
            }
        }
        self.moments_return(region, paces, &r.dm, g, &mut r.gtau, &mut r.gsig)?;
        if paced == 0 {
            return Ok(());
        }
        let l = &self.layout;
        let width = d.alphabet + 1;
        // Each blank's rates' covectors `(base, δκ)` a paced head, for its face's return.
        let mut rates: Vec<Vec<(usize, i128)>> = vec![Vec::new(); if faces.is_some() { sites } else { 0 }];
        let stretch = if self.per_blank_clock { sites } else { Self::silent_stretch(region) };
        for p in 0..paced {
            let base = l.pace + p * width;
            let head = (0..d.heads).find(|&h| paces.row[h] == Some(p)).ok_or(TowerError::Refused("a paced head with no row"))?;
            let (mut tail_tau, mut tail_sig) = (0i128, 0i128);
            let mut dks = vec![0i128; sites];
            for k in (1..sites).rev() {
                tail_tau += r.gtau[p][k];
                tail_sig += r.gsig[p][k];
                dks[k] = tail_tau + paces.kappa[p][k].signum() as i128 * tail_sig;
            }
            // [§16.47] The silent stretch past the last arrival runs at its first place's rate, so their covectors return there.
            if stretch < sites && !self.bare_stretch {
                let folded: i128 = dks[stretch + 1..].iter().sum();
                dks[stretch] += folded;
                for slot in &mut dks[stretch + 1..] {
                    *slot = 0;
                }
            }
            for k in (0..sites).rev() {
                let dk = dks[k];
                if dk == 0 {
                    continue;
                }
                let face = if Self::silent(region, k) { blank.get(k).and_then(Option::as_ref).filter(|_| !self.declaration.is_depth(head)) } else { Self::carried(region, k) };
                match face {
                    None if Self::silent(region, k) => {}
                    None => g[base + self.row(region, k)] += dk << STATE_BITS,
                    Some(face) => {
                        for &(c, w) in face {
                            g[base + c as usize] += dk * w as i128;
                        }
                        if Self::silent(region, k) && !rates.is_empty() {
                            rates[k].push((base, dk));
                        }
                    }
                }
            }
        }
        if let Some((reads, dx)) = faces {
            let reaches = self.reaches();
            for (t, rt) in rates.iter().enumerate().filter(|(_, rt)| !rt.is_empty()) {
                if let Some(Some(read)) = reads.get(t) {
                    self.blank_return(read, rt, &reaches, g, &mut dx[t * dw..(t + 1) * dw])?;
                }
            }
        }
        Ok(())
    }

    /// Each region's faces and the covector over the regions, summed in any order to the same bits.
    pub fn read_and_return(&self, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)> {
        let len = self.material_len();
        let (mut faces, g) = regions
            .par_iter()
            .enumerate()
            .try_fold(
                || (Vec::new(), vec![0i128; len]),
                |(mut faces, mut g), (n, region)| -> Result<_> {
                    let pass = self.pass(region, true)?;
                    self.returned(region, &pass, &mut g)?;
                    faces.push((n, pass.faces));
                    Ok((faces, g))
                },
            )
            .try_reduce(
                || (Vec::new(), vec![0i128; len]),
                |(mut fa, mut ga), (fb, gb)| {
                    fa.extend(fb);
                    for (x, y) in ga.iter_mut().zip(gb) {
                        *x += y;
                    }
                    Ok((fa, ga))
                },
            )?;
        faces.sort_by_key(|(n, _)| *n);
        Ok((faces.into_iter().map(|(_, f)| f).collect(), g))
    }

    /// Each region's faces, read in parallel.
    pub fn read_faces(&self, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>> {
        regions.par_iter().map(|r| self.faces(r)).collect()
    }

    /// Each region's unresolved sites' logits, read in parallel.
    pub fn read_logits(&self, regions: &[Region]) -> Result<Vec<FieldRead>> {
        regions.par_iter().map(|r| self.pass(r, false).map(|p| FieldRead { logits: p.logits, echo: p.echo })).collect()
    }

    /// A site's face at its pump: over every class before the extent is read, over every class but the
    /// void after it.
    /// [definition; agent-inferred, November 3, §16.27, the comparison record's §3.3] **The release by the training clock run
    /// backwards**: training reads a region whose open sites are a uniform state of a random reading order (§16.23); the
    /// release runs that clock backwards. Every answer place opens unresolved beside its known question; over `sweeps`
    /// sweeps the open places are resolved by octaves of their distance from the question, each octave in its keyed order
    /// once the earlier octaves are resolved (§16.47), about `n/sweeps` a sweep, each drawn from its own
    /// face at temperature one (the field's own probabilities, an integer draw against the face's masses) on the read
    /// of the region as it stands, with every place resolved before it known. No place is chosen by its certainty, nothing
    /// is left open, and a place drawn as the void closes the answer there: every place past it is resolved as the void,
    /// so the region stays an answer and its void tail, the only states training reads (§16.35). Returns each problem's
    /// answer places' classes, in place order, and stops early (every place it did not reach drawn on its last read) where
    /// `sweep` says to. `refine` passes then revisit the written answer, one place at a time (§16.36, §16.47); zero writes it once.
    pub fn sample_realized(&self, problems: &[(&[usize], usize)], sweeps: usize, refine: usize, void: usize, seed: u64, realization: &mut dyn FieldRealization, sweep: &mut dyn FnMut(usize, usize) -> bool) -> Result<Vec<Vec<usize>>> {
        self.sample_observed(problems, sweeps, refine, void, seed, realization, sweep, &mut |_| {})
    }

    /// [agent-inferred, November 5] **A release's read of the problems it still writes**: only the `active` problems' regions
    /// are read (a problem with no place this read is left out), and their faces are returned at their own problems'
    /// places, every other problem's empty. A region's faces are its own (each region is read alone), so the answers are the
    /// same bits; a finished problem no longer takes a region's read (the unified-theory reading of November 5, 17:41: about
    /// 60% of a 32-answer write's region reads were of finished problems).
    ///
    /// [definition; agent-inferred, November 5, the unified-theory reading of 22:38] With `near_tail`, **the writer's region ends
    /// `NEAR` places past its lowest resolved void**, as every training region and the withheld read do: the places past it are
    /// the void, resolved, and no field trained under the near tail met them (a refine pass redrew each place beside up to
    /// 2,000 of them). Its faces past the cut are none; every open place stands before it.
    fn read_active(&self, starts: &[usize], classes: &[Vec<usize>], open: &[Vec<bool>], active: &[usize], void: usize, near_tail: bool, realization: &mut dyn FieldRealization) -> Result<Vec<Vec<Option<TowerFace>>>> {
        let cut = |k: usize| -> usize {
            let len = classes[k].len();
            match (near_tail, (starts[k]..len).find(|&t| !open[k][t] && classes[k][t] == void)) {
                (true, Some(end)) => (end + NEAR).min(len),
                _ => len,
            }
        };
        let regions: Vec<Region> = active.iter().map(|&k| Region { classes: &classes[k][..cut(k)], unresolved: &open[k][..cut(k)], faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
        let mut faces: Vec<Vec<Option<TowerFace>>> = vec![Vec::new(); classes.len()];
        if regions.is_empty() {
            return Ok(faces);
        }
        for (mut read, &k) in realization.read_faces(self, &regions)?.into_iter().zip(active) {
            read.resize(classes[k].len(), None);
            faces[k] = read;
        }
        Ok(faces)
    }

    /// [measurement; agent-inferred, November 5, §16.47] **The release, read as it writes** ([`Field::sample_realized`],
    /// draw for draw): `observe` is shown every read the release makes (each sweep's and each refine step's), with every
    /// problem's classes, open places and faces as that read meets them, before its draws, and once more at the end with no
    /// faces. A reading only: nothing in the release reads it.
    #[allow(clippy::too_many_arguments)]
    pub fn sample_observed(&self, problems: &[(&[usize], usize)], sweeps: usize, refine: usize, void: usize, seed: u64, realization: &mut dyn FieldRealization, sweep: &mut dyn FnMut(usize, usize) -> bool, observe: &mut dyn FnMut(ReleaseRead)) -> Result<Vec<Vec<usize>>> {
        self.release(problems, sweeps, refine, void, seed, 0, true, false, None, false, false, false, None, RefineOrder::Keyed, realization, sweep, observe)
    }

    /// [definition; agent-inferred, November 5, the unified-theory reading of 17:41, its bound read without a maximum]
    /// **A read releases a run** ([`Field::sample_observed`] with `run_bound` on the codes' `2^(−20)` bits; zero, one place a
    /// read): past each read's free places, the walk releases each next open place of its order (within the octave in the
    /// sweeps) while the entropies of the places it adds, read on this read's faces, sum within `run_bound`; a refine pass's
    /// run reopens the next places of its order whose entropies at their last draw sum so, and draws them all from one
    /// read. Drawing a run from one read loses at most `ΣH − H_joint` of its joint, its total correlation, and since the
    /// joint holds at least the first place's entropy that is at most the added places' sum, so `run_bound` bounds the
    /// loss with no place chosen by its certainty: certainty sets only how long the run is. Why: one place a read made a
    /// write of 32 answers about 3,000 full reads; a place whose face is nearly settled adds almost nothing to the joint's
    /// loss when it is drawn beside the run's first.
    #[allow(clippy::too_many_arguments)]
    /// `near_tail` is the writer's region law ([`Field::read_active`]); `false` declares the whole room for comparison.
    /// `place_order` draws each octave's places in place order rather than its keyed order. [agent-inferred, November 6, the
    /// unified-theory reading of 03:08] `lengths`, where given, fixes each answer's length: its places past it stand resolved as
    /// the void from the first read (so the region is the question, the answer and its near tail), and every answer place,
    /// in the sweeps and in refine, draws from its face over the letters; the end never moves. `one_end` draws each answer's
    /// length from the release's first read when none is given ([`Field::release`]). `rest` lets each answer's refine
    /// passes stop where they come to rest ([`Field::release`]), `refine` then their most. `spans` makes every second refine
    /// pass a pass of span moves ([`Field::release`]). `from`, with `lengths` its answers' lengths, starts the walk from those
    /// answers instead of the sweeps, its first refine pass read without drawing ([`Field::release`]). `refine_order` is the
    /// order a single-place refine pass walks each answer in ([`RefineOrder`]).
    pub fn sample_runs(&self, problems: &[(&[usize], usize)], sweeps: usize, refine: usize, void: usize, seed: u64, run_bound: i128, near_tail: bool, place_order: bool, lengths: Option<&[usize]>, one_end: bool, rest: bool, spans: bool, from: Option<&[Vec<usize>]>, refine_order: RefineOrder, realization: &mut dyn FieldRealization, sweep: &mut dyn FnMut(usize, usize) -> bool, observe: &mut dyn FnMut(ReleaseRead)) -> Result<Vec<Vec<usize>>> {
        self.release(problems, sweeps, refine, void, seed, run_bound, near_tail, place_order, lengths, one_end, rest, spans, from, refine_order, realization, sweep, observe)
    }

    #[allow(clippy::too_many_arguments)]
    fn release(&self, problems: &[(&[usize], usize)], sweeps: usize, refine: usize, void: usize, seed: u64, run_bound: i128, near_tail: bool, place_order: bool, lengths: Option<&[usize]>, one_end: bool, rest: bool, spans: bool, from: Option<&[Vec<usize>]>, refine_order: RefineOrder, realization: &mut dyn FieldRealization, sweep: &mut dyn FnMut(usize, usize) -> bool, observe: &mut dyn FnMut(ReleaseRead)) -> Result<Vec<Vec<usize>>> {
        if sweeps == 0 || void >= self.declaration.alphabet || problems.iter().any(|&(_, n)| n == 0) {
            return refuse("a sample needs a sweep, an answer place and a void class in the alphabet");
        }
        let mix = |counter: u64| -> u64 {
            let mut z = seed.wrapping_add(counter.wrapping_mul(0x9E37_79B9_7F4A_7C15));
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        };
        let starts: Vec<usize> = problems.iter().map(|&(q, _)| q.len()).collect();
        let mut classes: Vec<Vec<usize>> = problems.iter().map(|&(q, n)| q.iter().copied().chain(std::iter::repeat_n(void, n)).collect()).collect();
        let mut open: Vec<Vec<bool>> = problems.iter().map(|&(q, n)| (0..q.len() + n).map(|t| t >= q.len()).collect()).collect();
        // [definition; agent-inferred, November 6, the unified-theory reading of 04:03] With `one_end`, **one end, one draw**: at
        // the release's first read (every answer place open, training's fully masked state) a place `d` is the void exactly when
        // the answer is shorter than `d`, so its void mass is the field's `P(L < d | q)`, the length's distribution; the end is
        // one uniform `u` against that profile, the answer's length the places before the first whose void mass passes `u` (an
        // integer comparison), and the sweeps then write given it. One `u`, not one draw a place: independent draws
        // multiply survivals, and the earliest void drawn is not the profile's draw.
        //
        // [definition; agent-inferred, November 6, the unified-theory reading of 07:21] **The draw is conditioned on the room**:
        // the answer ends within it, so `P(L ≤ t | L ≤ R) = M(t)/M(R)`, `M` the running maximum of the void mass and `R` the
        // room's last place; the end is the first place whose void mass passes `u M(R)`, read as `m_∅(t) T_R 2^32 > u m_R T_t`
        // on 256-bit products (`m_R/T_R` the profile's largest void mass). Why: unconditioned, every `u` above the void mass at the
        // room's last place landed there, so the opening's shortfall from one was drawn as length (code91: about 22 places of
        // letter mass past 1,200 on held and training alike, where the length law holds under one).
        let drawn_lengths: Option<Vec<usize>> = if one_end && lengths.is_none() {
            let active: Vec<usize> = (0..problems.len()).collect();
            let faces = self.read_active(&starts, &classes, &open, &active, void, near_tail, realization)?;
            Some(
                problems
                    .iter()
                    .enumerate()
                    .map(|(k, &(q, n))| {
                        let u = mix(((k as u64) << 40) ^ 0x0E4D) as u32 as u128;
                        let room: Vec<Option<&TowerFace>> = (0..n).map(|j| faces[k][q.len() + j].as_ref()).collect();
                        one_end_length(&room, void, u)
                    })
                    .collect(),
            )
        } else {
            None
        };
        let lengths = lengths.or(drawn_lengths.as_deref());
        let given = lengths.is_some();
        if let Some(ls) = lengths {
            if ls.len() != problems.len() {
                return refuse("a given length for each problem");
            }
            for (k, &(q, _)) in problems.iter().enumerate() {
                for slot in open[k].iter_mut().skip(q.len() + ls[k]) {
                    *slot = false;
                }
            }
        }
        // [measurement; agent-inferred, November 6, the unified-theory reading of 18:28] With `from` (and its lengths), **the walk
        // starts from given answers** (held's truth): every answer place stands resolved as given, no sweep is drawn, and the
        // first refine pass reads each place's face and keeps its standing letter, so its drive is the field's calibration on
        // those answers (zero in expectation under the faces' own joint) before the walk moves them.
        if let Some(answers) = from {
            let ls = lengths.ok_or(TowerError::Refused("a walk from given answers needs their lengths"))?;
            if answers.len() != problems.len() || answers.iter().zip(ls).any(|(a, &l)| a.len() < l) {
                return refuse("a given answer for each problem, as long as its length");
            }
            for (k, &(q, _)) in problems.iter().enumerate() {
                for t in 0..ls[k] {
                    classes[k][q.len() + t] = answers[k][t];
                    open[k][q.len() + t] = false;
                }
            }
        }
        // [definition; agent-inferred, November 5, §16.47] **The answer is released by octaves of its distance from the
        // question** (the unified-theory reading of 15:04): octave `j` holds the places at distance `[2^j, 2^(j+1))` past
        // the question (the first place at distance one), and its places open to the draws only once every place of the
        // earlier octaves is resolved; within an octave the keyed order. Why: with faces that are the true conditionals every order draws the same
        // joint, but with the field's the order decides what the end reads, and drawn in one keyed order of the whole
        // extent the end was fixed in the first reads while nearly every place was open (95% of the length's drift in
        // reads 1 to 64), so the written length barely heard the problem (its bytes correlated +0.18 with the held); by
        // octaves the end is drawn reading at least half its answer as written.
        let orders: Vec<Vec<usize>> = problems
            .iter()
            .enumerate()
            .map(|(k, &(q, n))| {
                // [definition; agent-inferred, November 6, the unified-theory reading of 00:14] With `place_order`, **the octave
                // law at every byte**: the order decides what each draw reads, and by octaves the end reads at least half its
                // answer as written; measured from the writer's own front the same reason orders every place, so each octave
                // is drawn in place order (the keyed order within an octave was the one grain where the law was dropped, a
                // byte drawn with every neighbour blank coding about 5 bits against 1.4 beside them). Runs stay.
                let mut order: Vec<usize> = (q.len()..q.len() + n).collect();
                if !place_order {
                    order.sort_by_key(|&t| (octave_of(t + 1 - q.len()), mix(((k as u64) << 32) ^ t as u64 ^ (1 << 62)), t));
                }
                order
            })
            .collect();
        // Each problem's place in its order: a sweep draws its next open places, never past its octave (the last sweep
        // draws every place left), so a place the closing law has resolved costs no read.
        let mut cursors = vec![0usize; problems.len()];
        // Each place's entropy at its last draw, for a refine pass's runs (none where the closing law resolved it).
        let mut drawn_entropy: Vec<Vec<Option<i128>>> = classes.iter().map(|c| vec![None; c.len()]).collect();
        // Each answer's refine passes' drives ([`PassDrive`]), one a pass it was redrawn in.
        let mut drives: Vec<Vec<PassDrive>> = vec![Vec::new(); problems.len()];
        let mut swept = if from.is_some() { 0 } else { sweeps };
        for done in 0..swept {
            let last = done + 1 == sweeps || !sweep(done, sweeps);
            let active: Vec<usize> = (0..problems.len()).filter(|&k| open[k].iter().any(|&u| u)).collect();
            let faces = self.read_active(&starts, &classes, &open, &active, void, near_tail, realization)?;
            let (mut bound, mut passed) = (0i128, 0usize);
            let mut runs: Vec<Vec<usize>> = Vec::with_capacity(problems.len());
            for (k, &(q, n)) in problems.iter().enumerate() {
                let count = if last { n } else { (done + 1) * n / sweeps - done * n / sweeps };
                let mut picked: Vec<usize> = Vec::new();
                while let Some(&t) = orders[k].get(cursors[k]) {
                    if picked.len() == count || (!last && picked.first().is_some_and(|&p| octave_of(p + 1 - q.len()) != octave_of(t + 1 - q.len()))) {
                        break;
                    }
                    cursors[k] += 1;
                    if open[k][t] {
                        picked.push(t);
                    }
                }
                // The run past the free places: the next open places of the octave while their entropies sum within the bound.
                if run_bound > 0 && !last && !picked.is_empty() {
                    let mut held = 0i128;
                    while let Some(&t) = orders[k].get(cursors[k]) {
                        if octave_of(picked[0] + 1 - q.len()) != octave_of(t + 1 - q.len()) {
                            break;
                        }
                        if !open[k][t] {
                            cursors[k] += 1;
                            continue;
                        }
                        let h = entropy(faces[k][t].as_ref().ok_or(TowerError::Refused("a sample's open place without a face"))?);
                        // Strictly within the bound: below one bit the places past the first hold one configuration with more
                        // than half their mass, so the read makes one choice (at one bit a fair coin can stand there).
                        if held + h >= run_bound {
                            break;
                        }
                        held += h;
                        cursors[k] += 1;
                        picked.push(t);
                    }
                    bound += held;
                }
                runs.push(picked);
            }
            observe(ReleaseRead { read: done, pass: 0, classes: &classes, open: &open, faces: Some(&faces), bound, passed, drives: &drives });
            // [definition; agent-inferred, November 5, the unified-theory reading of 22:38] **A void never unwrites a letter**: in
            // the sweeps as in refine, a place before the last written letter draws from its face restricted to the letters
            // (the void's mass removed, an integer draw against the rest), and only a place past every letter draws
            // from its whole face, so the void is drawn only where it closes nothing written. A read's places are drawn from
            // the farthest in, each beside the letters drawn past it this read. Faces that are the true conditionals are unchanged (the truth's void
            // has no mass before its last letter). A face before the last letter with no letter mass draws its whole face.
            // Why: within an octave the keyed order puts most draws before a written letter (93% in octave 6, 96% in octave
            // 7), the field's void there is a residue of about 1% that costs training 0.014 bits a place, and each such
            // draw ended the answer there: a flat hazard deaf to held (b1's write, one in 110 places at or under held and
            // past it alike, 23 of its 28 short writes cut by a void that unwrote letters).
            let mut draws: Vec<(usize, usize, usize)> = Vec::new();
            for (k, picked) in runs.iter().enumerate() {
                let q = problems[k].0.len();
                let mut last_letter = (q..classes[k].len()).rev().find(|&t| !open[k][t] && classes[k][t] != void);
                let mut far_first = picked.clone();
                far_first.sort_unstable_by(|a, b| b.cmp(a));
                for &t in &far_first {
                    let face = faces[k][t].as_ref().ok_or(TowerError::Refused("a sample's open place without a face"))?;
                    drawn_entropy[k][t] = Some(entropy(face));
                    let u = ((mix(((k as u64) << 40) ^ ((t as u64) << 8) ^ 0xD) as u128) << 64) | mix(((k as u64) << 40) ^ ((t as u64) << 8) ^ 0xE) as u128;
                    let letters = face.total - face.masses[void];
                    let c = if (given || last_letter.is_some_and(|l| t < l)) && letters > 0 {
                        let u = u % letters;
                        let mut acc = 0u128;
                        (0..face.masses.len()).filter(|&c| c != void).find(|&c| {
                            acc += face.masses[c];
                            acc > u
                        })
                    } else {
                        let u = u % face.total;
                        let mut acc = 0u128;
                        face.masses.iter().position(|&m| {
                            acc += m;
                            acc > u
                        })
                    };
                    let c = c.unwrap_or(face.masses.len() - 1);
                    if c != void && last_letter.is_none_or(|l| t > l) {
                        last_letter = Some(t);
                    }
                    draws.push((k, t, c));
                }
            }
            for (k, t, c) in draws {
                classes[k][t] = c;
                open[k][t] = false;
            }
            // [definition; agent-inferred, November 3, §16.35] The void is the class past an answer's end, so a place drawn
            // as the void is the answer's boundary: every place past it is the void, resolved, as in every state training
            // reads (an answer, then its void tail). The boundary only moves in; a letter drawn past it is past the end.
            for (k, &(q, _)) in problems.iter().enumerate() {
                if let Some(end) = (q.len()..classes[k].len()).find(|&t| !open[k][t] && classes[k][t] == void) {
                    for t in end + 1..classes[k].len() {
                        classes[k][t] = void;
                        open[k][t] = false;
                    }
                }
            }
            if last {
                if done + 1 < sweeps {
                    observe(ReleaseRead { read: done + 1, pass: 0, classes: &classes, open: &open, faces: None, bound: 0, passed: 0, drives: &drives });
                    return Ok(problems.iter().enumerate().map(|(k, &(q, _))| classes[k][q.len()..].to_vec()).collect());
                }
                break;
            }
            // Every place resolved: the sweeps are done.
            if open.iter().all(|o| o.iter().all(|&u| !u)) {
                swept = done + 1;
                break;
            }
        }
        // [definition; agent-inferred, November 3, §16.36; November 5, §16.47] **The places keep moving** (the lens of
        // November 1: an answer is a joint field whose parts move together until its faces align, never committed
        // surest-first): after every place is written, `refine` passes revisit the answer, the field's own one-place
        // resampling. Each pass walks each problem's keyed order of all its answer places, one place of each problem a
        // read, passing over a place that stands past the boundary (the first void) when its turn comes, so an end that has
        // moved is met again. A revisited place is opened again, read beside every other place as it now stands, and drawn
        // at temperature one: a place before the last letter from its face restricted to the letters (the void's mass
        // removed, an integer draw against the rest), the last letter and the boundary place from their whole faces,
        // so the end moves one place in or out a draw and the closing law holds after every draw. Why (the unified-theory
        // reading of November 5, 14:47): drawn from the whole face, a void inside erased every later letter while a
        // boundary drawn as a letter moved out one place, the new boundary waiting for the next pass, so the passes cut
        // deep and grew by one (segment 2's −4.8 places came all in its third pass, from its 14 short answers). A place
        // before the last letter whose face holds no letter mass keeps the letter it had. No place is chosen by its
        // certainty. [agent-inferred, November 6, the unified-theory reading of 00:13] The passes stop where the answer's
        // redrawn code per byte reaches real text's on this field (the walk helps only while the answer is more surprising to
        // the field than the truth is); the withheld code reads it from above, and on code86's state the passes cross it
        // between passes 3 and 4, so `refine = 3` stands for that stop. A stop on the faces' own level (held letters at least
        // as likely as draws) was built and retired: these faces are no joint's conditionals, so the walk descends
        // without pausing (to spaces and short strings over tens of passes, §16.47's settle93).
        let mut read = swept;
        let total = swept + refine * problems.iter().map(|&(_, n)| n).max().unwrap_or(0);
        let boundary = |classes: &[usize], open: &[bool], q: usize| (q..classes.len()).find(|&t| classes[t] == void && !open[t]).unwrap_or(classes.len());
        // [definition; agent-inferred, November 6, Brandon's lens of 17:31 and the unified-theory reading of 17:38] **A pass
        // comes to rest** (with `rest`): at temperature one the walk has no fixed point, so its plateau is zero net drive, not
        // zero change. Each pass sums over the places it redraws in an answer ([`PassDrive`]) the standing letters' codes
        // `S` on the faces they are redrawn from and those faces' entropies `H`; `D = S − H` is the drive (positive while
        // the answer contracts toward what its faces expect, negative while it expands), and the faces' varentropies `C`
        // are the draws' own spread (the distributed capacitance). An answer rests after the first pass whose drive is
        // within its spread, `D ≤ √C`, or fell from the pass before by no more than it, `D_(p−1) − D_p ≤ √C`, and its later
        // passes pass it over. Why (lap 24's ten passes, `PASSES.tsv`): the drawn code a place fell from 1.82 bits at pass 1
        // to 1.38 at pass 8 and rose to 1.48 by pass 10 as some answers heated (one from 1.78 to 3.73 bits a place), so a
        // fixed count both stops answers still falling and walks heating ones on.
        let mut resting = vec![false; problems.len()];
        // [definition; agent-inferred, November 6, the unified-theory reading of 17:58, the cube's move] With `spans`, **every
        // second pass moves spans**: the answer's places before its boundary are cut into spans of `2^(1 + (m − 1) mod 4)`
        // places at the `m`-th span pass (2, 4, 8, 16, then again), from a keyed offset; each span in a keyed order is opened
        // whole (silent, never a draft) and redrawn in place order, a run a read, given the rest of the answer as it stands.
        // Why: the single-place walk settles with its drive four to five times its spread (rest118), and a single-letter move
        // barely leaves a wrong word whose letters each fit their neighbours; if the walk's standing code falls below its
        // single-place plateau after span moves, the plateau was a trap of the move, and if not, the field's own faces hold
        // those words.
        let mut span_kept: Vec<Vec<Option<usize>>> = classes.iter().map(|c| vec![None; c.len()]).collect();
        let mut pass = 0u64;
        while (pass as usize) < refine && !resting.iter().all(|&r| r) {
            pass += 1;
            let mut moved: Vec<PassDrive> = vec![PassDrive::default(); problems.len()];
            let orders: Vec<Vec<usize>> = problems
                .iter()
                .enumerate()
                .map(|(k, &(q, _))| {
                    let mut order: Vec<usize> = (q.len()..classes[k].len()).collect();
                    match refine_order {
                        RefineOrder::Keyed => order.sort_by_key(|&t| (mix(((k as u64) << 32) ^ t as u64 ^ (pass << 48) ^ (1 << 62)), t)),
                        RefineOrder::Place => {}
                        RefineOrder::Reversed => order.reverse(),
                    }
                    order
                })
                .collect();
            let mut cursors = vec![0usize; problems.len()];
            let span_lists: Option<Vec<Vec<Vec<usize>>>> = (spans && pass % 2 == 0).then(|| {
                let length = 1usize << (1 + (pass / 2 - 1) % 4);
                problems
                    .iter()
                    .enumerate()
                    .map(|(k, &(q, _))| {
                        let end = boundary(&classes[k], &open[k], q.len());
                        let offset = (mix(((k as u64) << 32) ^ (pass << 48) ^ (3 << 60)) % length as u64) as usize;
                        let mut cuts: Vec<usize> = std::iter::once(q.len()).chain((q.len() + offset..end).step_by(length).filter(|&c| c > q.len())).collect();
                        cuts.push(end);
                        let mut list: Vec<Vec<usize>> = cuts.windows(2).filter(|w| w[0] < w[1]).map(|w| (w[0]..w[1]).collect()).collect();
                        list.sort_by_key(|span| (mix(((k as u64) << 32) ^ span[0] as u64 ^ (pass << 48) ^ (5 << 60)), span[0]));
                        list
                    })
                    .collect()
            });
            let mut span_cursors = vec![(0usize, 0usize); problems.len()];
            loop {
                // Each problem's next place in its order standing at or before its boundary, beside that boundary, and the run
                // past it: the next places at or before the boundary whose entropies at their last draw sum within the bound.
                let mut places: Vec<Option<(Vec<usize>, usize)>> = vec![None; problems.len()];
                for (k, &(q, _)) in problems.iter().enumerate() {
                    if resting[k] {
                        continue;
                    }
                    let end = boundary(&classes[k], &open[k], q.len());
                    if let Some(lists) = &span_lists {
                        // A span pass: the next run of the open span in place order, the next span opened whole at its turn.
                        let (si, pi) = &mut span_cursors[k];
                        let Some(span) = lists[k].get(*si) else { continue };
                        if *pi == 0 {
                            for &u in span {
                                span_kept[k][u] = Some(classes[k][u]);
                                classes[k][u] = void;
                                open[k][u] = true;
                            }
                        }
                        let mut run = vec![span[*pi]];
                        *pi += 1;
                        let mut held = 0i128;
                        while run_bound > 0 && *pi < span.len() {
                            let Some(h) = drawn_entropy[k][span[*pi]] else { break };
                            if held + h >= run_bound {
                                break;
                            }
                            held += h;
                            run.push(span[*pi]);
                            *pi += 1;
                        }
                        if *pi == span.len() {
                            (*si, *pi) = (*si + 1, 0);
                        }
                        places[k] = Some((run, end));
                        continue;
                    }
                    while let Some(&t) = orders[k].get(cursors[k]) {
                        cursors[k] += 1;
                        if t < end || (!given && t == end) {
                            places[k] = Some((vec![t], end));
                            break;
                        }
                    }
                    if let (true, Some((run, _))) = (run_bound > 0, places[k].as_mut()) {
                        let mut held = 0i128;
                        while let Some(&t) = orders[k].get(cursors[k]) {
                            if t > end || (given && t == end) {
                                cursors[k] += 1;
                                continue;
                            }
                            let Some(h) = drawn_entropy[k][t] else { break };
                            if held + h >= run_bound {
                                break;
                            }
                            held += h;
                            cursors[k] += 1;
                            run.push(t);
                        }
                    }
                }
                if places.iter().all(Option::is_none) {
                    break;
                }
                if !sweep(read, total) {
                    observe(ReleaseRead { read, pass: pass as usize, classes: &classes, open: &open, faces: None, bound: 0, passed: 0, drives: &drives });
                    return Ok(problems.iter().enumerate().map(|(k, &(q, _))| classes[k][q.len()..].to_vec()).collect());
                }
                read += 1;
                let mut kept: Vec<Vec<usize>> = vec![Vec::new(); problems.len()];
                for (k, place) in places.iter().enumerate() {
                    if let Some((run, _)) = place {
                        for &t in run {
                            if let Some(was) = span_kept[k][t].take() {
                                kept[k].push(was);
                            } else {
                                kept[k].push(classes[k][t]);
                                open[k][t] = true;
                                classes[k][t] = void;
                            }
                        }
                    }
                }
                let active: Vec<usize> = (0..problems.len()).filter(|&k| places[k].is_some()).collect();
                let faces = self.read_active(&starts, &classes, &open, &active, void, near_tail, realization)?;
                // What the read certifies is its own faces' sum past each run's first place.
                let (mut bound, mut passed) = (0i128, 0usize);
                for (k, place) in places.iter().enumerate() {
                    if let Some((run, _)) = place {
                        let mut held = 0i128;
                        for &t in &run[1..] {
                            held += entropy(faces[k][t].as_ref().ok_or(TowerError::Refused("a sample's open place without a face"))?);
                        }
                        bound += held;
                        passed += usize::from(run_bound > 0 && held >= run_bound);
                    }
                }
                observe(ReleaseRead { read: read - 1, pass: pass as usize, classes: &classes, open: &open, faces: Some(&faces), bound, passed, drives: &drives });
                for (k, place) in places.into_iter().enumerate() {
                    let Some((run, end)) = place else { continue };
                    for (&t, &was) in run.iter().zip(&kept[k]) {
                    let face = faces[k][t].as_ref().ok_or(TowerError::Refused("a sample's open place without a face"))?;
                    drawn_entropy[k][t] = Some(entropy(face));
                    let u = ((mix(((k as u64) << 40) ^ ((t as u64) << 8) ^ (pass << 56) ^ 0xD) as u128) << 64) | mix(((k as u64) << 40) ^ ((t as u64) << 8) ^ (pass << 56) ^ 0xE) as u128;
                    let whole = !given && t + 1 >= end;
                    let letters = face.total - face.masses[void];
                    // The drive is read on the face the place is drawn from: the whole face, or its letters.
                    let off_void = if whole { None } else { letters_face(face, void) };
                    if let Some(drawn) = if whole { Some(face) } else { off_void.as_ref() } {
                        if drawn.masses[was] > 0 {
                            moved[k].add(drawn, was);
                        }
                    }
                    classes[k][t] = if whole {
                        let u = u % face.total;
                        let mut acc = 0u128;
                        face.masses.iter().position(|&m| {
                            acc += m;
                            acc > u
                        }).unwrap_or(face.masses.len() - 1)
                    } else if letters == 0 {
                        was
                    } else {
                        let u = u % letters;
                        let mut acc = 0u128;
                        (0..face.masses.len()).filter(|&c| c != void).find(|&c| {
                            acc += face.masses[c];
                            acc > u
                        }).unwrap_or(was)
                    };
                    if from.is_some() && pass == 1 {
                        classes[k][t] = was;
                    }
                    moved[k].changes += usize::from(classes[k][t] != was);
                    open[k][t] = false;
                    }
                    // A run's draws read one boundary: where its last letter was drawn the void, the closing law resolves every
                    // place past it, a boundary drawn as a letter there among them.
                    let q = problems[k].0.len();
                    if let Some(first) = (q..classes[k].len()).find(|&t| classes[k][t] == void && !open[k][t]) {
                        for t in first + 1..classes[k].len() {
                            classes[k][t] = void;
                        }
                    }
                }
            }
            for k in (0..problems.len()).filter(|&k| moved[k].redrawn > 0) {
                let before = drives[k].last().map(PassDrive::drive);
                drives[k].push(moved[k]);
                resting[k] = rest && moved[k].rests(before);
            }
        }
        observe(ReleaseRead { read, pass: pass as usize + 1, classes: &classes, open: &open, faces: None, bound: 0, passed: 0, drives: &drives });
        Ok(problems.iter().enumerate().map(|(k, &(q, _))| classes[k][q.len()..].to_vec()).collect())
    }

    /// [definition; agent-inferred, November 1] **The landmarks** (the dispersing field's §3
    /// receipt): for each of `sites`, the `count` sites before `question` carrying the most weight in
    /// its still heads' currents at the last tick, `Σ_(h still) e_ij / Σ_k e_ik` on `2^(−16)` (each
    /// with its weight), the places where the answer's contacts converge. A reading only; nothing
    /// drives the release from it.
    pub fn landmarks(&self, region: &Region, question: usize, sites: &[usize], count: usize) -> Result<Vec<Vec<(usize, u64)>>> {
        let pass = self.pass(region, true)?;
        let d = &self.declaration;
        let cell = pass.ticks.last().ok_or(TowerError::Refused("a pass with no tick"))?;
        let n = region.classes.len();
        if sites.iter().any(|&i| i >= n) || question > n {
            return refuse("a landmark site outside its region");
        }
        let rows = sites
            .iter()
            .map(|&i| (0..d.heads).filter(|h| h % d.frames < d.still).map(|h| (cell.rows[h * n + i].iter().map(|src| (src.j, src.p)).collect(), 1u64 << SHARE_BITS)).collect())
            .collect::<Vec<Vec<_>>>();
        Ok(landmarks_of(&rows, question, count))
    }

    /// [measurement; agent-inferred, November 5, §16.44] **Each of `sites`' clocks by tick** ([`BlankClocks`]): whether a
    /// blank gap's expected duration holds its written length, and whether the faces the clocks read still predict the
    /// byte. A reading only: nothing in the law reads it.
    pub fn blank_clocks(&self, region: &Region, sites: &[usize]) -> Result<Vec<BlankClocks>> {
        let pass = self.pass(region, true)?;
        if sites.iter().any(|&i| i >= region.classes.len()) {
            return refuse("a clock's site outside its region");
        }
        Ok(sites
            .iter()
            .map(|&i| BlankClocks {
                ticks: pass
                    .ticks
                    .iter()
                    .map(|cell| cell.clock.as_deref().and_then(|c| c.reads.get(i).and_then(Option::as_ref).map(|r| (c.paces.kappa.iter().map(|k| k[i]).collect(), r.face.clone()))))
                    .collect(),
            })
            .collect())
    }

    /// [measurement; agent-inferred, November 4, §16.42] **Each of `sites`' near field by offset** ([`NearOffsets`]): whether
    /// a receiver tells its neighbouring offsets apart where their faces are equal, as a restated result needs (in
    /// `<<E=C>>D` the result C is written again as D, and D's `k`-th site reads C's `k`-th at offset `|C| + 2`). A reading
    /// only: nothing in the law reads it.
    pub fn near_offsets(&self, region: &Region, sites: &[usize]) -> Result<Vec<NearOffsets>> {
        let pass = self.pass(region, true)?;
        let n = region.classes.len();
        if sites.iter().any(|&i| i >= n) {
            return refuse("a near-field site outside its region");
        }
        let heads = self.declaration.heads;
        Ok(sites
            .iter()
            .map(|&i| {
                let mut out = NearOffsets { logits: pass.logits[i].clone(), ..NearOffsets::default() };
                for cell in &pass.ticks {
                    for h in 0..heads {
                        let (mut before, mut after) = ([0u64; NEAR - 1], [0u64; NEAR - 1]);
                        for src in &cell.rows[h * n + i] {
                            let j = src.j as usize;
                            if j < i && i - j < NEAR {
                                before[i - j - 1] = src.p;
                            } else if j > i && j - i < NEAR {
                                after[j - i - 1] = src.p;
                            }
                        }
                        out.before.push(before);
                        out.after.push(after);
                    }
                }
                out
            })
            .collect())
    }

    /// The field as text: its head line, then its material on one line.
    /// The field as text: its declaration and its material, each on one line; a tower adds a line `scale P split`, the
    /// packets' field's two lines and the glue's one.
    pub fn to_text(&self) -> String {
        let theta: Vec<String> = self.theta.iter().map(i32::to_string).collect();
        let mut out = format!("{}\n{}\n", self.declaration.to_text(), theta.join(" "));
        if let Some(s) = &self.scale {
            let glue: Vec<String> = s.glue.iter().map(i32::to_string).collect();
            out.push_str(&format!("scale {} {}\n{}{}\n", s.period, s.split, s.coarse.to_text(), glue.join(" ")));
        }
        out
    }

    pub fn from_text(text: &str) -> Result<Self> {
        Self::from_lines(&mut text.lines().peekable())
    }

    /// A field read from its text's lines ([`Field::to_text`]), the lines after it left unread.
    pub fn from_lines<'a>(lines: &mut std::iter::Peekable<impl Iterator<Item = &'a str>>) -> Result<Self> {
        let d = FieldDeclaration::from_text(lines.next().unwrap_or(""))?;
        let theta = read_numbers::<i32>(lines.next())?;
        if theta.len() != FieldLayout::new(&d).len {
            return refuse("a field's material that is not its declaration's length");
        }
        let mut field = Self::with_theta(d, theta);
        if let Some(head) = lines.peek().copied().filter(|l| l.starts_with("scale ")) {
            lines.next();
            let words: Vec<usize> = head.split(' ').skip(1).map(|w| w.parse::<usize>().map_err(|_| TowerError::Refused("a scale's line that is not two counts"))).collect::<Result<_>>()?;
            let [period, split] = words[..] else { return refuse("a scale's line that is not two counts") };
            let coarse = Self::from_lines(lines)?;
            let glue = read_numbers::<i32>(lines.next())?;
            let (.., len) = scale::glue_len(period, field.declaration.width, coarse.declaration.width);
            if glue.len() != len || split == 0 || split >= field.declaration.ticks {
                return refuse("a scale's glue that is not its declaration's length, or a split outside the ticks");
            }
            field.scale = Some(Box::new(Scale { period, split, coarse, glue }));
        }
        Ok(field)
    }
}

/// [`Field::landmarks`] from each site's still heads' weight rows at the last tick (each row's met
/// sources with their weights, and its mass): `Σ_h e_ij 2^16 / mass_i` at each source before
/// `question`, the `count` heaviest (the earlier source on a tie). A realization reads the rows; the
/// ranking is one law.
pub fn landmarks_of(rows: &[Vec<(Vec<(u32, u64)>, u64)>], question: usize, count: usize) -> Vec<Vec<(usize, u64)>> {
    rows.iter()
        .map(|heads| {
            let mut weight = vec![0u64; question];
            for (row, mass) in heads {
                for &(j, e) in row.iter().filter(|&&(j, _)| (j as usize) < question) {
                    weight[j as usize] += (((e as u128) << STATE_BITS) / *mass as u128) as u64;
                }
            }
            let mut ranked: Vec<(usize, u64)> = weight.into_iter().enumerate().filter(|&(_, w)| w > 0).collect();
            ranked.sort_by_key(|&(j, w)| (std::cmp::Reverse(w), j));
            ranked.truncate(count);
            ranked
        })
        .collect()
}

/// [definition; agent-inferred, November 3, §16.34] **A site's strand mate for pair contact `e`**: the site before it at an
/// even `e`, the one after at an odd, `None` past the region's ends. The parity survives growth by copies (a contact's copy
/// stands at `c · f/2 + e`, `f/2` even), so a grown merge reads the old one exactly.
pub fn strand_mate(t: usize, e: usize, sites: usize) -> Option<usize> {
    if e % 2 == 0 {
        t.checked_sub(1)
    } else {
        (t + 1 < sites).then_some(t + 1)
    }
}

/// [definition; agent-inferred, November 4, §16.40] **The chart by lanes** (the tower record, D2): a site's face of `L`
/// lanes is read lane by lane, each lane's `W = D/L` coordinates a ratio to its own power, `r̂_ℓ = r_ℓ / ‖r_ℓ‖_rms`, its
/// scale `‖r_ℓ‖_rms` pushed after the lanes before it; one lane is the chart over the whole width. Why lanes: a lane
/// founded beside trained ones with every read from it at zero ([`Field::laned`]) leaves each other lane's chart, and so
/// every face, exactly as it was, which a chart over the whole width would not (the new coordinates would join the power
/// every coordinate is divided by), and the reads from it carry a covector at once.
fn lane_chart(xt: &[i64], lanes: usize, read: &mut Vec<i32>, scale: &mut Vec<i128>) -> Result<()> {
    for lane in xt.chunks_exact(xt.len() / lanes) {
        let (r, s) = ratio_to_power(lane)?;
        read.extend_from_slice(&r);
        scale.push(s);
    }
    Ok(())
}

/// The adjoint of [`lane_chart`] at one site: each lane's covector through its own chart ([`ratio_adjoint`]).
fn lane_adjoint(read: &[i32], scales: &[i128], cov: &[i64]) -> Result<Vec<i64>> {
    let w = read.len() / scales.len();
    let mut out = Vec::with_capacity(read.len());
    for (k, &s) in scales.iter().enumerate() {
        out.extend(ratio_adjoint(&read[k * w..(k + 1) * w], s, &cov[k * w..(k + 1) * w])?);
    }
    Ok(out)
}

/// The founding's scale of the charts and pair drives at width `D`, `√(3/D)` as a ratio of square
/// roots on `2^(−16)`.
fn chart_scale(width: usize) -> (u128, u128) {
    ((3u128 << 32).isqrt(), ((width as u128) << 32).isqrt())
}

impl Field {
    /// The key draws a growth by `factor` reads, four bytes a draw: `f − 1` a part of each row
    /// copy's entry of every family the founding opens away from zero (the charts and the pair
    /// drives).
    pub fn growth_draws(&self, factor: usize) -> usize {
        self.declaration.growth_draws(factor)
    }

    /// [definition; agent-inferred, November 1; November 3, §16.29] **The field widened by `factor`**, by the tower's
    /// growth law (`hnn::tower::growth`): every face coordinate gets `f` equal copies (the encoding and every face bias
    /// repeated), every contact repeated, and every matrix entry that reads the face split over its `f` column copies
    /// into parts that sum to it; a matrix that writes the face (the current's return, the moment's chart, the pair's
    /// return) has its rows repeated over the face copies, the current's and the moment's columns whole. The heads
    /// are kept: their charts' rows, biases, moments, clocks and temperatures are the old ones. A part's zero-sum
    /// difference is the grown founding's draw at its scale (`√(3/fD)` for the charts and pair drives, read from
    /// `keys` four bytes a draw); the families founded at zero (the returns and the readout) split evenly. Every sum
    /// the forward forms is then the old sum, so the grown field reads the old faces exactly, and the copies part
    /// under learning.
    ///
    /// Returns the grown field and, for each grown entry, the old entry it carries and whether its
    /// covector is divided among the copies (every family but the readout's).
    pub fn grown(&self, factor: usize, keys: &[u8]) -> Result<(Self, Vec<(usize, bool)>)> {
        if factor < 2 {
            return refuse("a growth makes at least two copies");
        }
        if self.scale.is_some() {
            return refuse("a tower grows by its levels' lanes, not by copies (the tower record, D2)");
        }
        let old = self.declaration;
        let d = old.grown(factor)?;
        let layout = FieldLayout::new(&d);
        let (ol, f) = (&self.layout, factor);
        let (dw, m, fc, a) = (old.width, old.complex(), old.contacts, old.alphabet);
        let dw2 = d.width;
        let mut new = vec![0i32; layout.len];
        let mut from = vec![(0usize, true); layout.len];
        let mut cursor = 0usize;
        let mut draw = |scale: Option<(u128, u128)>| -> Result<i128> {
            let Some((num, den)) = scale else { return Ok(0) };
            let word = keys.get(cursor..cursor + 4).ok_or(TowerError::Refused("fewer key bytes than the growth draws"))?;
            cursor += 4;
            let k = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i128;
            Ok((k * ((num << MATERIAL_BITS) / den) as i128) >> 31)
        };
        // A matrix of `rows × cols` (old), its rows mapped by `row_of(b, r)` over `row_copies`
        // copies and each column's `f` parts placed at `col_of(c, j)` in a row of `new_cols`.
        let mut split = |old_at: usize, new_at: usize, rows: usize, cols: usize, row_copies: usize, row_of: &dyn Fn(usize, usize) -> usize, new_cols: usize, col_of: &dyn Fn(usize, usize) -> usize, scale: Option<(u128, u128)>, divided: bool| -> Result<()> {
            for b in 0..row_copies {
                for r in 0..rows {
                    let nr = row_of(b, r);
                    for j in 0..cols {
                        let v = self.theta[old_at + r * cols + j] as i128;
                        let (q, rem) = (v.div_euclid(f as i128), v.rem_euclid(f as i128));
                        let mut spent = 0i128;
                        for c in 0..f {
                            let delta = if c + 1 < f { draw(scale)? } else { -spent };
                            spent += delta;
                            let at = new_at + nr * new_cols + col_of(c, j);
                            new[at] = fit32(q + i128::from((c as i128) < rem) + delta, "a grown part outgrew its 32-bit carrier")?;
                            from[at] = (old_at + r * cols + j, divided);
                        }
                    }
                }
            }
            Ok(())
        };
        let scale = Some(chart_scale(dw2));
        // Index maps: a face coordinate's copy `c` at `cD + j`; a contact's at `bf + e`.
        let face = |c: usize, j: usize| c * dw + j;
        // A contact is a complex pair (`e`, `f/2 + e`, §15.1): copy `c` of its real part at `c f/2 + e`,
        // of its imaginary part at `f'/2 + c f/2 + e`, so every copy keeps its pair.
        let contact = |c: usize, e: usize| if e < fc / 2 { c * (fc / 2) + e } else { f * fc / 2 + c * (fc / 2) + e - fc / 2 };
        let kept = |_: usize, r: usize| r;
        // [§16.29] A head's chart reads every face copy (its row kept, each entry split over its column's copies), and the
        // current returns whole to every face copy (each row repeated, below): every copy of a coordinate stays its source.
        split(ol.q, layout.q, 2 * m, dw, 1, &kept, dw2, &face, scale, false)?;
        split(ol.v, layout.v, 2 * m, dw, 1, &kept, dw2, &face, scale, false)?;
        split(ol.probe, layout.probe, 2 * m, dw, 1, &kept, dw2, &face, scale, false)?;
        split(ol.a, layout.a, fc, dw, f, &contact, dw2, &face, scale, true)?;
        split(ol.b, layout.b, fc, dw, f, &contact, dw2, &face, scale, true)?;
        split(ol.w, layout.w, dw, fc, f, &face, f * fc, &contact, None, true)?;
        // The current's return and the moment's chart into the face (§16.22) write the face: each row repeated over the
        // face copies, its columns (the heads' modes, kept) whole, so the grown current and opening are the old ones on
        // every copy; a copy's covector arrives divided, as the face's does.
        for (old_at, new_at) in [(ol.out, layout.out), (ol.moment_face, layout.moment_face)] {
            for b in 0..f {
                for r in 0..dw {
                    for k in 0..2 * m {
                        let at = new_at + face(b, r) * 2 * m + k;
                        new[at] = self.theta[old_at + r * 2 * m + k];
                        from[at] = (old_at + r * 2 * m + k, true);
                    }
                }
            }
        }
        // [§16.26] The readout's lift reads every face copy and writes the first copy of each coordinate only, each entry split
        // evenly over its column's copies, its bias the first copy's; the encoding's rows are repeated over the copies, so the
        // grown face `⟨E′(a), y′⟩ = ⟨E(a), y⟩` exactly, and the copies part under learning.
        for j in 0..dw {
            for k in 0..dw {
                let old_at = ol.read + j * dw + k;
                let v = self.theta[old_at] as i128;
                let (q, rem) = (v.div_euclid(f as i128), v.rem_euclid(f as i128));
                for b in 0..f {
                    for c in 0..f {
                        let at = layout.read + face(b, j) * dw2 + face(c, k);
                        new[at] = if b == 0 { fit32(q + i128::from((c as i128) < rem), "a grown part outgrew its 32-bit carrier")? } else { 0 };
                        from[at] = (old_at, true);
                    }
                }
            }
            for b in 0..f {
                let at = layout.lift_bias + face(b, j);
                new[at] = if b == 0 { self.theta[ol.lift_bias + j] } else { 0 };
                from[at] = (ol.lift_bias + j, true);
            }
        }
        // The heads' own families (§16.29: kept, no face coordinate among them): the paces (§16.16), the moment encodings
        // (§15.1), the temperatures (§15.10) and the charts' biases, each its source's, its covector its source's whole.
        for (old_at, new_at, len) in [
            (ol.pace, layout.pace, layout.moment_face - layout.pace),
            (ol.moment_before, layout.moment_before, layout.moment_after - layout.moment_before),
            (ol.moment_after, layout.moment_after, layout.temper - layout.moment_after),
            (ol.temper, layout.temper, 2 * old.heads),
            (ol.q_bias, layout.q_bias, 2 * m),
            (ol.v_bias, layout.v_bias, 2 * m),
            (ol.probe_bias, layout.probe_bias, 2 * m),
        ] {
            for i in 0..len {
                new[new_at + i] = self.theta[old_at + i];
                from[new_at + i] = (old_at + i, false);
            }
        }
        // Vector families: each entry's copies.
        let mut repeat = |old_at: usize, new_at: usize, len: usize, copies: usize, index: &dyn Fn(usize, usize) -> usize, divided: bool| {
            for c in 0..copies {
                for i in 0..len {
                    new[new_at + index(c, i)] = self.theta[old_at + i];
                    from[new_at + index(c, i)] = (old_at + i, divided);
                }
            }
        };
        for row in 0..=a {
            repeat(ol.enc + row * dw, layout.enc + row * dw2, dw, f, &face, true);
            repeat(ol.before + row * dw, layout.before + row * dw2, dw, f, &face, true);
            repeat(ol.after + row * dw, layout.after + row * dw2, dw, f, &face, true);
        }
        repeat(ol.out_bias, layout.out_bias, dw, f, &face, true);
        repeat(ol.a_bias, layout.a_bias, fc, f, &contact, true);
        repeat(ol.b_bias, layout.b_bias, fc, f, &contact, true);
        repeat(ol.w_bias, layout.w_bias, dw, f, &face, true);
        repeat(ol.read_bias, layout.read_bias, a, 1, &kept, false);
        repeat(ol.moment_face_bias, layout.moment_face_bias, dw, f, &face, true);
        Ok((Self::with_theta(d, new), from))
    }

    /// [definition; agent-inferred, November 4, §16.40] **The field with one more lane** (the tower record, D2): a lane of
    /// `W` coordinates founded after the others as a founding founds them, the encoding's and the strand contacts' rows of
    /// every class uniform on `±1` (the unresolved row at zero) and the moment's chart into the lane uniform on `±√(3/2T)`
    /// at the turned modes, read from `keys` four bytes a draw in that order; every read from the lane (the key, value and
    /// probe charts' columns, both pair drives' columns, the readout's lift, its rows and its columns) and every other
    /// write into it (the current's return, the pair contact's return, the biases) at zero. Every old entry keeps its row
    /// and column in its family. Each old lane's chart is its own ([`lane_chart`]), nothing reads the new lane and nothing
    /// it is written by reaches a read, so the laned field reads every face exactly as the old one did; and every read
    /// from the lane has a covector from the first section on (the lane's chart times the read's covector), so the lane
    /// opens with no copy's symmetry to break (§16.37).
    ///
    /// Returns the laned field and, for each entry, the old entry it carries (`None` for the lane's own).
    pub fn laned(&self, keys: &[u8]) -> Result<(Self, Vec<Option<usize>>)> {
        if self.scale.is_some() {
            return refuse("a tower's levels grow their lanes level by level, not through the fine field alone");
        }
        let old = self.declaration;
        let d = old.laned()?;
        let layout = FieldLayout::new(&d);
        let ol = &self.layout;
        let (dw, dw2, m2, fc, a) = (old.width, d.width, 2 * old.complex(), old.contacts, old.alphabet);
        let mut new = vec![0i32; layout.len];
        let mut from: Vec<Option<usize>> = vec![None; layout.len];
        // A block of `rows × cols` (old) placed at the same rows and columns of a block `new_cols` wide.
        let mut place = |old_at: usize, new_at: usize, rows: usize, cols: usize, new_cols: usize| {
            for r in 0..rows {
                for c in 0..cols {
                    new[new_at + r * new_cols + c] = self.theta[old_at + r * cols + c];
                    from[new_at + r * new_cols + c] = Some(old_at + r * cols + c);
                }
            }
        };
        // The reads of the face (its coordinates the columns) and the encodings (a class a row).
        for (o, n, rows) in [(ol.q, layout.q, m2), (ol.v, layout.v, m2), (ol.probe, layout.probe, m2), (ol.a, layout.a, fc), (ol.b, layout.b, fc), (ol.enc, layout.enc, a + 1), (ol.before, layout.before, a + 1), (ol.after, layout.after, a + 1)] {
            place(o, n, rows, dw, dw2);
        }
        // The writes into the face (its coordinates the rows), and the face's own vectors.
        for (o, n, cols) in [(ol.out, layout.out, m2), (ol.w, layout.w, fc), (ol.moment_face, layout.moment_face, m2)] {
            place(o, n, dw, cols, cols);
        }
        for (o, n) in [(ol.out_bias, layout.out_bias), (ol.w_bias, layout.w_bias), (ol.moment_face_bias, layout.moment_face_bias), (ol.lift_bias, layout.lift_bias)] {
            place(o, n, 1, dw, dw);
        }
        place(ol.read, layout.read, dw, dw, dw2);
        // The families with no face coordinate: as they were.
        for (o, n, len) in [
            (ol.q_bias, layout.q_bias, m2),
            (ol.v_bias, layout.v_bias, m2),
            (ol.probe_bias, layout.probe_bias, m2),
            (ol.a_bias, layout.a_bias, fc),
            (ol.b_bias, layout.b_bias, fc),
            (ol.read_bias, layout.read_bias, a),
            (ol.moment_before, layout.moment_before, ol.moment_after - ol.moment_before),
            (ol.moment_after, layout.moment_after, ol.temper - ol.moment_after),
            (ol.temper, layout.temper, 2 * old.heads),
            (ol.pace, layout.pace, ol.moment_face - ol.pace),
        ] {
            place(o, n, 1, len, len);
        }
        // The lane's founding draws.
        let mut cursor = 0usize;
        let mut draw = |num: u128, den: u128, bits: u32| -> Result<i32> {
            let word = keys.get(cursor..cursor + 4).ok_or(TowerError::Refused("fewer key bytes than the lane's founding reads"))?;
            cursor += 4;
            let k = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i128;
            fit32((k * ((num << bits) / den) as i128) >> 31, "a lane's founded value outgrew its 32-bit carrier")
        };
        for start in [layout.enc, layout.before, layout.after] {
            for row in 0..a {
                for j in dw..dw2 {
                    new[start + row * dw2 + j] = draw(1, 1, FACE_BITS)?;
                }
            }
        }
        let tm = old.moment_modes();
        if tm > 0 {
            let (three_m, dd_m) = chart_scale(2 * tm);
            let carries: Vec<bool> = (0..m2).map(|k| old.carries_moment((k % old.complex()) / old.modes)).collect();
            for o in dw..dw2 {
                for (k, &on) in carries.iter().enumerate() {
                    if on {
                        new[layout.moment_face + o * m2 + k] = draw(three_m, dd_m, MATERIAL_BITS)?;
                    }
                }
            }
        }
        debug_assert_eq!(cursor, 4 * old.lane_draws());
        Ok((Self::with_theta(d, new), from))
    }
}

fn read_numbers<T: std::str::FromStr>(line: Option<&str>) -> Result<Vec<T>> {
    let line = line.ok_or(TowerError::Refused("a field's text ended before its material"))?;
    if line.is_empty() {
        return Ok(Vec::new());
    }
    line.split(' ').map(|w| w.parse::<T>().map_err(|_| TowerError::Refused("a field's material that is not a number"))).collect()
}

/// [measurement; agent-inferred, November 4] **A tick's read of a region**: each site's chart `r̂` on `2^(−16)` and its scales (the
/// faces' power, one a lane) at the opening of each tick, the field's state as its ticks meet it (a reading of expansion and
/// volume); and (§16.40) the pair contact's chart and scales, the state after the tick's current and before its pair contact.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TickRead {
    pub read: Vec<i32>,
    pub scale: Vec<i128>,
    pub pair_read: Vec<i32>,
    pub pair_scale: Vec<i128>,
}

impl Field {
    /// Each tick's read of `region` ([`TickRead`]), in tick order.
    pub fn tick_reads(&self, region: &Region) -> Result<Vec<TickRead>> {
        let pass = self.pass(region, true)?;
        Ok(pass.ticks.iter().map(|c| TickRead { read: c.read.clone(), scale: c.scale.clone(), pair_read: c.read2.clone(), pair_scale: c.scale2.clone() }).collect())
    }
}

/// [definition; agent-inferred, November 1] **A realization of the field's read and return**: a
/// region's faces and the covector over a section's regions, bit for bit the host's
/// ([`HostField`]). The card's realization is one such; a realization that cannot read a region
/// refuses, never substitutes.
pub trait FieldRealization {
    fn read_and_return(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)>;
    fn read_faces(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>>;
    /// Each unresolved site's readout logits on `2^(−16)` bits ([`Field::logits`]), the release's read.
    fn read_logits(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<FieldRead>>;
    /// The landmarks of `sites` in `region` ([`Field::landmarks`]), a reading of its last tick.
    fn read_landmarks(&mut self, field: &Field, region: &Region, question: usize, sites: &[usize], count: usize) -> Result<Vec<Vec<(usize, u64)>>>;
    /// The site pairs the realization's contact has met so far, where it counts them.
    fn met_pairs(&self) -> Option<u128> {
        None
    }
    /// A held read's rows by where their mass lies, summed over `regions` ([`Field::held_rows_all`]; each region's
    /// answer start in `questions`), a reading for the receipts.
    fn read_row_shares(&mut self, _field: &Field, _regions: &[Region], _questions: &[usize]) -> Result<Vec<HeldRows>> {
        refuse("a realization that cannot read its rows' shares")
    }
    /// The contact covector by where its pairs lie over `regions` ([`Field::covector_shares`]), a reading.
    fn read_covector_shares(&mut self, _field: &Field, _regions: &[Region]) -> Result<Vec<[u128; 2]>> {
        refuse("a realization that cannot read its covector's shares")
    }
    /// The held answer rows' currents by where they come from, region by region ([`Field::row_currents`]; each region's
    /// answer start in `questions`), a reading.
    fn read_row_currents(&mut self, _field: &Field, _regions: &[Region], _questions: &[usize], _returning: bool) -> Result<Vec<Vec<RowCurrent>>> {
        refuse("a realization that cannot read its rows' currents")
    }
    /// Each region's tick reads ([`Field::tick_reads`]), a reading.
    fn read_ticks(&mut self, _field: &Field, _regions: &[Region]) -> Result<Vec<Vec<TickRead>>> {
        refuse("a realization that cannot read its ticks")
    }
    /// Each of `sites`' near field by offset in `region` ([`Field::near_offsets`]), a reading.
    fn read_near_offsets(&mut self, _field: &Field, _region: &Region, _sites: &[usize]) -> Result<Vec<NearOffsets>> {
        refuse("a realization that cannot read its near fields")
    }
    /// Each of `sites`' clocks by tick in `region` ([`Field::blank_clocks`]), a reading.
    /// [measurement; the unified-theory reading of November 7, 01:37] An energy field's squares at one base
    /// ([`Field::energy_square_corners`] for each `(truth, (i, j))`), read on the host in parallel unless the realization
    /// reads them itself.
    fn read_energy_squares(&mut self, field: &Field, squares: &[(&[usize], (usize, usize))], void: usize, eps: u32) -> Result<Vec<Option<EnergySquare>>> {
        squares.par_iter().map(|&(truth, ij)| field.energy_square_corners(truth, ij, void, eps)).collect()
    }
    /// [measurement; the unified-theory readings of November 7, 03:22 and 04:20] An energy field's central squares at one base
    /// ([`Field::energy_central_square`] for each `(truth, (i, j))` at each step), read on the host in parallel unless the
    /// realization reads them itself.
    #[allow(clippy::type_complexity)]
    fn read_energy_central_squares(&mut self, field: &Field, squares: &[(&[usize], (usize, usize))], void: usize, steps: &[u32]) -> Result<Vec<Option<Vec<(i128, i128)>>>> {
        squares.par_iter().map(|&(truth, ij)| field.energy_central_square(truth, ij, void, steps)).collect()
    }
    /// [measurement; November 7] An energy field's faces and its energy `G` at the last state, region by region
    /// ([`Field::energy_faces_read`]), on the host in parallel unless the realization reads them itself.
    #[allow(clippy::type_complexity)]
    fn read_energy_faces(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)> {
        let reads: Vec<(Vec<Option<TowerFace>>, i128)> = regions.par_iter().map(|r| field.energy_faces_read(r)).collect::<Result<_>>()?;
        Ok(reads.into_iter().unzip())
    }
    /// [measurement; the unified-theory reading of November 7, 04:05] Each resolved region's energy `G` at its own certified
    /// halvings ([`Field::energy_g`]), on the host in parallel unless the realization reads them itself.
    fn read_energies(&mut self, field: &Field, regions: &[&[usize]]) -> Result<Vec<i128>> {
        regions.par_iter().map(|c| field.energy_g(c)).collect()
    }
    /// [definition; agent-inferred, November 7] An energy field's material covector `∂G/∂θ` and `G` a region
    /// ([`Field::energy_material`]), read on the host in parallel unless the realization reads them itself.
    fn read_energy_material(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<(Vec<i128>, i128)>> {
        regions.par_iter().map(|r| field.energy_material(r)).collect()
    }
    fn read_blank_clocks(&mut self, _field: &Field, _region: &Region, _sites: &[usize]) -> Result<Vec<BlankClocks>> {
        refuse("a realization that cannot read its blanks' clocks")
    }
}

/// The host's realization: the regions on the host's cores, each region's forward and reverse on
/// one core.
#[derive(Clone, Copy, Debug, Default)]
pub struct HostField;

impl FieldRealization for HostField {
    fn read_and_return(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)> {
        field.read_and_return(regions)
    }
    fn read_faces(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>> {
        field.read_faces(regions)
    }
    fn read_logits(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<FieldRead>> {
        field.read_logits(regions)
    }
    fn read_landmarks(&mut self, field: &Field, region: &Region, question: usize, sites: &[usize], count: usize) -> Result<Vec<Vec<(usize, u64)>>> {
        field.landmarks(region, question, sites, count)
    }
    fn read_row_shares(&mut self, field: &Field, regions: &[Region], questions: &[usize]) -> Result<Vec<HeldRows>> {
        field.held_rows_all(regions, questions)
    }
    fn read_covector_shares(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<[u128; 2]>> {
        field.covector_shares(regions)
    }
    fn read_row_currents(&mut self, field: &Field, regions: &[Region], questions: &[usize], returning: bool) -> Result<Vec<Vec<RowCurrent>>> {
        regions.iter().zip(questions).map(|(r, &q)| field.row_currents(r, q, returning)).collect()
    }
    fn read_ticks(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<Vec<TickRead>>> {
        regions.par_iter().map(|r| field.tick_reads(r)).collect()
    }

    fn read_near_offsets(&mut self, field: &Field, region: &Region, sites: &[usize]) -> Result<Vec<NearOffsets>> {
        field.near_offsets(region, sites)
    }

    fn read_blank_clocks(&mut self, field: &Field, region: &Region, sites: &[usize]) -> Result<Vec<BlankClocks>> {
        field.blank_clocks(region, sites)
    }
}

/// [definition; Brandon, November 7 19:22: "you can beat the clock speed of the CPU with more threads if the mathematics holds
/// for the orders you integrate with"] **The card and the host's lanes as one surface**: an energy read's regions are
/// partitioned between the host's cores (the first `k`, in parallel on the host's pool) and the card (the rest), both at
/// once, and joined in region order. Each region's read is its own and bit for bit the same on either side (the card's
/// parity with [`HostField`]), so the joined read is the card's alone at any partition. The host's share is the
/// partition that ends both sides together, read from the last split read's measured times: with `t_h` and `t_c` the
/// times a region on each side, `k/n = t_c/(t_h + t_c)`, met halfway from the share before. Every other read is the card's.
pub struct LanesField<'a> {
    pub card: &'a mut dyn FieldRealization,
    /// The host's share of a read's regions on `2^(−16)`.
    share: u64,
    /// Regions read and microseconds spent on each side, and the reads split.
    pub host_regions: u64,
    pub card_regions: u64,
    pub host_us: u128,
    pub card_us: u128,
    pub wall_us: u128,
    pub splits: u64,
}

impl<'a> LanesField<'a> {
    const ONE: u64 = 1 << 16;
    /// The opening share, a sixteenth: the host is read before its share is known.
    pub fn new(card: &'a mut dyn FieldRealization) -> Self {
        Self { card, share: Self::ONE >> 4, host_regions: 0, card_regions: 0, host_us: 0, card_us: 0, wall_us: 0, splits: 0 }
    }

    /// The host's share now, on `2^(−16)`.
    pub fn share(&self) -> u64 {
        self.share
    }

    /// `n` regions split at the current share: the host reads `[0, k)` on a scoped thread over the pool while the card
    /// reads `[k, n)` here; the share is then re-read from the two sides' times.
    fn split<T: Send>(&mut self, n: usize, host: impl FnOnce(std::ops::Range<usize>) -> Result<Vec<T>> + Send, card: impl FnOnce(&mut dyn FieldRealization, std::ops::Range<usize>) -> Result<Vec<T>>) -> Result<Vec<T>> {
        let k = if n < 2 { 0 } else { ((n as u64 * self.share) >> 16).clamp(1, n as u64 - 1) as usize };
        if k == 0 {
            return card(&mut *self.card, 0..n);
        }
        let wall = std::time::Instant::now();
        let (host_read, card_read) = std::thread::scope(|scope| {
            let lane = scope.spawn(move || {
                let t = std::time::Instant::now();
                host(0..k).map(|v| (v, t.elapsed().as_micros()))
            });
            let t = std::time::Instant::now();
            let c = card(&mut *self.card, k..n).map(|v| (v, t.elapsed().as_micros()));
            (lane.join().unwrap_or_else(|_| refuse("a host lane panicked")), c)
        });
        let ((mut out, th), (rest, tc)) = (host_read?, card_read?);
        out.extend(rest);
        self.wall_us += wall.elapsed().as_micros();
        (self.host_regions, self.card_regions, self.host_us, self.card_us, self.splits) = (self.host_regions + k as u64, self.card_regions + (n - k) as u64, self.host_us + th, self.card_us + tc, self.splits + 1);
        // Times a region on 2^(-16) microseconds, and the share that would end both together.
        let (per_h, per_c) = ((th.max(1) << 16) / k as u128, (tc.max(1) << 16) / (n - k) as u128);
        let even = (per_c << 16) / (per_h + per_c);
        self.share = ((self.share as u128 + even) / 2).clamp(1, Self::ONE as u128 - 1) as u64;
        Ok(out)
    }
}

impl FieldRealization for LanesField<'_> {
    fn read_and_return(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)> {
        self.card.read_and_return(field, regions)
    }
    fn read_faces(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>> {
        self.card.read_faces(field, regions)
    }
    fn read_logits(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<FieldRead>> {
        self.card.read_logits(field, regions)
    }
    fn read_landmarks(&mut self, field: &Field, region: &Region, question: usize, sites: &[usize], count: usize) -> Result<Vec<Vec<(usize, u64)>>> {
        self.card.read_landmarks(field, region, question, sites, count)
    }
    fn met_pairs(&self) -> Option<u128> {
        self.card.met_pairs()
    }
    fn read_row_shares(&mut self, field: &Field, regions: &[Region], questions: &[usize]) -> Result<Vec<HeldRows>> {
        self.card.read_row_shares(field, regions, questions)
    }
    fn read_covector_shares(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<[u128; 2]>> {
        self.card.read_covector_shares(field, regions)
    }
    fn read_row_currents(&mut self, field: &Field, regions: &[Region], questions: &[usize], returning: bool) -> Result<Vec<Vec<RowCurrent>>> {
        self.card.read_row_currents(field, regions, questions, returning)
    }
    fn read_ticks(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<Vec<TickRead>>> {
        self.card.read_ticks(field, regions)
    }
    fn read_near_offsets(&mut self, field: &Field, region: &Region, sites: &[usize]) -> Result<Vec<NearOffsets>> {
        self.card.read_near_offsets(field, region, sites)
    }
    fn read_blank_clocks(&mut self, field: &Field, region: &Region, sites: &[usize]) -> Result<Vec<BlankClocks>> {
        self.card.read_blank_clocks(field, region, sites)
    }
    fn read_energy_squares(&mut self, field: &Field, squares: &[(&[usize], (usize, usize))], void: usize, eps: u32) -> Result<Vec<Option<EnergySquare>>> {
        self.card.read_energy_squares(field, squares, void, eps)
    }
    #[allow(clippy::type_complexity)]
    fn read_energy_central_squares(&mut self, field: &Field, squares: &[(&[usize], (usize, usize))], void: usize, steps: &[u32]) -> Result<Vec<Option<Vec<(i128, i128)>>>> {
        self.card.read_energy_central_squares(field, squares, void, steps)
    }
    #[allow(clippy::type_complexity)]
    fn read_energy_faces(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)> {
        let joined = self.split(
            regions.len(),
            |r| regions[r].par_iter().map(|x| field.energy_faces_read(x)).collect::<Result<Vec<_>>>(),
            |card, r| card.read_energy_faces(field, &regions[r]).map(|(f, g)| f.into_iter().zip(g).collect()),
        )?;
        Ok(joined.into_iter().unzip())
    }
    fn read_energies(&mut self, field: &Field, regions: &[&[usize]]) -> Result<Vec<i128>> {
        self.split(regions.len(), |r| regions[r].par_iter().map(|c| field.energy_g(c)).collect(), |card, r| card.read_energies(field, &regions[r]))
    }
    fn read_energy_material(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<(Vec<i128>, i128)>> {
        self.split(regions.len(), |r| regions[r].par_iter().map(|x| field.energy_material(x)).collect(), |card, r| card.read_energy_material(field, &regions[r]))
    }
}

/// A place's conditional `p(v) ∝ 2^(−G_v/T)` on `2^(−24)` from its letters' energies, each weight through the exponential's
/// navigator and released to zero below `2^(−23)` (the conditional section's own shares).
fn conditional_shares(gs: &[i128], inverse: i128, fine: &Exponential) -> Result<Vec<i128>> {
    const OVER: &str = "a conditional covector past its 128-bit carrier";
    let lo = gs.iter().copied().min().unwrap_or(0);
    let w: Vec<i128> = gs
        .iter()
        .map(|&gv| {
            let l = release((lo - gv).checked_mul(inverse).ok_or(TowerError::Refused(OVER))?, MATERIAL_BITS);
            let ell = l >> (ENERGY_BITS - MATERIAL_BITS);
            if ell >= 0 {
                Ok(1i128 << MATERIAL_BITS)
            } else if ell <= -((MATERIAL_BITS as i128 - 1) << MATERIAL_BITS) {
                Ok(0)
            } else {
                temperature_of(ell as i32, fine)
            }
        })
        .collect::<Result<_>>()?;
    let z: i128 = w.iter().sum();
    Ok(w.iter().map(|&x| div_nearest(x << MATERIAL_BITS, z.max(1))).collect())
}

/// [agent-inferred, November 1] A held step read on regions it was not fit on
/// ([`FieldLearner::read_step_on`]): its change to those regions' code (the stepped material's
/// code less the material's before the step, on `2^(−20)` bits), the further halvings of the last
/// size read ([`FieldLearner::next_scale`]: the step stands at them unless refused), and whether
/// it refused the step.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FieldNext {
    pub change: i64,
    pub halvings: u32,
    pub refused: bool,
}

/// A section's receipt: its unresolved sites, its code before and after (on `2^(−20)` bits), the
/// halvings the certificate took, whether a step was deposited, and the read of the step the
/// section before deposited on this section's regions.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FieldReceipt {
    /// The sites the codes are of: each region's domain where it read an open site (§16.23).
    pub sites: usize,
    pub code_before: i64,
    /// The section's code reread under its step; none since the step fluxes (§16.47, Brandon, November 5 17:32).
    pub code_after: Option<i64>,
    pub halvings: u32,
    pub deposited: bool,
    pub next: Option<FieldNext>,
    /// [measurement; §16.41] The step's first-order change of the section's code at its full size, `Σ_i g_i Δθ_i` on the
    /// codes' grain ([`predicted_change`]; `None` past its carrier), and the change a reread measured there (none since
    /// the step fluxes): the section's own parabola `e(μ) = aμ + bμ²` with `a` the first and `a + b` the second.
    pub predicted: Option<i64>,
    pub change: Option<i64>,
    /// [measurement; agent-inferred, November 4, §16.41] **The step before, priced on this section**: `Σ_i g_i Δθ_i` with `g`
    /// this section's covector at the material that stands and `Δθ` the step the section before stood at (its halvings
    /// released), on the codes' grain: the first-order change of this section's code were that step taken once more. Negative
    /// where the step before was short of what this section, which it was not fit on, would take; positive where it went
    /// past. `None` at a learner's first section, after a section that deposited nothing, or past its carrier.
    pub transfer: Option<i64>,
    /// [measurement; agent-inferred, November 6, the unified-theory reading of 08:54] **The external price**, `p_ext =
    /// Σ_i g_i Δθᵉ_i` on the codes' grain, with `Δθᵉ` the step the moments would deposit before this section's covector
    /// moves them (`deposit_step(m_(s−1), v_(s−1))`): a step this section never shaped, priced on it as `transfer` prices the
    /// step before on the next section, with no self-alignment. `transfer − external` of the section before reads the
    /// step's curvature `ΔθᵀHΔθ` from the pass alone, with no reread. `None` past its carrier.
    pub external: Option<i64>,
}

/// [measurement; the unified-theory reading of November 7, 04:05] **An energy section's contrast receipt**
/// ([`FieldLearner::section_contrast`]): its states, how many releases wrote every open place as the truth, the energy's gap
/// `Σ_s (G(truth_s) − G(e′_s))/T` on `2^(−32)` bits (positive where the field holds its own release below the truth),
/// whether a step was deposited, and the step's prices as [`FieldReceipt`]'s, on the codes' grain.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ContrastReceipt {
    pub states: usize,
    pub same: usize,
    pub gap: i128,
    pub deposited: bool,
    pub predicted: Option<i64>,
    pub transfer: Option<i64>,
    pub external: Option<i64>,
}

/// [measurement; the unified-theory reading of November 7, 05:20] **An energy section's kernel receipt**
/// ([`FieldLearner::section_kernel`]): its states, block places and the places whose proposal moved off the truth, the
/// weights `min(1, A)` summed, their squares summed, least and most (on `2^(−24)`) and how many were whole, whether a step
/// was deposited, and the step's prices as [`FieldReceipt`]'s.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct KernelReceipt {
    pub states: usize,
    pub places: usize,
    pub moved: usize,
    pub weight: i128,
    pub weight_square: i128,
    pub least: i128,
    pub most: i128,
    pub whole: usize,
    pub deposited: bool,
    pub predicted: Option<i64>,
    pub transfer: Option<i64>,
    pub external: Option<i64>,
    /// Each state's block places and weight `min(1, A)` on `2^(−24)`, the acceptance by block size's operand.
    pub per_state: Vec<(usize, i128)>,
    /// Each state's `log₂ A` on `2^(−32)` bits (the block's per-place spread `σ² = −2 ln 2 E log₂ A / k` reads from it).
    pub log2_a: Vec<i128>,
    /// The evidence-shrunk Newton step's read, where the learner takes it ([`FieldLearner::newton`]).
    pub newton: Option<NewtonRead>,
    /// [measurement; November 7, lap 7] Each family's part of the transfer and of the predicted change, in the families'
    /// order ([`Field::families_all`]), on the codes' grain (`None` past its carrier): where the step that lowers its own
    /// section raises the next.
    pub by_family: Vec<(Option<i64>, Option<i64>)>,
    /// Each family's length `ρ_f` after the section (on `2^(−24)` bits), where the learner reads them.
    pub rates: Vec<i128>,
    /// [measurement; theory, November 7 19:41] Each state's two relaxations, compared: the states (truths and proposals) whose
    /// `G` read with their faces (places open, carrying their letters whole) is the `G` read with their material (resolved)
    /// in bits, of all, and the largest gap on `2^(−32)`. Agreement means one relaxation a state gives both.
    pub g_agree: (usize, usize),
    pub g_gap: i128,
    /// [measurement; theory, November 7 19:50] The section's deposit before its length, `g = Σ_s w_s D_s/T` on the families'
    /// natural grains (empty where the Newton step deposits): the operand of the sections' coherence.
    pub covector: Vec<i128>,
    /// [measurement; theory, November 7 21:08] The places read and spent in each band `k` of a beat-selected conditional
    /// section ([`FieldLearner::section_conditional_beat`]): the counts of counts of the field's surprise.
    pub bands: Vec<(usize, usize)>,
    /// [measurement; theory, November 7 21:44] Each place's conditional mass outside its face's top 4, 8 and 16 letters (the
    /// face read at the truth, places open carrying their letters whole), on `2^(−24)`: whether a few letters carry the place.
    pub outside: Vec<[i128; 3]>,
    /// [measurement; theory, November 7 22:55] Each letter's count as a truth less its conditional mass, `Σ_places (1[t = a] −
    /// p(a))` on `2^(−24)` (the counts the kernel's rest missed); the places' surprise bands `k = ⌊−log₂(1 − q(t))⌋` from the
    /// face at the truth (held to 16, read whether or not a beat spends them); and `Σ_places KL(p ‖ face)` on `2^(−32)` bits.
    pub letter_counts: Vec<i128>,
    pub surprise_bands: Vec<usize>,
    pub kl_face: i128,
}

/// [measurement; the unified-theory reading of November 7, 05:55] **An evidence-shrunk Newton step's read**
/// ([`FieldLearner::section_kernel`] with [`FieldLearner::newton`]): whether it moved the material, `α` as (numerator,
/// denominator), the shrink `(s² − v, s²)`, the slope `s` along the moments' direction (on `2^(−20)` bits), its variance `v`
/// and the curvature `c` (on `2^(−40)`), and the prices as [`FieldReceipt`]'s.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct NewtonRead {
    pub deposited: bool,
    pub alpha: (i128, i128),
    pub shrink: (i128, i128),
    pub slope: i128,
    pub variance: i128,
    pub curvature: i128,
    pub predicted: Option<i64>,
    pub transfer: Option<i64>,
    pub external: Option<i64>,
}

/// A deposited step held for the next regions' read: the proposed step on each family's grain and
/// the halvings it was certified at. The material before it is the material less nothing: the
/// deposit subtracted `release(step, halvings)` from each entry, so adding it back restores the same bits.
#[derive(Clone, Debug, PartialEq, Eq)]
struct HeldStep {
    step: Vec<i128>,
    halvings: u32,
}

/// Each unresolved site's face read at its class, the faces the certificates compare.
/// [definition; agent-inferred, November 3, §16.24] **A section's compared reading**: each open site's face at its
/// class before its region's port (`(mass, total)`), and the ports' coupling codes summed on `2^(−20)` bits.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Compared {
    pairs: Vec<(u128, u128)>,
    coupled: i64,
    ported: bool,
}

fn compared(faces: &[Vec<Option<TowerFace>>], regions: &[Region]) -> Result<Compared> {
    let mut out = Compared { pairs: Vec::new(), coupled: 0, ported: false };
    for (f, r) in faces.iter().zip(regions) {
        let end = r.port.map_or(r.classes.len(), |p| p.start);
        out.pairs.extend(f.iter().zip(r.classes).take(end).filter_map(|(face, &c)| face.as_ref().map(|face| (face.masses[c], face.total))));
        if let Some(port) = r.port {
            out.coupled += port_code(f, &port)?;
            out.ported = true;
        }
    }
    Ok(out)
}

/// A port's coupling code on `2^(−20)` bits from a region's faces (§16.24).
fn port_code(faces: &[Option<TowerFace>], port: &Port) -> Result<i64> {
    Ok(port_reading(&port_faces(faces, port)?, port)?.1)
}

/// A port's places' faces, each `(masses, total)`: every place must carry one, but a port at its boundary or on its letters
/// may hold resolved places, which carry none and are read as `(∅, 0)` (§16.47, [`boundary_reading`], [`letters_reading`]).
fn port_faces<'f>(faces: &'f [Option<TowerFace>], port: &Port) -> Result<Vec<(&'f [u128], u128)>> {
    let stop = port.stop.unwrap_or(faces.len()).min(faces.len());
    faces[port.start..]
        .iter()
        .enumerate()
        .map(|(k, f)| match f {
            _ if port.start + k >= stop || port.heard.is_some_and(|h| !h[port.start + k]) => Ok((&[][..], 0)),
            Some(f) => Ok((f.masses.as_slice(), f.total)),
            None if port.boundary || port.letters => Ok((&[][..], 0)),
            None => refuse("a port's place without a face"),
        })
        .collect()
}

/// Each region's run of compared sites before its port and its weight in the joint code, `(K, m, K)`
/// ([`Region::weight`], §16.23), in the order [`compared`] reads them.
fn spans_of(regions: &[Region]) -> Vec<(usize, u64, u64)> {
    regions.iter().map(|r| { let (m, k) = r.weight(); (r.unresolved[..r.port.map_or(r.unresolved.len(), |p| p.start)].iter().filter(|&&u| u).count(), m, k) }).collect()
}

/// The regions' code on `2^(−20)` bits: the weighed code of the sites before the ports (§16.23, [`super::weighed_code`])
/// and the ports' coupling codes (§16.24).
fn code_of(c: &Compared, spans: &[(usize, u64, u64)]) -> i64 {
    weighed_code(&c.pairs, spans) + c.coupled
}

/// Whether `new` codes strictly fewer bits than `old`. Where a port is read, its coupling code has no product form, so
/// the decision is the codes' on their grain (`2^(−20)` bits, §16.24); otherwise it is the weighed certificate's.
fn fewer(old: &Compared, new: &Compared, spans: &[(usize, u64, u64)]) -> bool {
    if old.ported || new.ported {
        code_of(new, spans) < code_of(old, spans)
    } else {
        fewer_bits_weighed(&old.pairs, &new.pairs, spans)
    }
}

/// [measurement; agent-inferred, November 4, §16.41] **A step's first-order change of the code it was fit on**: `Σ_i g_i Δθ_i`
/// with `Δθ = −step` at its full size and `g` the section's covector as its return gives it, on the codes' `2^(−20)` bits, a
/// unit of `g Δθ` standing at `2^(−(40 + grain − 20))` bits on the material's families and `2^(−(24 + grain − 20))` on the
/// faces' (the covector's grains, as `covector_matches_the_codes_difference` reads them); `None` where a product or the sum
/// passes its carrier. With the change the certificate reads at the full step it is the section's own parabola; with the next
/// section's covector and the step at the halvings it stood at, the step's transfer ([`FieldReceipt::transfer`]).
fn predicted_change(field: &Field, g: &[i128], step: &[i128], halvings: u32) -> Option<i64> {
    let mut total = 0i128;
    for &(start, len, grain) in &field.families_all() {
        let shift = if grain == MATERIAL_BITS { 40 + grain - 20 } else { 24 + grain - 20 };
        let mut family = 0i128;
        for i in start..start + len {
            family = family.checked_add(g[i].checked_mul(-release(step[i], halvings))?)?;
        }
        total = total.checked_add(family >> shift)?;
    }
    i64::try_from(total).ok()
}

/// [measurement; November 7] [`predicted_change`] over one family `(start, len, grain)` alone.
fn predicted_change_family(field: &Field, g: &[i128], step: &[i128], halvings: u32, (start, len, grain): (usize, usize, u32)) -> Option<i64> {
    let _ = field;
    let shift = if grain == MATERIAL_BITS { 40 + grain - 20 } else { 24 + grain - 20 };
    let mut family = 0i128;
    for i in start..start + len {
        family = family.checked_add(g[i].checked_mul(-release(step[i], halvings))?)?;
    }
    i64::try_from(family >> shift).ok()
}

/// `base` less `release(step, halvings)` in each entry, and whether any entry moved.
fn stepped(base: &Field, step: &[i128], halvings: u32) -> Result<(Field, bool)> {
    let mut candidate = base.clone();
    let mut moved = false;
    for (slot, &q) in candidate.material_mut().zip(step) {
        let s = release(q, halvings);
        if s != 0 {
            moved = true;
            *slot = fit32(*slot as i128 - s, "a deposited parameter outgrew its 32-bit carrier")?;
        }
    }
    Ok((candidate, moved))
}

/// What [`scaled`] read: the regions' code under the step at its size less `old`'s (on `2^(−20)`
/// bits), the further halvings of the last size read, and the stepped material that stands with
/// its faces (`None`: the step stands at no size read).
struct Scaled {
    change: i64,
    halvings: u32,
    standing: Option<(Field, Vec<Vec<Option<TowerFace>>>)>,
}

/// [definition; agent-inferred, November 1] **A step's size read in at most three reads**, the one
/// law of the certificate ([`FieldLearner::section_realized`], `strict`: the stepped material must
/// code the regions strictly fewer bits than `old`) and of the held step's read on the next
/// regions ([`FieldLearner::next_scale`]: no more bits). The step `base − release(step, h0)` is
/// read; where it stands, it stands. Otherwise it is read at half its size; where that stands, it
/// stands halved. Otherwise the excess `e(μ)` of the regions' code over `old`'s at the step's
/// fraction `μ` is read at `μ = 1` and `μ = ½`, and the parabola `e(μ) = aμ + bμ²` through them
/// (`e(0) = 0`) has `a = 4e(½) − e(1)`, `b = 2e(1) − 4e(½)`: with `a ≥ 0` (or an excess the codes
/// read at or below zero where the integer comparison did not stand) the step's direction raises the
/// regions' code at every size the reads resolve, and it stands nowhere; with `a < 0` (then
/// `b > 0`) the parabola is lowest at `μ* = −a/2b ≤ ¼`, and the step is read once more at the
/// largest halving `2^(−h) ≤ μ*`, where the parabola is below zero, standing there or nowhere. A
/// size that moves no entry stands nowhere.
///
/// Why bounded (the second reading, receipts `…_receipts/reading-2/`): halving until the step
/// stood took 1,608 rereads of the next regions over 131 of 336 sections, 67 of the 105 halved
/// steps standing only at `2^(−12)` of their size or less, and the certificate's own halvings
/// reached 9 to 18 on 14 sections; their direction, not their size, raised the code, which the
/// parabola reads from two reads where the halvings read it from a dozen.
fn scaled(base: &Field, step: &[i128], h0: u32, old: &Compared, strict: bool, regions: &[Region], realization: &mut dyn FieldRealization) -> Result<Scaled> {
    let spans = spans_of(regions);
    let stands = |new: &Compared| if strict { fewer(old, new, &spans) } else { !fewer(new, old, &spans) };
    let code_old = code_of(old, &spans);
    let (full, moved) = stepped(base, step, h0)?;
    if !moved {
        return Ok(Scaled { change: 0, halvings: 0, standing: None });
    }
    let full_faces = realization.read_faces(&full, regions)?;
    let at_full = compared(&full_faces, regions)?;
    let change = code_of(&at_full, &spans) - code_old;
    if stands(&at_full) {
        return Ok(Scaled { change, halvings: 0, standing: Some((full, full_faces)) });
    }
    let nowhere = |halvings: u32| Scaled { change, halvings, standing: None };
    let (half, moved) = stepped(base, step, h0 + 1)?;
    if !moved {
        return Ok(nowhere(1));
    }
    let half_faces = realization.read_faces(&half, regions)?;
    let at_half = compared(&half_faces, regions)?;
    if stands(&at_half) {
        return Ok(Scaled { change, halvings: 1, standing: Some((half, half_faces)) });
    }
    // The parabola through the two excesses (on the codes' `2^(−20)` bits).
    let (e1, e2) = (i128::from(change), i128::from(code_of(&at_half, &spans) - code_old));
    let a = 4 * e2 - e1;
    if e1 <= 0 || e2 <= 0 || a >= 0 {
        return Ok(nowhere(1));
    }
    // `1/μ* = 2b/(−a) = (4e(1) − 8e(½))/(e(1) − 4e(½))`; `h` the least with `2^h ≥ 1/μ*`.
    let (num, den) = (4 * e1 - 8 * e2, e1 - 4 * e2);
    let mut h = 2u32;
    while h < 127 && (den << h) < num {
        h += 1;
    }
    let (candidate, moved) = stepped(base, step, h0 + h)?;
    if !moved {
        return Ok(nowhere(h));
    }
    let candidate_faces = realization.read_faces(&candidate, regions)?;
    if stands(&compared(&candidate_faces, regions)?) {
        return Ok(Scaled { change, halvings: h, standing: Some((candidate, candidate_faces)) });
    }
    Ok(nowhere(h))
}

/// [definition; agent-inferred, November 1] **The field's learner**: the field, the covector's two
/// moments and the step's rate `2^(−k)`. The deposit is the tower's ([`super::TowerLearner`]),
/// with one difference: a coordinate's moments open at its own first nonzero covector (`m = g`,
/// `v = g²`), not at the section the learner first read. The returns and the readout open at zero,
/// so the charts' covectors first arrive sections later; moments opened from zero would step them
/// two to four times the declared rate until the second moment caught up (the review of
/// November 1).
///
/// **A step is held and read on the next regions** (the tower's acceptance 77,
/// [`super::TowerLearner::next_section`], always declared here): a step certified on its own
/// section is held, and the next section's regions are read under the material before it and its
/// size read on them by the one bounded law of a step's size ([`scaled`]): it stands at its size,
/// at half, or at the parabola's halving where it codes them no higher, or is refused (the
/// material before it stands). The moments stay as they moved. Why
/// (the first reading on the card, November 1): the certificate read only its own section, and
/// the held-out answer code rose at the second lap and the third (5.38, 5.49, 6.18 bits a class)
/// while the passage's own code fell every section; the tower had recorded this failure and its
/// repair, and the field was built without it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldLearner {
    pub field: Field,
    /// [definition; the unified-theory reading of November 7, 21:58] **The averaged constitution** `θ̄`, moved toward the live
    /// `θ` by `2^(−8)` each section ([`FieldLearner::average_section`]; the second moments' rate, a memory of 256 sections):
    /// a state stepping noisily about its floor sits above it by `½ tr(H·Cov)` while the mean of its states sits at it, so
    /// `θ̄` is what is read and saved beside the live `θ`, which keeps stepping. A restart carries both. It is kept 8 bits
    /// finer than `θ`'s grain (theory, 22:08), so the remainder `toward` releases is carried and `θ̄` is the walk's mean,
    /// not its median.
    pub average: Option<Vec<i64>>,
    first: Vec<i128>,
    second: Vec<i128>,
    pub rate_bits: u32,
    /// The founding key bytes read so far: the founding's, then each growth's.
    pub drawn: usize,
    /// The laps the learner has read (an exterior walk's count, so a continued run keeps its
    /// keyed masks and order moving rather than replaying the first lap's).
    pub laps: u64,
    held: Option<HeldStep>,
    /// [definition; agent-inferred, November 3, §16.30] Whether a deposited step is held and read on the next regions
    /// before it stands (the tower's acceptance 77). The field's law is `false`: a step stands at the size its own
    /// section certified (strictly fewer bits there, [`scaled`]), and the next regions are read under it as they come.
    /// Why: from the same trained state, two laps read the held answers' joint code at 3.200 and 3.160 bits a byte with
    /// the steps standing unread against 3.204 and 3.174 with the next-section read, in 171 s a lap against 280 s (the
    /// read refused 30% of the steps and halved 55%: a step that lowers its own section's code raises another
    /// section's about as often as gradient noise says, so the read mostly threw away and shrank good steps). `true`
    /// keeps the read as a declared comparison. Not carried in the learner's text.
    pub read_held: bool,
    /// [definition; the unified-theory reading of November 7, 05:55] Whether a kernel section steps by the evidence-shrunk
    /// Newton step along the moments' direction ([`FieldLearner::section_kernel`]) instead of the moments' own step. Not
    /// carried in the learner's text.
    pub newton: bool,
    /// [measurement; the unified-theory reading of November 7, 06:26] Whether a kernel section reads the evidence-shrunk Newton
    /// step's terms (`s`, `v`, `c` and `α`) beside the moments' own step, without taking it. Not carried in the learner's
    /// text.
    pub newton_read: bool,
    /// [definition; the unified-theory reading of November 7, 06:26] **The moments count states, not sections**: the first
    /// and second moments move at `2^(−first_rate)` and `2^(−second_rate)` a section ([`FIRST_RATE`] and [`SECOND_RATE`]
    /// at sixteen states a section; a section of `16·4^k` states moves them `2k` bits faster, so a section of 256 is its own
    /// first moment). Not carried in the learner's text.
    pub first_rate: u32,
    pub second_rate: u32,
    /// [definition; the unified-theory reading of November 7, 06:57] **Each family reads its length from its own transfer**:
    /// where set, family `f` steps at `2^(−ρ_f)` (`ρ_f` on `2^(−24)` bits, opening at the learner's rate, unbounded: a
    /// negative `ρ_f` lengthens the step past the moments' unit, checked at its carrier), and after each
    /// section `ρ_f` moves `¼ τ̄_f/|π̄_f|` bits, `τ̄_f` and `π̄_f` the family's transfer (the step before priced on this
    /// section) and own-section price, each averaged at `2^(−first_rate)`. A step the next section pays for grows shorter, a
    /// step the next section keeps pulling grows longer: for one noisy quadratic mode `E τ = −η|μ|² + η²c` vanishes at the
    /// length `η = |μ|²/c` that lowers the code most per step [derived]; a quarter of the correction a section settles in about
    /// twenty sections [agent-inferred]. Carried in the learner's text with the two averages (the unified-theory reading of
    /// November 7, 07:24), so a continued learner keeps them.
    pub family_rates: Option<Vec<i128>>,
    /// [definition; the unified-theory reading of November 7, 06:57] Whether a kernel section deposits the letters'
    /// temperature's covector ([`FieldLearner::section_kernel`]). Not carried in the learner's text.
    pub temper_learns: bool,
    family_transfer: Vec<i128>,
    family_price: Vec<i128>,
    /// [measurement; §16.41] The step the last section stood at, the operand of the next section's
    /// [`FieldReceipt::transfer`]; a reading's operand, not carried in the learner's text, cleared by every growth, and not
    /// kept under the held read (whose next section moves the step before pricing it).
    last: Option<HeldStep>,
}

impl FieldLearner {
    /// The learner of a field founded on its declared key stream (the founding read
    /// [`FieldDeclaration::founding_draws`] draws).
    pub fn new(field: Field, rate_bits: u32) -> Self {
        let len = field.material_len();
        let drawn = 4 * field.declaration.founding_draws();
        Self { field, first: vec![0; len], second: vec![0; len], rate_bits, drawn, laps: 0, held: None, read_held: false, newton: false, newton_read: false, first_rate: FIRST_RATE, second_rate: SECOND_RATE, family_rates: None, temper_learns: false, family_transfer: Vec::new(), family_price: Vec::new(), last: None, average: None }
    }

    /// Whether a deposited step is held for the next regions' read.
    pub fn holds_step(&self) -> bool {
        self.held.is_some()
    }

    /// [definition; agent-inferred, November 1] **The learner widened** ([`Field::grown`]), its
    /// differences read from the founding key stream past every draw read before, and its moments
    /// lifted as the tower's are: split evenly, each grown coordinate's covector at the growth
    /// point is the old one divided among its `f` copies and the readout's the old one, so a grown
    /// coordinate carries `m/f` and `v/f²`, the readout `m` and `v`, and opens on the old
    /// normalized step. Each copy then steps as the old coordinate did, and the `f` copies of a
    /// sum move together, so the rate falls by `⌈log₂ f⌉` bits: the field's step stays the old one.
    /// A learner holding a step is refused: the step is read first ([`FieldLearner::read_step_on`]).
    pub fn widened(&self, factor: usize, keys: &[u8]) -> Result<Self> {
        if self.held.is_some() {
            return refuse("a learner widens after its held step is read");
        }
        let rest = keys.get(self.drawn..).ok_or(TowerError::Refused("fewer key bytes than the growth draws"))?;
        let (field, from) = self.field.grown(factor, rest)?;
        let (f, f2) = (factor as i128, (factor * factor) as i128);
        let first = from.iter().map(|&(i, divided)| if divided { div_nearest(self.first[i], f) } else { self.first[i] }).collect();
        let second = from.iter().map(|&(i, divided)| if divided { div_nearest(self.second[i], f2) } else { self.second[i] }).collect();
        let drawn = self.drawn + 4 * self.field.growth_draws(factor);
        let rate_bits = self.rate_bits + (usize::BITS - (factor - 1).leading_zeros());
        Ok(Self { field, first, second, rate_bits, drawn, laps: self.laps, held: None, read_held: self.read_held, newton: self.newton, newton_read: self.newton_read, first_rate: self.first_rate, second_rate: self.second_rate, family_rates: None, temper_learns: false, family_transfer: Vec::new(), family_price: Vec::new(), last: None, average: None })
    }

    /// [definition; agent-inferred, November 4, §16.40] **The learner with one more lane** ([`Field::laned`]), the lane's
    /// draws read from the founding key stream past every draw read before. Every old entry keeps its moments; each of the
    /// lane's entries opens on its family's statistics, its first moment at zero and its second at the mean of its
    /// family's old second moments (a family no covector has reached opens at zero, at its own first covector, as a
    /// founding's entries do). The rate is kept: no coordinate is shared among copies, so each steps as it did.
    ///
    /// Why the family's statistics and not the founding's opening: an entry opened at its first covector takes the
    /// largest normalized step, `2^(grain − rate)` with the covector's sign, and every read from a fresh lane opens at
    /// once and in agreement, so the lane moved the trained keys, values and drives together by about a tenth of their
    /// unit a section. Measured from run41's alone state grown to `D 512` (`_receipts/law44/probe_founding.txt`): 208
    /// halvings over 212 sections against the alone arm's one, 166 of 212 deposited, the sections' code before their step
    /// 1.628 bits a byte against 1.470, and the withheld code 0.268 to 0.294 bits a site in half a lap. Opened on its
    /// family's second moment, a lane entry's first step is an eighth of its covector over the family's own scale, the
    /// step the trained entries beside it take; on the same state (`probe_family.txt`): 169 halvings over 219 sections,
    /// 211 deposited, the withheld code 0.268 to 0.286. Smaller, not gone: the lane's covectors stay coherent, so its steps
    /// grow toward the full normalized size as its first moments fill.
    pub fn laned(&self, keys: &[u8]) -> Result<Self> {
        if self.held.is_some() {
            return refuse("a learner grows a lane after its held step is read");
        }
        let rest = keys.get(self.drawn..).ok_or(TowerError::Refused("fewer key bytes than the lane's draws"))?;
        let (field, from) = self.field.laned(rest)?;
        let first = from.iter().map(|o| o.map_or(0, |i| self.first[i])).collect();
        let mut second: Vec<i128> = from.iter().map(|o| o.map_or(0, |i| self.second[i])).collect();
        for &(start, len, _) in field.families_all().iter() {
            let old: Vec<i128> = (start..start + len).filter_map(|k| from[k].map(|i| self.second[i])).collect();
            if old.len() == len || old.is_empty() {
                continue;
            }
            // The mean term by term (each second moment is under `2^126`, so a family's sum is not formed).
            let n = old.len() as i128;
            let mean = old.iter().map(|v| v / n).sum::<i128>() + old.iter().map(|v| v % n).sum::<i128>() / n;
            for k in (start..start + len).filter(|&k| from[k].is_none()) {
                second[k] = mean;
            }
        }
        let drawn = self.drawn + 4 * self.field.declaration.lane_draws();
        Ok(Self { field, first, second, rate_bits: self.rate_bits, drawn, laps: self.laps, held: None, read_held: self.read_held, newton: self.newton, newton_read: self.newton_read, first_rate: self.first_rate, second_rate: self.second_rate, family_rates: None, temper_learns: false, family_transfer: Vec::new(), family_price: Vec::new(), last: None, average: None })
    }

    /// The held step read on `regions` without a deposit: the faces of `regions` under the
    /// material that stands after the read, and the read (`None` when no step was held).
    pub fn read_step_on(&mut self, regions: &[Region], realization: &mut dyn FieldRealization) -> Result<(Vec<Vec<Option<TowerFace>>>, Option<FieldNext>)> {
        let (faces, _, next) = self.open(regions, realization, false)?;
        Ok((faces, next))
    }

    /// The opening read of `regions` (with the covector when `returning`), after the held step,
    /// if any, is read on them ([`FieldLearner::next_scale`]): the material before it and the
    /// stepped material read first, the material that stands decided, and the opening read read
    /// on it (a read already made is not made again).
    fn open(&mut self, regions: &[Region], realization: &mut dyn FieldRealization, returning: bool) -> Result<(Vec<Vec<Option<TowerFace>>>, Option<Vec<i128>>, Option<FieldNext>)> {
        let Some(held) = self.held.take() else {
            return if returning {
                let (faces, g) = realization.read_and_return(&self.field, regions)?;
                Ok((faces, Some(g), None))
            } else {
                Ok((realization.read_faces(&self.field, regions)?, None, None))
            };
        };
        let mut before = self.field.clone();
        for (slot, &q) in before.material_mut().zip(&held.step) {
            *slot = fit32(*slot as i128 + release(q, held.halvings), "a held step's material outgrew its 32-bit carrier")?;
        }
        let (standing, faces, next) = Self::next_scale(&before, &held, regions, realization)?;
        self.field = standing;
        if returning {
            let (faces, g) = realization.read_and_return(&self.field, regions)?;
            return Ok((faces, Some(g), Some(next)));
        }
        Ok((faces, None, Some(next)))
    }

    /// [definition; agent-inferred, November 1] **The held step read on regions it was not fit
    /// on** (the tower's acceptance 77, `TowerLearner::next_section`): the regions are read under
    /// the material before the step (`old`), and the step's size is read on them by [`scaled`]
    /// against `old`, standing where it codes them no higher. A refused step leaves the material
    /// before it, so the material that stands never codes the regions higher than `old`. At most
    /// four reads of the regions are made before the opening read.
    ///
    /// Returns the material that stands, its faces, and the read.
    #[allow(clippy::type_complexity)]
    fn next_scale(before: &Field, held: &HeldStep, regions: &[Region], realization: &mut dyn FieldRealization) -> Result<(Field, Vec<Vec<Option<TowerFace>>>, FieldNext)> {
        let before_faces = realization.read_faces(before, regions)?;
        let old = compared(&before_faces, regions)?;
        let scale = scaled(before, &held.step, held.halvings, &old, false, regions, realization)?;
        let next = FieldNext { change: scale.change, halvings: scale.halvings, refused: scale.standing.is_none() };
        Ok(match scale.standing {
            Some((field, faces)) => (field, faces, next),
            None => (before.clone(), before_faces, next),
        })
    }

    /// One section: the step the section before deposited read on its regions, then its regions
    /// read and returned on the material that stands, the moments moved, and the step deposited
    /// at the size where the regions reread under it code strictly fewer bits ([`scaled`]: its
    /// size, half, or the parabola's halving; none of them, no deposit) and held for the next
    /// section.
    pub fn section(&mut self, regions: &[Region]) -> Result<FieldReceipt> {
        self.section_realized(regions, &mut HostField)
    }

    /// [`FieldLearner::section`] on a declared realization of the field's read and return; the
    /// moments, the step and the certificates' decisions stay on the host.
    pub fn section_realized(&mut self, regions: &[Region], realization: &mut dyn FieldRealization) -> Result<FieldReceipt> {
        let (faces, g, next) = self.open(regions, realization, true)?;
        let g = g.ok_or(TowerError::Refused("a section's opening read returned no covector"))?;
        let faces_old = compared(&faces, regions)?;
        let spans = spans_of(regions);
        let code_before = code_of(&faces_old, &spans);
        if faces_old.pairs.is_empty() && !faces_old.ported {
            return refuse("a section with no unresolved site");
        }
        // The sites the weighed code is a code of (§16.23): each region's domain where it reads an open site.
        let sites = spans.iter().filter(|s| s.0 > 0).map(|s| s.1 as usize).sum::<usize>()
            + regions.iter().filter_map(|r| r.port.map(|p| (p.start..p.stop.unwrap_or(r.classes.len()).min(r.classes.len())).filter(|&t| r.unresolved[t] && p.heard.is_none_or(|h| h[t])).count())).sum::<usize>();
        let (deposited, predicted, transfer, external) = self.deposit(g)?;
        Ok(FieldReceipt { sites, code_before, code_after: None, halvings: 0, deposited, next, predicted, change: None, transfer, external })
    }

    /// The moments moved by a section's covector `g` (each family's on its natural grain; `g` is left on the step's grain).
    fn moments_take(&mut self, g: &mut [i128]) -> Result<()> {
        for &(start, len, grain) in &self.field.families_all() {
            for v in &mut g[start..start + len] {
                *v = on_step_grain(grain, *v);
            }
        }
        for ((m, v), gv) in self.first.iter_mut().zip(self.second.iter_mut()).zip(g.iter()) {
            let square = gv.checked_mul(*gv).ok_or(TowerError::Refused("a covector's square outgrew its 128-bit carrier"))?;
            if *m == 0 && *v == 0 {
                // A coordinate opens at its own first nonzero covector.
                (*m, *v) = (*gv, square);
            } else {
                *m = toward(*m, *gv, self.first_rate);
                *v = toward(*v, square, self.second_rate);
            }
        }
        Ok(())
    }

    /// The evidence-shrunk Newton step's terms along `direction` (a step on the families' grains, subtracted from the
    /// material): each state's `u_s = D_s · d` weighed `f_s = w_s u_s`, `s = Σ f`, `v = n/(n − 1) Σ(f − s/n)²`,
    /// `c = (ln 2/2) Σ w u²`, the shrink `(max(0, s² − v), s²)` and `α = (s² − v) 2^20 / (−s c)` where `s < 0`, `s² > v` and
    /// `c > 0` (else `(0, 0)`). A reading: nothing is moved.
    fn newton_terms(&self, states: &[Vec<i128>], weights: &[i128], direction: &[i128]) -> Result<NewtonRead> {
        const OVER: &str = "a Newton step past its 128-bit carrier";
        let mut read = NewtonRead::default();
        let (mut sum, mut squares, mut curvature) = (0i128, 0i128, 0i128);
        let mut priced = 0usize;
        for (d, &w) in states.iter().zip(weights) {
            let Some(u) = predicted_change(&self.field, d, direction, 0) else { continue };
            let u = u as i128;
            let f = release(w.checked_mul(u).ok_or(TowerError::Refused(OVER))?, MATERIAL_BITS);
            sum += f;
            squares += f.checked_mul(f).ok_or(TowerError::Refused(OVER))?;
            curvature += release(w.checked_mul(u.checked_mul(u).ok_or(TowerError::Refused(OVER))?).ok_or(TowerError::Refused(OVER))?, MATERIAL_BITS);
            priced += 1;
        }
        let n = priced as i128;
        let variance = if n > 1 { (n * squares - sum * sum) / (n - 1) } else { 0 };
        let curvature = release(curvature.checked_mul(crate::hnn::keyed_modes::ln2_face()).ok_or(TowerError::Refused(OVER))?, LN2_FACE_BITS) / 2;
        (read.slope, read.variance, read.curvature) = (sum, variance, curvature);
        let evidence = sum * sum - variance;
        read.shrink = (evidence.max(0), sum * sum);
        if sum < 0 && evidence > 0 && curvature > 0 {
            // α = −(s² − v) 2^20 / (s c): s on 2^(−20), v and c on 2^(−40).
            read.alpha = (evidence.checked_mul(1 << 20).ok_or(TowerError::Refused(OVER))?, (-sum).checked_mul(curvature).ok_or(TowerError::Refused(OVER))?);
        }
        Ok(read)
    }

    /// Opens each family's length at the learner's rate ([`FieldLearner::family_rates`]).
    pub fn open_family_rates(&mut self) {
        let families = self.field.families_all().len();
        self.family_rates = Some(vec![(self.rate_bits as i128) << MATERIAL_BITS; families]);
        (self.family_transfer, self.family_price) = (vec![0; families], vec![0; families]);
    }

    /// [definition; the unified-theory reading of November 7, 05:55; agent-inferred where marked] **An evidence-shrunk Newton
    /// step along the moments' direction.** `d` is the step the moments would deposit before this section moves them (a
    /// direction this section never shaped). Each state's first-order change along it is `u_s = D_s · d` (bits on
    /// `2^(−20)`, `D_s` its covector on the families' natural grains), weighed `f_s = w_s u_s` by its kernel weight `w_s`
    /// (on `2^(−24)`). The section's slope is `s = Σ f_s`, its variance `v = n/(n − 1) Σ (f_s − s/n)²`, and its curvature
    /// `c = (ln 2/2) Σ w_s u_s²` (the information `J = (ln 2/2T²) E[min(1, A) D Dᵀ]` along `d`). The step is
    /// `α d` with `α = −(s/c)(1 − v/s²)`: Newton's along `d`, shrunk by the evidence `1 − v/s²`. [agent-inferred] The shrink
    /// is floored at zero (its positive part), so a section whose slope is uphill or under its own noise (`s ≥ 0` or
    /// `s² ≤ v`) deposits nothing. Then the covector `Σ w_s D_s` enters the moments. Returns whether it moved, `α` as
    /// `(numerator, denominator)`, the shrink as `(s² − v, s²)` (on `2^(−40)`), `s`, `v` and `c`, and the prices.
    #[allow(clippy::type_complexity)]
    fn deposit_newton(&mut self, states: &[Vec<i128>], weights: &[i128]) -> Result<NewtonRead> {
        let len = self.field.material_len();
        const OVER: &str = "a Newton step past its 128-bit carrier";
        let mut g = vec![0i128; len];
        for (d, &w) in states.iter().zip(weights) {
            if w == 0 {
                continue;
            }
            for (gv, &x) in g.iter_mut().zip(d) {
                *gv += release(x.checked_mul(w).ok_or(TowerError::Refused(OVER))?, MATERIAL_BITS);
            }
        }
        let raw = g.clone();
        let transfer = self.last.take().and_then(|s| predicted_change(&self.field, &raw, &s.step, s.halvings));
        let mut direction = vec![0i128; len];
        for &(start, n, grain) in &self.field.families_all() {
            for i in start..start + n {
                direction[i] = deposit_step(self.first[i], self.second[i], grain, self.rate_bits);
            }
        }
        let external = predicted_change(&self.field, &raw, &direction, 0);
        let mut read = self.newton_terms(states, weights, &direction)?;
        (read.transfer, read.external) = (transfer, external);
        let mut moved = false;
        let mut step = vec![0i128; len];
        if read.alpha.1 > 0 {
            let (num, den) = read.alpha;
            for (st, &dv) in step.iter_mut().zip(&direction) {
                *st = div_nearest(dv.checked_mul(num).ok_or(TowerError::Refused(OVER))?, den);
            }
            let (candidate, any) = stepped(&self.field, &step, 0)?;
            if any {
                self.field = candidate;
                moved = true;
            }
        }
        read.predicted = predicted_change(&self.field, &raw, &step, 0);
        self.moments_take(&mut g)?;
        read.deposited = moved;
        if moved {
            if self.read_held {
                self.held = Some(HeldStep { step, halvings: 0 });
            } else {
                self.last = Some(HeldStep { step, halvings: 0 });
            }
        }
        Ok(read)
    }

    /// [definition; agent-inferred, November 7] **A section's deposit of its covector** `g` (each family's on its natural
    /// grain, the code's covector): the step the section before stood at priced on it (`transfer`), the step the moments
    /// would deposit before it moves them priced on it (`external`), the moments moved, and the step deposited at its size
    /// (fluxing, Brandon, November 5 17:29 and 17:32) with its first-order change (`predicted`). Returns whether it moved the
    /// material, `predicted`, `transfer` and `external`. Shared by [`FieldLearner::section_realized`] and
    /// [`FieldLearner::section_contrast`].
    #[allow(clippy::type_complexity)]
    fn deposit(&mut self, mut g: Vec<i128>) -> Result<(bool, Option<i64>, Option<i64>, Option<i64>)> {
        let raw = g.clone();
        let prev = self.last.take();
        let transfer = prev.as_ref().and_then(|s| predicted_change(&self.field, &raw, &s.step, s.halvings));
        // [the unified-theory reading of November 6, 08:54] The step the moments would deposit before this section moves them,
        // priced on this section: the external price, a step this section never shaped.
        let mut external_step = vec![0i128; g.len()];
        for &(start, len, grain) in &self.field.families_all() {
            for i in start..start + len {
                external_step[i] = deposit_step(self.first[i], self.second[i], grain, self.rate_bits);
            }
        }
        let external = predicted_change(&self.field, &raw, &external_step, 0);
        // The step before priced on this section by family, before the moments move.
        let families = self.field.families_all();
        let transfers: Option<Vec<Option<i64>>> = match (&self.family_rates, &prev) {
            (Some(_), Some(prev)) => Some(families.iter().map(|&fam| predicted_change_family(&self.field, &raw, &prev.step, prev.halvings, fam)).collect()),
            _ => None,
        };
        self.moments_take(&mut g)?;
        let mut step = vec![0i128; g.len()];
        for (k, &(start, len, grain)) in families.iter().enumerate() {
            match &self.family_rates {
                // `2^(−ρ_f)`: the whole bits through the deposit's own law (a right shift, or a left shift checked at its carrier
                // where `ρ_f < 0`: the unified-theory reading of November 7, 07:16, the law unclamped), the fraction through the
                // exponential's navigator.
                Some(rates) => {
                    let rho = rates[k];
                    let (whole, part) = (rho >> MATERIAL_BITS, (rho & ((1 << MATERIAL_BITS) - 1)) as i32);
                    let scale = temperature_of(-part, &self.field.fine)?;
                    const PAST: &str = "a family's step past its 128-bit carrier";
                    for i in start..start + len {
                        let root = super::deposit_root(self.second[i]);
                        let num = self.first[i].checked_mul(1i128 << grain).ok_or(TowerError::Refused(PAST))?;
                        let whole_step = if whole >= 0 {
                            (num >> whole.min(127)) / root
                        } else {
                            let k = u32::try_from(-whole).map_err(|_| TowerError::Refused(PAST))?;
                            num.checked_mul(1i128.checked_shl(k).filter(|&b| b > 0).ok_or(TowerError::Refused(PAST))?).ok_or(TowerError::Refused(PAST))? / root
                        };
                        step[i] = release(whole_step.checked_mul(scale).ok_or(TowerError::Refused(PAST))?, MATERIAL_BITS);
                    }
                }
                None => {
                    for i in start..start + len {
                        step[i] = deposit_step(self.first[i], self.second[i], grain, self.rate_bits);
                    }
                }
            }
        }
        let predicted = predicted_change(&self.field, &raw, &step, 0);
        // Each family's length moves by a quarter of its averaged transfer over its averaged own-section price.
        if let (Some(rates), Some(transfers)) = (&mut self.family_rates, transfers) {
            let rate = self.first_rate;
            for (k, &fam) in families.iter().enumerate() {
                let price = predicted_change_family(&self.field, &raw, &step, 0, fam).unwrap_or(0) as i128;
                let transfer = transfers[k].unwrap_or(0) as i128;
                let (t_avg, p_avg) = (&mut self.family_transfer[k], &mut self.family_price[k]);
                *t_avg = toward(*t_avg, transfer, rate);
                *p_avg = toward(*p_avg, price, rate);
                if *p_avg != 0 {
                    rates[k] += div_nearest(*t_avg << MATERIAL_BITS, 4 * p_avg.abs());
                }
            }
        }
        // [definition; Brandon, November 5 17:29 and 17:32] **The step fluxes**: it deposits at its size, and no reread of the
        // section certifies it. The reread kept a step only where the regions reread under it coded strictly fewer bits, a
        // selection on the code (a maximum in effect) that discarded what an expansion measures ("you can't discard failure
        // or mistakes, knowing what causes contraction in contrast to expansion is equally important") and cost a full read
        // of the section (27% of path75's second segment). What the step does is read by the passes the field makes anyway:
        // the next section's own covector prices it at first order ([`FieldReceipt::transfer`]), contraction and expansion
        // alike, and the moments carry every covector.
        let (candidate, moved) = stepped(&self.field, &step, 0)?;
        if !moved {
            return Ok((false, predicted, transfer, external));
        }
        self.field = candidate;
        if self.read_held {
            self.held = Some(HeldStep { step, halvings: 0 });
        } else {
            self.last = Some(HeldStep { step, halvings: 0 });
        }
        Ok((true, predicted, transfer, external))
    }

    /// [definition; the unified-theory reading of November 7, 10:12] **The contrast with persistent writes, its length from the
    /// writes' own fluctuation.** The section's covector `g = (1/T) Σ_j [∂G/∂θ(truth_j) − ∂G/∂θ(write_j)]` enters the moments, and
    /// the direction `d` is the moments' step with each family's length held (its `ρ_f`, unmoved). Along `d` each pair's
    /// first-order change `p_j = D_j · d` (bits) gives Newton's length `η = −2 Σ p_j / (n ln 2 Var_j p_j)`: the contrast's slope
    /// over the partition's curvature, the curvature read as half the variance across the pairs of `d·[∂G(write) − ∂G(truth)]`
    /// (away from the rest it errs the length short). The section steps `d` times an eleventh of the harmonic mean of the last
    /// eleven positive `η` (`etas`, on `2^(−32)`). The transfer (the step before priced on this section) is read, never acted
    /// on. `T` is held. Returns the receipt and this section's `η` (on `2^(−32)`, zero where it is not positive).
    pub fn section_contrast_scaled(&mut self, truth: &[Region], writes: &[Region], etas: &mut std::collections::VecDeque<i128>, realization: &mut dyn FieldRealization) -> Result<(ContrastReceipt, i128)> {
        let f = &self.field;
        if !f.declaration.energy || f.scale.is_some() {
            return refuse("a contrast section of a field without one energy");
        }
        if truth.len() < 2 || truth.len() != writes.len() {
            return refuse("a scaled contrast section needs two pairs or more, one write a truth");
        }
        let inverse = temperature_of(-f.theta[f.layout.face_temper], &f.fine)?;
        let both: Vec<Region> = truth.iter().chain(writes).copied().collect();
        let reads = realization.read_energy_material(f, &both)?;
        let n = truth.len();
        let material = f.material_len();
        let families = f.families_all();
        const OVER: &str = "a scaled contrast past its 128-bit carrier";
        let mut pairs: Vec<Vec<i128>> = Vec::with_capacity(n);
        let mut gap = 0i128;
        let mut same = 0usize;
        for s in 0..n {
            let ((gt, et), (gw, ew)) = (&reads[s], &reads[n + s]);
            if gt.len() != material || gw.len() != material {
                return refuse("a material covector of another length than the field's material");
            }
            gap += et - ew;
            same += usize::from(truth[s].classes == writes[s].classes);
            let mut d = vec![0i128; material];
            for &(start, len, grain) in &families {
                for i in start..start + len {
                    let scaled = release((gt[i] - gw[i]).checked_mul(inverse).ok_or(TowerError::Refused(OVER))?, MATERIAL_BITS);
                    d[i] = if grain == MATERIAL_BITS { scaled } else { release(scaled, 40 - super::COVECTOR_BITS) };
                }
            }
            pairs.push(d);
        }
        let gap = release(gap.checked_mul(inverse).ok_or(TowerError::Refused(OVER))?, MATERIAL_BITS);
        let mut g = vec![0i128; material];
        for d in &pairs {
            for (v, &x) in g.iter_mut().zip(d) {
                *v += x;
            }
        }
        let raw = g.clone();
        let transfer = self.last.take().and_then(|s| predicted_change(&self.field, &raw, &s.step, s.halvings));
        self.moments_take(&mut g)?;
        // The direction: the moments' step at each family's held length.
        let mut direction = vec![0i128; material];
        let rates = self.family_rates.clone();
        for (k, &(start, len, grain)) in families.iter().enumerate() {
            let rho = rates.as_ref().map_or((self.rate_bits as i128) << MATERIAL_BITS, |r| r[k]);
            let (whole, part) = (rho >> MATERIAL_BITS, (rho & ((1 << MATERIAL_BITS) - 1)) as i32);
            let scale = temperature_of(-part, &self.field.fine)?;
            for i in start..start + len {
                let root = super::deposit_root(self.second[i]);
                let num = self.first[i].checked_mul(1i128 << grain).ok_or(TowerError::Refused(OVER))?;
                let whole_step = if whole >= 0 {
                    (num >> whole.min(127)) / root
                } else {
                    num.checked_mul(1i128.checked_shl(u32::try_from(-whole).map_err(|_| TowerError::Refused(OVER))?).filter(|&b| b > 0).ok_or(TowerError::Refused(OVER))?).ok_or(TowerError::Refused(OVER))? / root
                };
                direction[i] = release(whole_step.checked_mul(scale).ok_or(TowerError::Refused(OVER))?, MATERIAL_BITS);
            }
        }
        // Each pair's first-order change along the direction, on 2^(−20) bits, and Newton's length.
        let p: Vec<i128> = pairs.iter().map(|d| predicted_change(&self.field, d, &direction, 0).map(i128::from).ok_or(TowerError::Refused(OVER))).collect::<Result<_>>()?;
        let sum: i128 = p.iter().sum();
        let nn = n as i128;
        let var = (nn * p.iter().map(|&x| x * x).sum::<i128>() - sum * sum) / (nn * (nn - 1));
        // η = −2 Σp / (n ln 2 Var p): Σp on 2^(−20), Var on 2^(−40); η on 2^(−32).
        let eta = if var > 0 && sum < 0 {
            let num = (-2 * sum).checked_mul(1i128 << (20 + 32 + LN2_FACE_BITS)).ok_or(TowerError::Refused(OVER))?;
            num / (nn * crate::hnn::keyed_modes::ln2_face() * var)
        } else {
            0
        };
        if eta > 0 {
            etas.push_back(eta);
            while etas.len() > 11 {
                etas.pop_front();
            }
        }
        // An eleventh of the harmonic mean of the last eleven positive lengths.
        let length = if etas.is_empty() {
            0
        } else {
            let inverse_sum: i128 = etas.iter().map(|&e| (1i128 << 64) / e.max(1)).sum();
            ((etas.len() as i128) << 64) / inverse_sum.max(1) / 11
        };
        let step: Vec<i128> = direction.iter().map(|&dv| release(dv.checked_mul(length).unwrap_or(0), 32)).collect();
        let predicted = predicted_change(&self.field, &raw, &step, 0);
        let (candidate, moved) = stepped(&self.field, &step, 0)?;
        if moved {
            self.field = candidate;
            self.last = Some(HeldStep { step, halvings: 0 });
        }
        Ok((ContrastReceipt { states: n, same, gap, deposited: moved, predicted, transfer, external: None }, eta))
    }

    /// [definition; the unified-theory reading of November 7, 04:05, route (b)] **An energy field's section meets its own
    /// release.** The open places' code under one energy is
    /// `l = −log₂ P(e_O = truth_O | rest) = G(truth)/T + log₂ Σ_e 2^(−G(e)/T)`, with `G(e) = Φ(x^K(e); e)` each configuration
    /// relaxed at its own certified halvings ([`Field::energy_material`]). Its material covector is
    /// `(1/T)[∂G/∂θ(truth) − E_P ∂G/∂θ(e′)]`, read at one release `e′` a state: `release[s]` is `truth[s]` with its open
    /// places as the field's own release wrote them (the writer as it writes), every site resolved in both. The section
    /// deposits that covector as any section's ([`FieldLearner::deposit`]): the step fluxes. The partition function is not
    /// read, so no code certifies it. `T` is the letters' temperature (`face_temper`), held: neither `G` nor its covector
    /// reads it. The lock temperatures are held as `G`'s covector holds them.
    ///
    /// Covector units: [`Field::energy_material`] reads every family on `2^(−40)` a real unit, the deposit's material
    /// families on `2^(−40)` and its face families on `2^(−24)`, so a face family's is released 16 bits.
    pub fn section_contrast(&mut self, truth: &[Region], release_of: &[Region], realization: &mut dyn FieldRealization) -> Result<ContrastReceipt> {
        let f = &self.field;
        if !f.declaration.energy || f.scale.is_some() {
            return refuse("a contrast section of a field without one energy");
        }
        if truth.is_empty() || truth.len() != release_of.len() {
            return refuse("a contrast section needs one release a state");
        }
        let inverse = temperature_of(-f.theta[f.layout.face_temper], &f.fine)?;
        let both: Vec<Region> = truth.iter().chain(release_of).copied().collect();
        let reads = realization.read_energy_material(f, &both)?;
        let n = truth.len();
        let mut g = vec![0i128; f.material_len()];
        let mut gap = 0i128;
        let mut same = 0usize;
        for s in 0..n {
            let ((gt, et), (gr, er)) = (&reads[s], &reads[n + s]);
            if gt.len() != g.len() || gr.len() != g.len() {
                return refuse("a material covector of another length than the field's material");
            }
            gap += et - er;
            same += usize::from(truth[s].classes == release_of[s].classes);
            for ((v, a), b) in g.iter_mut().zip(gt).zip(gr) {
                *v += a - b;
            }
        }
        const OVER: &str = "a contrast covector past its 128-bit carrier";
        for &(start, len, grain) in &f.families_all() {
            for v in &mut g[start..start + len] {
                let scaled = release(v.checked_mul(inverse).ok_or(TowerError::Refused(OVER))?, MATERIAL_BITS);
                *v = if grain == MATERIAL_BITS { scaled } else { release(scaled, 40 - super::COVECTOR_BITS) };
            }
        }
        let gap = release(gap.checked_mul(inverse).ok_or(TowerError::Refused(OVER))?, MATERIAL_BITS);
        // [the unified-theory reading of November 7, 09:36] The letters' temperature in the deposit, as the kernel's:
        // `∂l/∂τ = −ln 2 Σ_s (G_s − G′_s)/T`, here the gap itself.
        if self.temper_learns {
            let nats = release(gap.checked_mul(crate::hnn::keyed_modes::ln2_face()).ok_or(TowerError::Refused(OVER))?, LN2_FACE_BITS);
            g[f.layout.face_temper] = -(nats << (40 - ENERGY_BITS));
        }
        let (deposited, predicted, transfer, external) = self.deposit(g)?;
        Ok(ContrastReceipt { states: n, same, gap, deposited, predicted, transfer, external })
    }

    /// [definition; the unified-theory reading of November 7, 05:20; agent-inferred] **A kernel block's spacing**: the least
    /// spacing at which no receiver's near lock sees two block places. A receiver's near field is `0 < |i − j| < NEAR`, so two
    /// places `NEAR − 1` from one receiver on either side are `2(NEAR − 1)` apart; a block's places stand `2(NEAR − 1) + 1`
    /// apart. Couplings past the near field (a crowd joining two, or the ticks' transport) the Metropolis–Hastings test
    /// counts.
    pub fn kernel_spacing() -> usize {
        2 * (NEAR - 1) + 1
    }

    /// [definition; the unified-theory reading of November 7, 05:20, route (b)'s negative] **An energy section's step from
    /// one invariant kernel step at the truth.** Each state `truth[s]` (every site resolved) opens its block `blocks[s]`, each
    /// block place carrying its truth's letter as a locked mixture, so one read ([`FieldRealization::read_energy_faces`])
    /// gives `G` and every block place's face at the truth. Each block place draws `a_t` from its face (keyed by `seed`, the
    /// state and the place); the proposal read gives `G′` and the faces `face′`. The block's Metropolis–Hastings ratio is
    /// `A = 2^((G − G′)/T) Π_t face′_t(truth_t)/face_t(a_t)`, and the section deposits
    /// `(1/T) Σ_s min(1, A_s)[∂G/∂θ(truth_s) − ∂G/∂θ(e′_s)]` (the accept coin's expectation, no coin), its step fluxing. By
    /// detailed balance the expected deposit is zero at the true distribution for any block and proposal; over the keyed
    /// blocks every open place is reached, and the rest holds each place's enumerated conditional at the truth (every letter's `G` read). `min(1, A)` is
    /// read through the exponential's navigator on `2^(−24)` and released to zero below its carrier (`2^(−23)`). Four reads
    /// a state: the faces at the truth and at the proposal, and the two material covectors.
    pub fn section_kernel(&mut self, truth: &[Region], blocks: &[Vec<usize>], seed: u64, realization: &mut dyn FieldRealization) -> Result<KernelReceipt> {
        let owners: Vec<usize> = (0..blocks.len()).collect();
        self.section_kernel_grouped(truth, &owners, blocks, seed, realization)
    }

    /// [definition; the unified-theory reading of November 7, 07:40] **[`FieldLearner::section_kernel`] with several blocks a
    /// problem, the truth formed once.** Block `b` belongs to problem `owners[b]`; each problem's places of all its blocks
    /// are opened together at the truth (each carrying its truth letter whole), so one read gives the truth's `G` and faces
    /// for every block of it, and one material read its `∂G/∂θ`. Each block's proposal opens the same places, its own carrying
    /// their drawn letters and the others their truth, so `G′` and `face′` are read in the same structure as `G` and the
    /// Metropolis–Hastings ratio keeps its law. The deposit is `(1/T) Σ_b w_b [∂G/∂θ(truth_(owner b)) − ∂G/∂θ(e′_b)]`, two reads
    /// a block and two a problem. With one block a problem it is [`FieldLearner::section_kernel`]'s.
    pub fn section_kernel_grouped(&mut self, truth: &[Region], owners: &[usize], blocks: &[Vec<usize>], seed: u64, realization: &mut dyn FieldRealization) -> Result<KernelReceipt> {
        let f = &self.field;
        if !f.declaration.energy || f.scale.is_some() {
            return refuse("a kernel section of a field without one energy");
        }
        if truth.is_empty() || blocks.is_empty() || owners.len() != blocks.len() || owners.iter().any(|&o| o >= truth.len()) || blocks.iter().zip(owners).any(|(b, &o)| b.is_empty() || b.iter().any(|&t| t >= truth[o].classes.len() || truth[o].unresolved[t])) {
            return refuse("a kernel section needs nonempty blocks of resolved places, each a problem's");
        }
        let alphabet = f.declaration.alphabet;
        let inverse = temperature_of(-f.theta[f.layout.face_temper], &f.fine)?;
        let (problems, n) = (truth.len(), blocks.len());
        let mix = |counter: u64| -> u64 {
            let mut z = seed.wrapping_add(counter.wrapping_mul(0x9E37_79B9_7F4A_7C15));
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        };
        let one = 1u32 << STATE_BITS;
        // Each problem's opened places: the union of its blocks.
        let mut union: Vec<Vec<usize>> = vec![Vec::new(); problems];
        for (b, &o) in blocks.iter().zip(owners) {
            union[o].extend_from_slice(b);
        }
        for u in &mut union {
            u.sort_unstable();
            u.dedup();
        }
        // A problem with its opened places open, each carrying `letter(t)` whole, and its classes with those letters.
        let opened = |p: usize, letter: &dyn Fn(usize) -> usize| -> (Vec<usize>, Vec<bool>, Vec<Option<Shares>>) {
            let mut classes = truth[p].classes.to_vec();
            let mut open = vec![false; classes.len()];
            let mut faces: Vec<Option<Shares>> = vec![None; classes.len()];
            for &t in &union[p] {
                classes[t] = letter(t);
                open[t] = true;
                faces[t] = Some(vec![(classes[t] as u32, one)]);
            }
            (classes, open, faces)
        };
        let at_truth: Vec<_> = (0..problems).map(|p| opened(p, &|t| truth[p].classes[t])).collect();
        let truth_views: Vec<Region> = at_truth.iter().map(|(c, o, fc)| Region { classes: c, unresolved: o, faces: fc, locked: o, echo: &[], domain: None, port: None }).collect();
        let (faces, g_truth) = realization.read_energy_faces(f, &truth_views)?;
        // Each block place's proposal drawn from its face at the truth.
        let mut proposals: Vec<Vec<usize>> = Vec::with_capacity(n);
        for s in 0..n {
            let o = owners[s];
            let mut drawn = Vec::with_capacity(blocks[s].len());
            for &t in &blocks[s] {
                let face = faces[o][t].as_ref().ok_or(TowerError::Refused("a kernel block place with no face"))?;
                let u = ((mix((s as u64) << 32 | t as u64) as u128) << 64 | mix(!((s as u64) << 32 | t as u64)) as u128) % face.total.max(1);
                let mut acc = 0u128;
                drawn.push((0..alphabet).find(|&c| {
                    acc += face.masses[c];
                    acc > u
                }).unwrap_or(truth[o].classes[t]));
            }
            proposals.push(drawn);
        }
        let at_proposal: Vec<_> = (0..n)
            .map(|s| {
                let o = owners[s];
                let letters: Vec<(usize, usize)> = blocks[s].iter().copied().zip(proposals[s].iter().copied()).collect();
                opened(o, &|t| letters.iter().find(|&&(p, _)| p == t).map_or(truth[o].classes[t], |&(_, a)| a))
            })
            .collect();
        let proposal_views: Vec<Region> = at_proposal.iter().map(|(c, o, fc)| Region { classes: c, unresolved: o, faces: fc, locked: o, echo: &[], domain: None, port: None }).collect();
        let (faces2, g_prop) = realization.read_energy_faces(f, &proposal_views)?;
        // Each block's `log₂ A` on 2^(−32) bits and its weight `min(1, A)` on 2^(−24).
        let mut weights = Vec::with_capacity(n);
        let mut log2_a = Vec::with_capacity(n);
        for s in 0..n {
            let o = owners[s];
            let mut log_a = release((g_truth[o] - g_prop[s]).checked_mul(inverse).ok_or(TowerError::Refused("a kernel's energy past its carrier"))?, MATERIAL_BITS);
            for (&t, &a) in blocks[s].iter().zip(&proposals[s]) {
                let (face, face2) = (faces[o][t].as_ref().ok_or(TowerError::Refused("a kernel block place with no face"))?, faces2[s][t].as_ref().ok_or(TowerError::Refused("a kernel block place with no face at its proposal"))?);
                log_a += ((face.code(a) as i128) - (face2.code(truth[o].classes[t]) as i128)) << (ENERGY_BITS - 20);
            }
            log2_a.push(log_a);
            let ell = log_a >> (ENERGY_BITS - MATERIAL_BITS);
            weights.push(if ell >= 0 {
                1i128 << MATERIAL_BITS
            } else if ell <= -((MATERIAL_BITS as i128 - 1) << MATERIAL_BITS) {
                0
            } else {
                temperature_of(ell as i32, &f.fine)?
            });
        }
        // The material covectors at each problem's truth and at each block's proposal, resolved.
        let resolved: Vec<Vec<bool>> = truth.iter().map(|r| vec![false; r.classes.len()]).collect();
        let mut both: Vec<Region> = (0..problems).map(|p| Region { classes: &at_truth[p].0, unresolved: &resolved[p], faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
        both.extend((0..n).map(|s| Region { classes: &at_proposal[s].0, unresolved: &resolved[owners[s]], faces: &[], locked: &[], echo: &[], domain: None, port: None }));
        let reads = realization.read_energy_material(f, &both)?;
        let (mut g_same, mut g_gap) = (0usize, 0i128);
        for (i, read) in reads.iter().enumerate() {
            let g_faces = if i < problems { g_truth[i] } else { g_prop[i - problems] };
            g_same += usize::from(g_faces == read.1);
            g_gap = g_gap.max((g_faces - read.1).abs());
        }
        let g_agree = (g_same, reads.len());
        const OVER: &str = "a kernel covector past its 128-bit carrier";
        let families = f.families_all();
        let material = f.material_len();
        // Each state's `D_s/T = (∂G/∂θ(truth) − ∂G/∂θ′)/T` on the families' natural grains (2^(−40) a material family's, 2^(−24) a
        // face family's).
        let natural = |gt: &[i128], gp: &[i128]| -> Result<Vec<i128>> {
            if gt.len() != material || gp.len() != material {
                return refuse("a material covector of another length than the field's material");
            }
            let mut d = vec![0i128; material];
            for &(start, len, grain) in &families {
                for i in start..start + len {
                    let scaled = release((gt[i] - gp[i]).checked_mul(inverse).ok_or(TowerError::Refused(OVER))?, MATERIAL_BITS);
                    d[i] = if grain == MATERIAL_BITS { scaled } else { release(scaled, 40 - super::COVECTOR_BITS) };
                }
            }
            Ok(d)
        };
        let places = blocks.iter().map(Vec::len).sum();
        let moved = (0..n).map(|s| blocks[s].iter().zip(&proposals[s]).filter(|&(&t, &a)| a != truth[owners[s]].classes[t]).count()).sum();
        let weight = weights.iter().sum();
        let weight_square = weights.iter().map(|&w| release(w * w, MATERIAL_BITS)).sum();
        let (least, most) = (weights.iter().copied().min().unwrap_or(0), weights.iter().copied().max().unwrap_or(0));
        let whole = weights.iter().filter(|&&w| w == 1i128 << MATERIAL_BITS).count();
        let per_state: Vec<(usize, i128)> = blocks.iter().map(Vec::len).zip(weights.iter().copied()).collect();
        let states: Vec<Vec<i128>> = (0..n).map(|s| natural(&reads[owners[s]].0, &reads[problems + s].0)).collect::<Result<_>>()?;
        if self.newton {
            let newton = self.deposit_newton(&states, &weights)?;
            return Ok(KernelReceipt { states: n, places, moved, weight, weight_square, least, most, whole, deposited: newton.deposited, predicted: newton.predicted, transfer: newton.transfer, external: newton.external, per_state, log2_a, newton: Some(newton), by_family: Vec::new(), rates: Vec::new(), g_agree, g_gap, covector: Vec::new(), bands: Vec::new(), outside: Vec::new(), letter_counts: Vec::new(), surprise_bands: Vec::new(), kl_face: 0 });
        }
        // [the unified-theory reading of November 7, 06:26] The Newton terms read along the moments' direction before this section
        // moves them, beside the moments' own step.
        let newton = if self.newton_read {
            let mut direction = vec![0i128; material];
            for &(start, len, grain) in &families {
                for i in start..start + len {
                    direction[i] = deposit_step(self.first[i], self.second[i], grain, self.rate_bits);
                }
            }
            Some(self.newton_terms(&states, &weights, &direction)?)
        } else {
            None
        };
        let mut g = vec![0i128; material];
        for (d, &w) in states.iter().zip(&weights) {
            if w == 0 {
                continue;
            }
            for (v, &x) in g.iter_mut().zip(d) {
                *v += release(x.checked_mul(w).ok_or(TowerError::Refused(OVER))?, MATERIAL_BITS);
            }
        }
        // [definition; the unified-theory reading of November 7, 06:57] **The letters' temperature joins the deposit**: with
        // `T = 2^τ`, `∂l/∂τ = −ln 2 Σ_s w_s (G_s − G′_s)/T` from the energies already read, on `2^(−40)` a unit of `τ` (the
        // family's material grain). Held when `temper_learns` is off.
        if self.temper_learns {
            let mut gap = 0i128;
            for (s, &w) in weights.iter().enumerate() {
                gap += release((reads[owners[s]].1 - reads[problems + s].1).checked_mul(w).ok_or(TowerError::Refused(OVER))?, MATERIAL_BITS);
            }
            let over_t = release(gap.checked_mul(inverse).ok_or(TowerError::Refused(OVER))?, MATERIAL_BITS);
            let nats = release(over_t.checked_mul(crate::hnn::keyed_modes::ln2_face()).ok_or(TowerError::Refused(OVER))?, LN2_FACE_BITS);
            g[f.layout.face_temper] = -(nats << (40 - ENERGY_BITS));
        }
        // Each family's part of the step before priced on this section, before the deposit takes it.
        let transfers: Vec<Option<i64>> = match &self.last {
            Some(prev) => self.field.families_all().iter().map(|&fam| predicted_change_family(&self.field, &g, &prev.step, prev.halvings, fam)).collect(),
            None => vec![None; self.field.families_all().len()],
        };
        let raw = g.clone();
        let (deposited, predicted, transfer, external) = self.deposit(g)?;
        let predictions: Vec<Option<i64>> = match &self.last {
            Some(now) if deposited => self.field.families_all().iter().map(|&fam| predicted_change_family(&self.field, &raw, &now.step, now.halvings, fam)).collect(),
            _ => vec![None; transfers.len()],
        };
        let by_family = transfers.into_iter().zip(predictions).collect();
        let rates = self.family_rates.clone().unwrap_or_default();
        Ok(KernelReceipt { states: n, places, moved, weight, weight_square, least, most, whole, deposited, predicted, transfer, external, per_state, log2_a, newton, by_family, rates, g_agree, g_gap, covector: raw, bands: Vec::new(), outside: Vec::new(), letter_counts: Vec::new(), surprise_bands: Vec::new(), kl_face: 0 })
    }

    /// The averaged constitution's rate, `2^(−8)` a section (the second moments' own, theory November 7 21:58).
    const AVERAGE_RATE: u32 = 8;

    /// One section's move of the averaged constitution: `θ̄ ← toward(θ̄, θ, 8)` entry by entry on `θ`'s grain `2^(−8)` finer,
    /// opened at the live `θ`.
    pub fn average_section(&mut self) {
        let fine = Self::AVERAGE_RATE;
        match &mut self.average {
            Some(avg) if avg.len() == self.field.theta.len() => {
                for (a, &t) in avg.iter_mut().zip(&self.field.theta) {
                    *a = toward(*a as i128, (t as i128) << fine, Self::AVERAGE_RATE) as i64;
                }
            }
            _ => self.average = Some(self.field.theta.iter().map(|&t| (t as i64) << fine).collect()),
        }
    }

    /// The field read at the averaged constitution, each entry released to `θ`'s grain (the live field where none is kept).
    pub fn averaged_field(&self) -> Field {
        let mut field = self.field.clone();
        if let Some(avg) = self.average.as_ref().filter(|a| a.len() == field.theta.len()) {
            for (t, &a) in field.theta.iter_mut().zip(avg) {
                *t = release(a as i128, Self::AVERAGE_RATE) as i32;
            }
        }
        field
    }

    /// [definition; the unified-theory reading of November 7, 20:29, law (D)] **The deposit against each place's whole
    /// conditional**: at each block place `t` of a problem, every letter `v` of the alphabet is put at `t` with the rest at the
    /// truth, and one material read gives each configuration's `G(x_v)` and `∂G/∂θ(x_v)` (the two relaxations a state read one
    /// `G`, so the material read's `G` is the enumerated read's). The place's conditional `p(v) ∝ 2^(−G(x_v)/T)` (each weight on
    /// `2^(−24)` through the exponential's navigator, released to zero below `2^(−23)` as the kernel's) weighs the deposit
    /// `(1/T)(∂G/∂θ(t) − Σ_v p(v) ∂G/∂θ(x_v)) = (1/T) Σ_v p(v)(∂G/∂θ(t) − ∂G/∂θ(x_v))`, and the letters' temperature takes
    /// `G(t) − E_p G`. No proposal and no coin: it is the pseudo-likelihood's gradient at that place, and it rests where the
    /// held read's code is lowest, where the kernel's rest weighs each letter by `min(q(v)/p(v), q′(t)/p(t))`. The places are
    /// read a chunk at a time, so a section's configurations never stand together. The receipt reads as the kernel's, with
    /// each place a state: `weight` the truth's conditional probability `p(t)` on `2^(−24)`, `whole` the places whose truth is
    /// the conditional's mode, `log2_a` each `log₂ p(t)` on `2^(−32)`, nothing moved.
    pub fn section_conditional(&mut self, truth: &[Region], owners: &[usize], blocks: &[Vec<usize>], realization: &mut dyn FieldRealization) -> Result<KernelReceipt> {
        let shifts: Vec<Vec<u32>> = blocks.iter().map(|b| vec![0; b.len()]).collect();
        self.section_conditional_weighed(truth, owners, blocks, &shifts, None, realization)
    }

    /// [definition; the unified-theory reading of November 7, 21:08] **The places chosen by what is left of their news**: the
    /// deposit at a place is `(1 − p(t))(∂G/∂θ(t) − the other letters' p-mean)`, so what the field already predicts cancels (a
    /// static flux induces nothing). Each problem's block places are read once at the truth, open and carrying their letters
    /// whole (one faces read a problem), and each place takes the band `k = ⌊−log₂(1 − q(t))⌋` of its face's truth share
    /// `q(t)`, held to `0..=top`. A place is spent on its beat, when the lap's count agrees with the place's phase (a key of
    /// its problem `ids[o]` and position) modulo `2^k`, and its every covector (material, temperature) is weighed by `2^k`,
    /// so over `2^k` laps it carries its whole weight: the expectation is the full conditional sum and its rest the held code's,
    /// news not spent now carried, never dropped. A deposit spreads through `θ` and lowers coupled places' surprise before they
    /// are reached; their next read climbs a band. The receipt's `bands` are the counts of counts.
    #[allow(clippy::too_many_arguments)]
    pub fn section_conditional_beat(&mut self, truth: &[Region], owners: &[usize], blocks: &[Vec<usize>], ids: &[u64], lap: u64, top: u32, realization: &mut dyn FieldRealization) -> Result<KernelReceipt> {
        let f = &self.field;
        if ids.len() != truth.len() || blocks.len() != owners.len() || owners.iter().any(|&o| o >= truth.len()) {
            return refuse("a beat section needs one key a problem and an owner a block");
        }
        let problems = truth.len();
        let one = 1u32 << STATE_BITS;
        let mut union: Vec<Vec<usize>> = vec![Vec::new(); problems];
        for (b, &o) in blocks.iter().zip(owners) {
            union[o].extend_from_slice(b);
        }
        let opened: Vec<(Vec<bool>, Vec<Option<Shares>>)> = (0..problems)
            .map(|p| {
                let sites = truth[p].classes.len();
                let mut open = vec![false; sites];
                let mut faces: Vec<Option<Shares>> = vec![None; sites];
                for &t in &union[p] {
                    if t < sites {
                        open[t] = true;
                        faces[t] = Some(vec![(truth[p].classes[t] as u32, one)]);
                    }
                }
                (open, faces)
            })
            .collect();
        let views: Vec<Region> = (0..problems).map(|p| Region { classes: truth[p].classes, unresolved: &opened[p].0, faces: &opened[p].1, locked: &opened[p].0, echo: &[], domain: None, port: None }).collect();
        let (faces, _) = realization.read_energy_faces(f, &views)?;
        let key = |id: u64, t: usize| -> u64 {
            let mut z = id.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (t as u64).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        };
        let mut bands = vec![(0usize, 0usize); top as usize + 1];
        let (mut kept_blocks, mut kept_owners, mut kept_shifts) = (Vec::new(), Vec::new(), Vec::new());
        for (b, &o) in blocks.iter().zip(owners) {
            let (mut places, mut shifts) = (Vec::new(), Vec::new());
            for &t in b {
                let face = faces[o].get(t).and_then(Option::as_ref).ok_or(TowerError::Refused("a beat place with no face at the truth"))?;
                let (m, total) = (face.masses[truth[o].classes[t]], face.total.max(1));
                let rest = total - m.min(total);
                // The largest `k` with `2^k (1 − q) ≤ 1`, held to `top`.
                let mut k = 0u32;
                while k < top && rest << (k + 1) <= total {
                    k += 1;
                }
                bands[k as usize].0 += 1;
                if lap & ((1u64 << k) - 1) == key(ids[o], t) & ((1u64 << k) - 1) {
                    bands[k as usize].1 += 1;
                    places.push(t);
                    shifts.push(k);
                }
            }
            if !places.is_empty() {
                kept_blocks.push(places);
                kept_owners.push(o);
                kept_shifts.push(shifts);
            }
        }
        if kept_blocks.is_empty() {
            let rates = self.family_rates.clone().unwrap_or_default();
            return Ok(KernelReceipt { states: 0, places: 0, moved: 0, weight: 0, weight_square: 0, least: 0, most: 0, whole: 0, deposited: false, predicted: None, transfer: None, external: None, per_state: Vec::new(), log2_a: Vec::new(), newton: None, by_family: Vec::new(), rates, g_agree: (0, 0), g_gap: 0, covector: Vec::new(), bands, outside: Vec::new(), letter_counts: Vec::new(), surprise_bands: Vec::new(), kl_face: 0 });
        }
        let mut receipt = self.section_conditional_weighed(truth, &kept_owners, &kept_blocks, &kept_shifts, None, realization)?;
        receipt.bands = bands;
        Ok(receipt)
    }

    /// [`FieldLearner::section_conditional`] with each place's covectors weighed by `2^shifts[b][i]`.
    /// [definition; the unified-theory reading of November 7, 22:08] **The letters' coin**: [`FieldLearner::section_conditional`]
    /// with every letter's energy read forward only (its `G` is the material read's), so each place's conditional `p` is whole,
    /// and the reverse run only for the letters a coin keeps: letter `v` with chance `2^(−k_v)`, `k_v = max(0, ⌈log₂(τ/p(v))⌉)`
    /// for `τ = 2^(−tau_bits)`, on a coin keyed by `key`, the place and the letter, its covector weighed by `2^(k_v)`. The
    /// covector's expectation is the full conditional's, so the rest is the held code's; the letters' temperature reads every
    /// letter's `G`. With `τ` at or below every nonzero `p(v)` every letter is kept at weight one and the section is
    /// [`FieldLearner::section_conditional`]'s bit for bit.
    pub fn section_conditional_coin(&mut self, truth: &[Region], owners: &[usize], blocks: &[Vec<usize>], tau_bits: u32, key: u64, realization: &mut dyn FieldRealization) -> Result<KernelReceipt> {
        let shifts: Vec<Vec<u32>> = blocks.iter().map(|b| vec![0; b.len()]).collect();
        self.section_conditional_weighed(truth, owners, blocks, &shifts, Some((tau_bits, key)), realization)
    }

    fn section_conditional_weighed(&mut self, truth: &[Region], owners: &[usize], blocks: &[Vec<usize>], shifts: &[Vec<u32>], coin: Option<(u32, u64)>, realization: &mut dyn FieldRealization) -> Result<KernelReceipt> {
        let f = &self.field;
        if !f.declaration.energy || f.scale.is_some() {
            return refuse("a conditional section of a field without one energy");
        }
        if self.newton {
            return refuse("a conditional section deposits through the moments, not the Newton step");
        }
        if truth.is_empty() || blocks.is_empty() || owners.len() != blocks.len() || owners.iter().any(|&o| o >= truth.len()) || blocks.iter().zip(owners).any(|(b, &o)| b.is_empty() || b.iter().any(|&t| t >= truth[o].classes.len() || truth[o].unresolved[t])) {
            return refuse("a conditional section needs nonempty blocks of resolved places, each a problem's");
        }
        let alphabet = f.declaration.alphabet;
        let inverse = temperature_of(-f.theta[f.layout.face_temper], &f.fine)?;
        const OVER: &str = "a conditional covector past its 128-bit carrier";
        let families = f.families_all();
        let material = f.material_len();
        let natural = |gt: &[i128], gv: &[i128]| -> Result<Vec<i128>> {
            if gt.len() != material || gv.len() != material {
                return refuse("a material covector of another length than the field's material");
            }
            let mut d = vec![0i128; material];
            for &(start, len, grain) in &families {
                for i in start..start + len {
                    let scaled = release((gt[i] - gv[i]).checked_mul(inverse).ok_or(TowerError::Refused(OVER))?, MATERIAL_BITS);
                    d[i] = if grain == MATERIAL_BITS { scaled } else { release(scaled, 40 - super::COVECTOR_BITS) };
                }
            }
            Ok(d)
        };
        if shifts.len() != blocks.len() || shifts.iter().zip(blocks).any(|(s, b)| s.len() != b.len()) {
            return refuse("a weighed conditional section needs one shift a place");
        }
        let places: Vec<(usize, usize)> = blocks.iter().zip(owners).flat_map(|(b, &o)| b.iter().map(move |&t| (o, t))).collect();
        let place_shift: Vec<u32> = shifts.iter().flatten().copied().collect();
        let resolved: Vec<Vec<bool>> = truth.iter().map(|r| vec![false; r.classes.len()]).collect();
        // The faces at the truth, each problem's places open carrying their letters whole: one read a problem (theory 21:44).
        let one = 1u32 << STATE_BITS;
        let opened: Vec<(Vec<bool>, Vec<Option<Shares>>)> = (0..truth.len())
            .map(|p| {
                let sites = truth[p].classes.len();
                let (mut open, mut carried) = (vec![false; sites], vec![None; sites]);
                for &(o, t) in places.iter().filter(|&&(o, _)| o == p) {
                    open[t] = true;
                    carried[t] = Some(vec![(truth[o].classes[t] as u32, one)]);
                }
                (open, carried)
            })
            .collect();
        let views: Vec<Region> = (0..truth.len()).map(|p| Region { classes: truth[p].classes, unresolved: &opened[p].0, faces: &opened[p].1, locked: &opened[p].0, echo: &[], domain: None, port: None }).collect();
        let (truth_faces, _) = realization.read_energy_faces(f, &views)?;
        let mut outside = Vec::with_capacity(places.len());
        let (mut letter_counts, mut surprise_bands, mut kl_face) = (vec![0i128; alphabet], vec![0usize; 17], 0i128);
        let mut g = vec![0i128; material];
        // `Σ_places Σ_v p(v)(G(t) − G(x_v))` on 2^(−32): the letters' temperature's operand.
        let mut gap = 0i128;
        let (mut weight, mut weight_square, mut least, mut most, mut whole) = (0i128, 0i128, i128::MAX, 0i128, 0usize);
        let mut per_state = Vec::with_capacity(places.len());
        let mut log2_p = Vec::with_capacity(places.len());
        // [agent-inferred] Sixteen places a read: their `16·alphabet` configurations' covectors stand together (about 0.8 GB at
        // this field), never a section's.
        const CHUNK: usize = 16;
        for (c, chunk) in places.chunks(CHUNK).enumerate() {
            let configs: Vec<Vec<usize>> = chunk
                .iter()
                .flat_map(|&(o, t)| {
                    (0..alphabet).map(move |v| {
                        let mut c = truth[o].classes.to_vec();
                        c[t] = v;
                        c
                    })
                })
                .collect();
            let regions: Vec<Region> = configs.iter().enumerate().map(|(i, c)| Region { classes: c, unresolved: &resolved[chunk[i / alphabet].0], faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
            // Each place's letters' energies and, where a letter's reverse is read, its material covector and its coin's `k`.
            let (energies, materials): (Vec<i128>, Vec<Option<(Vec<i128>, u32)>>) = match coin {
                None => {
                    let reads = realization.read_energy_material(f, &regions)?;
                    let g: Vec<i128> = reads.iter().map(|r| r.1).collect();
                    (g, reads.into_iter().map(|r| Some((r.0, 0u32))).collect())
                }
                Some((tau_bits, key)) => {
                    let asked: Vec<&[usize]> = configs.iter().map(Vec::as_slice).collect();
                    let g = realization.read_energies(f, &asked)?;
                    // The conditional a place, as below, to read each letter's coin.
                    let mut keep: Vec<Option<u32>> = vec![None; g.len()];
                    for (i, &(o, t)) in chunk.iter().enumerate() {
                        let gs = &g[i * alphabet..(i + 1) * alphabet];
                        let p = conditional_shares(gs, inverse, &f.fine)?;
                        let at = truth[o].classes[t];
                        let tau = 1i128 << (MATERIAL_BITS.saturating_sub(tau_bits.min(MATERIAL_BITS)));
                        for v in 0..alphabet {
                            if v == at {
                                keep[i * alphabet + v] = Some(0);
                                continue;
                            }
                            if p[v] == 0 {
                                continue;
                            }
                            // `k = ⌈log₂(τ / p)⌉`, zero where `p ≥ τ`.
                            let mut k = 0u32;
                            while (p[v] << k) < tau && k < 62 {
                                k += 1;
                            }
                            let place = (c * CHUNK + i) as u64;
                            let draw = { let mut z = key ^ place.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (v as u64).wrapping_mul(0xBF58_476D_1CE4_E5B9); z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9); z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB); z ^ (z >> 31) };
                            if k == 0 || draw & ((1u64 << k) - 1) == 0 {
                                keep[i * alphabet + v] = Some(k);
                            }
                        }
                    }
                    let kept: Vec<usize> = (0..g.len()).filter(|&j| keep[j].is_some()).collect();
                    let kept_regions: Vec<Region> = kept.iter().map(|&j| regions[j]).collect();
                    let reads = realization.read_energy_material(f, &kept_regions)?;
                    let mut materials: Vec<Option<(Vec<i128>, u32)>> = vec![None; g.len()];
                    for (&j, r) in kept.iter().zip(reads) {
                        materials[j] = Some((r.0, keep[j].unwrap_or(0)));
                    }
                    (g, materials)
                }
            };
            for (i, &(o, t)) in chunk.iter().enumerate() {
                let gs = &energies[i * alphabet..(i + 1) * alphabet];
                let reads = &materials[i * alphabet..(i + 1) * alphabet];
                let at = truth[o].classes[t];
                let lo = gs.iter().copied().min().unwrap_or(0);
                // Each letter's `log₂ w = −(G(x_v) − G_min)/T` on 2^(−32), and its weight on 2^(−24).
                let logs: Vec<i128> = gs.iter().map(|&gv| (lo - gv).checked_mul(inverse).map(|x| release(x, MATERIAL_BITS)).ok_or(TowerError::Refused(OVER))).collect::<Result<_>>()?;
                let w: Vec<i128> = logs
                    .iter()
                    .map(|&l| {
                        let ell = l >> (ENERGY_BITS - MATERIAL_BITS);
                        if ell >= 0 {
                            Ok(1i128 << MATERIAL_BITS)
                        } else if ell <= -((MATERIAL_BITS as i128 - 1) << MATERIAL_BITS) {
                            Ok(0)
                        } else {
                            temperature_of(ell as i32, &f.fine)
                        }
                    })
                    .collect::<Result<_>>()?;
                let z: i128 = w.iter().sum();
                let p: Vec<i128> = w.iter().map(|&x| div_nearest(x << MATERIAL_BITS, z.max(1))).collect();
                let mt = &reads[at].as_ref().ok_or(TowerError::Refused("a conditional place whose truth was not read"))?.0;
                // The place's beat weight `2^k` (one where every place is read).
                let k = place_shift[c * CHUNK + i];
                for v in 0..alphabet {
                    if v == at || p[v] == 0 {
                        continue;
                    }
                    let pv = p[v] << k;
                    // The temperature reads every letter's `G`; the material only the letters whose reverse a coin kept.
                    gap += release((gs[at] - gs[v]).checked_mul(pv).ok_or(TowerError::Refused(OVER))?, MATERIAL_BITS);
                    if let Some((mv, kv)) = &reads[v] {
                        let weighed = pv << kv;
                        for (acc, &x) in g.iter_mut().zip(&natural(mt, mv)?) {
                            *acc += release(x.checked_mul(weighed).ok_or(TowerError::Refused(OVER))?, MATERIAL_BITS);
                        }
                    }
                }
                for (v, &pv) in p.iter().enumerate() {
                    letter_counts[v] += if v == at { (1i128 << MATERIAL_BITS) - pv } else { -pv };
                }
                if let Some(face) = truth_faces[o].get(t).and_then(Option::as_ref) {
                    let (m, total) = (face.masses[at], face.total.max(1));
                    let rest = total - m.min(total);
                    let mut k = 0usize;
                    while k < 16 && rest << (k + 1) <= total {
                        k += 1;
                    }
                    surprise_bands[k] += 1;
                    // KL(p ‖ face) in bits on 2^(−32): Σ_v p(v)(log₂ p(v) + code_face(v)), each log₂ p(v) = logs[v] − log₂ z.
                    let log2_z = super::log2_reading_at(z.max(1) as u128, ENERGY_BITS) - ((MATERIAL_BITS as i128) << ENERGY_BITS);
                    for (v, &pv) in p.iter().enumerate() {
                        if pv > 0 {
                            let log2_p = logs[v] - log2_z;
                            kl_face += release(pv * (log2_p + ((face.code(v) as i128) << (ENERGY_BITS - 20))), MATERIAL_BITS);
                        }
                    }
                    let mut order: Vec<usize> = (0..alphabet).collect();
                    order.sort_by_key(|&v| (std::cmp::Reverse(face.masses[v]), v));
                    let beyond = |top: usize| -> i128 { order[top.min(alphabet)..].iter().map(|&v| p[v]).sum() };
                    outside.push([beyond(4), beyond(8), beyond(16)]);
                }
                let pt = p[at];
                (weight, weight_square, least, most) = (weight + pt, weight_square + release(pt * pt, MATERIAL_BITS), least.min(pt), most.max(pt));
                whole += usize::from(p.iter().all(|&x| x <= pt));
                per_state.push((1, pt));
                log2_p.push(logs[at] - (super::log2_reading_at(z.max(1) as u128, ENERGY_BITS) - ((MATERIAL_BITS as i128) << ENERGY_BITS)));
            }
        }
        if self.temper_learns {
            let over_t = release(gap.checked_mul(inverse).ok_or(TowerError::Refused(OVER))?, MATERIAL_BITS);
            let nats = release(over_t.checked_mul(crate::hnn::keyed_modes::ln2_face()).ok_or(TowerError::Refused(OVER))?, LN2_FACE_BITS);
            g[f.layout.face_temper] = -(nats << (40 - ENERGY_BITS));
        }
        let transfers: Vec<Option<i64>> = match &self.last {
            Some(prev) => self.field.families_all().iter().map(|&fam| predicted_change_family(&self.field, &g, &prev.step, prev.halvings, fam)).collect(),
            None => vec![None; self.field.families_all().len()],
        };
        let raw = g.clone();
        let (deposited, predicted, transfer, external) = self.deposit(g)?;
        let predictions: Vec<Option<i64>> = match &self.last {
            Some(now) if deposited => self.field.families_all().iter().map(|&fam| predicted_change_family(&self.field, &raw, &now.step, now.halvings, fam)).collect(),
            _ => vec![None; transfers.len()],
        };
        let by_family = transfers.into_iter().zip(predictions).collect();
        let rates = self.family_rates.clone().unwrap_or_default();
        let n = places.len();
        Ok(KernelReceipt { states: n, places: n, moved: 0, weight, weight_square, least, most, whole, deposited, predicted, transfer, external, per_state, log2_a: log2_p, newton: None, by_family, rates, g_agree: (0, 0), g_gap: 0, covector: raw, bands: Vec::new(), outside, letter_counts, surprise_bands, kl_face })
    }

    /// [definition; agent-inferred, November 3, the tower record] **The learner grown in scale**: its field grown in scale
    /// ([`Field::scaled_up`], the key stream read on from the learner's drawn bytes), its moments kept on the fine field's
    /// material and opened at zero on the packets' field's and the glue's, which every coordinate opens at its own first
    /// nonzero covector.
    pub fn scaled_up(&self, period: usize, split: usize, declaration: FieldDeclaration, keys: &[u8]) -> Result<Self> {
        let (field, drawn) = self.field.scaled_up(period, split, declaration, keys, self.drawn)?;
        let len = field.material_len();
        let (mut first, mut second) = (self.first.clone(), self.second.clone());
        first.resize(len, 0);
        second.resize(len, 0);
        Ok(Self { field, first, second, rate_bits: self.rate_bits, drawn, laps: self.laps, held: None, read_held: self.read_held, newton: self.newton, newton_read: self.newton_read, first_rate: self.first_rate, second_rate: self.second_rate, family_rates: None, temper_learns: false, family_transfer: Vec::new(), family_price: Vec::new(), last: None, average: None })
    }

    /// [measurement; agent-inferred, November 3, §16.31] **Each family's step coherence**: over the family's entries, `Σ |m|`
    /// and `Σ √v` of the covector's two moments, so `Σ|m| / Σ√v` is near one where the family's covector keeps its sign
    /// from section to section (its step is driven) and near zero where its signs cancel (its step is noise). A reading only.
    pub fn step_coherence(&self) -> Vec<(usize, u128, u128)> {
        self.field
            .families_all()
            .iter()
            .map(|&(start, len, _)| {
                let m: u128 = self.first[start..start + len].iter().map(|v| v.unsigned_abs()).sum();
                let v: u128 = self.second[start..start + len].iter().map(|v| v.unsigned_abs().isqrt()).sum();
                (len, m, v)
            })
            .collect()
    }

    /// The learner as text: its head line (the held step's halvings, or `-`), the field, each
    /// moment on one line, then the held step on one line when one is held.
    pub fn to_text(&self) -> String {
        let join = |v: &[i128]| v.iter().map(i128::to_string).collect::<Vec<_>>().join(" ");
        let (held, step) = match &self.held {
            Some(h) => (h.halvings.to_string(), format!("{}\n", join(&h.step))),
            None => ("-".to_string(), String::new()),
        };
        // [definition; the unified-theory reading of November 7, 07:24] Each family's length and its two averages are carried,
        // so a continued learner keeps the lengths its families read.
        let lengths = match &self.family_rates {
            Some(rates) => format!("family-lengths {}\n", join(&rates.iter().zip(&self.family_transfer).zip(&self.family_price).flat_map(|((&r, &t), &p)| [r, t, p]).collect::<Vec<_>>())),
            None => String::new(),
        };
        let average = match &self.average {
            Some(avg) => format!("average {}\n", avg.iter().map(i64::to_string).collect::<Vec<_>>().join(" ")),
            None => String::new(),
        };
        format!("hnn-field-learner-v3 {} {} {} {held}\n{}{}\n{}\n{step}{lengths}{average}", self.rate_bits, self.drawn, self.laps, self.field.to_text(), join(&self.first), join(&self.second))
    }

    pub fn from_text(text: &str) -> Result<Self> {
        let mut lines = text.lines();
        let head: Vec<&str> = lines.next().unwrap_or("").split(' ').collect();
        if head.len() != 5 || head[0] != "hnn-field-learner-v3" {
            return refuse("a learner's head line that is not hnn-field-learner-v3");
        }
        let rate_bits = head[1].parse::<u32>().map_err(|_| TowerError::Refused("a learner's rate that is not a count"))?;
        let drawn = head[2].parse::<usize>().map_err(|_| TowerError::Refused("a learner's drawn keys that are not a count"))?;
        let laps = head[3].parse::<u64>().map_err(|_| TowerError::Refused("a learner's laps that are not a count"))?;
        let mut lines = lines.peekable();
        let field = Field::from_lines(&mut lines)?;
        let first = read_numbers::<i128>(lines.next())?;
        let second = read_numbers::<i128>(lines.next())?;
        if first.len() != field.material_len() || second.len() != field.material_len() {
            return refuse("a learner's moments that are not its field's length");
        }
        let held = match head[4] {
            "-" => None,
            h => {
                let halvings = h.parse::<u32>().map_err(|_| TowerError::Refused("a learner's held halvings that are not a count"))?;
                let step = read_numbers::<i128>(lines.next())?;
                if step.len() != field.material_len() {
                    return refuse("a learner's held step that is not its field's length");
                }
                Some(HeldStep { step, halvings })
            }
        };
        let families = field.families_all().len();
        let lengths_line = match lines.peek() {
            Some(l) if l.starts_with("family-lengths ") => lines.next(),
            _ => None,
        };
        let (family_rates, family_transfer, family_price) = match lengths_line.and_then(|l| l.strip_prefix("family-lengths ")) {
            Some(rest) => {
                let v = read_numbers::<i128>(Some(rest))?;
                if v.len() != 3 * families {
                    return refuse("a learner's family lengths that are not three a family");
                }
                (Some(v.iter().step_by(3).copied().collect()), v.iter().skip(1).step_by(3).copied().collect(), v.iter().skip(2).step_by(3).copied().collect())
            }
            None => (None, Vec::new(), Vec::new()),
        };
        let average = match lines.next().and_then(|l| l.strip_prefix("average ")) {
            Some(rest) => {
                let v = read_numbers::<i64>(Some(rest))?;
                if v.len() != field.theta.len() {
                    return refuse("a learner's averaged constitution that is not its field's length");
                }
                Some(v)
            }
            None => None,
        };
        Ok(Self { field, first, second, rate_bits, read_held: held.is_some(), newton: false, newton_read: false, first_rate: FIRST_RATE, second_rate: SECOND_RATE, family_rates, temper_learns: false, family_transfer, family_price, drawn, laps, held, last: None, average })
    }
}

mod energy;
pub mod moment;
mod scale;
pub use energy::{EnergyPairKinds, EnergyRead, EnergySquare, EnergyTangentRead, SquareCorners, ENERGY_BITS, FIRST_HALVINGS, MOST_HALVINGS};
pub use scale::Scale;

#[cfg(test)]
mod tests;

/// [definition; §16.47] The octave of a distance `d ≥ 1` from the question: `⌊log₂ d⌋`, so octave `j` holds `[2^j, 2^(j+1))`.
/// [definition; agent-inferred, November 6, the unified-theory reading of 07:21] **One end, one draw, conditioned on the room**
/// ([`Field::sample_runs`] with `one_end`): `room`'s faces at the release's first read, place by place, and `u` on `2^(−32)`; the
/// length is the places before the first whose void mass passes `u M(R)`, `M(R)` the largest void mass over the room (the
/// running maximum's last value), read exactly as `m_∅(t) T_R 2^32 > u m_R T_t` on 256-bit products; the room's extent where
/// none passes (none where no place carries void mass).
pub fn one_end_length(room: &[Option<&TowerFace>], void: usize, u: u128) -> usize {
    let wide = crate::compression::landmark::context::wide_mul;
    let Some(top) = room.iter().flatten().copied().reduce(|a, b| if wide(b.masses[void], a.total) > wide(a.masses[void], b.total) { b } else { a }) else { return room.len() };
    room.iter().position(|f| f.is_some_and(|f| wide(f.masses[void] << 32, top.total) > wide(u * top.masses[void], f.total))).unwrap_or(room.len())
}

pub fn octave_of(d: usize) -> u32 {
    usize::BITS - 1 - d.leading_zeros()
}

/// A face restricted to the letters, the void's mass removed (`None` where no letter has mass): the face a place before an
/// answer's last letter is drawn from ([`Field::release`]).
pub fn letters_face(face: &TowerFace, void: usize) -> Option<TowerFace> {
    let total = face.total - face.masses[void];
    (total > 0).then(|| TowerFace { masses: face.masses.iter().enumerate().map(|(c, &m)| if c == void { 0 } else { m }).collect(), total })
}

/// [definition; agent-inferred, November 6] A face's varentropy `Σ_a p(a) (−log₂ p(a))² − H²`, the spread of a draw's
/// code about the entropy it expects, on `2^(−40)` bits² ([`Field::release`]'s rest).
pub fn varentropy(face: &TowerFace) -> i128 {
    let second: u128 = face.masses.iter().enumerate().filter(|&(_, &m)| m > 0).map(|(a, &m)| m * (face.code(a) as u128).pow(2)).sum();
    let h = entropy(face);
    div_nearest(second as i128, face.total as i128) - h * h
}

/// [definition; §16.47] A face's entropy `Σ_a p(a) (−log₂ p(a))` on the codes' `2^(−20)` bits, each class's code
/// ([`TowerFace::code`]) weighed by its mass over the total and the sum released once at its nearest.
pub fn entropy(face: &TowerFace) -> i128 {
    let sum: i128 = face.masses.iter().enumerate().filter(|&(_, &m)| m > 0).map(|(a, &m)| m as i128 * face.code(a) as i128).sum();
    div_nearest(sum, face.total as i128)
}
