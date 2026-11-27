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
//! current    y_i = conj(U_i) ⊙ Σ_(j∈S_i) e_ij D(|i−j|) ṽ_j / Σ_(j∈S_i) e_ij (one exact series, released once),   x ← x + O y + b_o
//! pair       r̂'_t = x_t / ‖x_t‖_rms,   a_t = W_a r̂'_t + b_a,   b_t = W_b r̂'_t + b_b,   x_t ← x_t + W_c (a_t · b_(s(t))) + b_c
//!            s(t) the site's strand mate, t − 1 at an even contact and t + 1 at an odd (§16.34)   complex pairs along the strand
//! triad      α_t, β_t, γ_t = (A, B, G) r̂'_t + biases,   p_k(t) = α_k(t) β_k(t−1),   c^T_k(t) = p_k(t) γ_k(t+1),   x_t ← x_t + W_c c_t + W_T c^T_t + b_c
//!            at a site with both strand mates, one sum released once (J triads, the triad record §3)   the junction's three
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
//! temperature one ([`crate::coupling::coupling_code`]): an unused place writes the void, and the covector is
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
//! ([`Declaration::score_shift`]; the share is the gaps', `p_* = (1 + Σ_(j≠*) 2^(−(z_* − z_j)))^(−1)`,
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
//! operands that produced each carrier, held from the forward). The deposit is the tower's two moments of the covector,
//! and the step deposits at its size, `m/(⌊√v⌋ + 1)` at `2^(−rate)`: at most about 4.2 times its rate, by Cauchy–Schwarz
//! over the moments' rates `2^(−3)` and `2^(−8)` (agent-inferred). No reread decides it (Brandon, November 5: the step
//! fluxes). What a step does is priced, never certified: predicted on its own section (`Receipt::predicted`), at
//! first order on the next section's covector (`Receipt::transfer`), and before this section's covector moves the
//! moments (`Receipt::external`). History, kept as history ([`Learner`]): from November 1 the step was
//! certified on the section's own regions (by the products of their faces where every weight is one, by partition of
//! their readings where one is not, on the codes' grain where a port is read) and halved until it was certified or moved
//! nothing, then held and read on the next section's regions, which it was not fit on, and halved again or refused where
//! it coded them higher (the tower's acceptance 77); the held read was set aside on November 3 and stands since as a
//! declared comparison only (`read_held`, `false`); the certificate itself was retired on November 5.
//!
//! [definition; agent-inferred, November 3, §16.27] **The writer is the training clock run backwards**
//! ([`Constitution::sample_realized`]): training reads a region whose open sites are a uniform state of a random reading
//! order; the writer opens every answer place beside the known question and resolves them in one keyed random order,
//! each drawn from its own face at temperature one on the read of the region as it stands, every place resolved before it
//! known. Every place is written; a place drawn as the void is the answer's boundary, and every place past it is the void
//! (§16.35: the void is the class past an answer's end, as training's states and the codec read it). Why (the field's code read end to end,
//! November 3): the release before it locked a place only where one class held a majority of its face and moved its front
//! only past locked places; text is uncertain at most places under any model, so it wrote the classes it was surest of
//! (runs of `0`, `<<`, `=`, `####`), each lock making its neighbour's lock likelier, and left the rest open.
//!
//! **Exact integers, grains declared.** Faces, charts, framed charts and currents on `2^(−16)`;
//! material on `2^(−24)`; frames and skins on `2^(−30)`; each row an exact series of its terms'
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

#[allow(unused_imports)]
use rayon::prelude::*;

pub use crate::width::*;
pub use crate::ratio::*;
pub use crate::declaration::*;
pub use crate::constitution::*;
pub use crate::region::*;
pub use crate::navigator::*;
pub use crate::contact::*;
pub use crate::carry::*;
pub use crate::face::*;
pub use crate::adjoint::*;
pub use crate::deposit::*;
pub use crate::release::*;
pub use crate::level::*;
pub use crate::realization::*;
pub use crate::learner::*;
pub use crate::ruler::*;

pub mod moment;
pub(crate) mod scale;
pub use scale::{bank_rotations, level_anchors, level_anchors_before, level_cut, level_cut_sided, strand_face_reads, strand_face_terms, strand_level_cut, StrandCut, level_declaration, level_isolation, level_section, level_split, LevelCut, Scale, LEVEL_HARMONICS};
#[cfg(test)]
mod tests;
