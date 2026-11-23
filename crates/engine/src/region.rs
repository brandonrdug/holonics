//! **A region: its support and its ports.**
//!
//! a site is known (resolved, carrying nothing), carried as a face (it opens on `Σ_a w_a E(a)`, its shares on `2^(−16)`) or open, and an
//! open site carrying nothing is silent on the strand; only definite sites (known or locked) are heard past the near field; a state of `K`
//! open sites among the `m` of its domain weighs its code `Σ_open −log₂ p̂` by `m/K`; a port `[s, n)` is read through its coupling (its
//! code on `2^(−20)` bits, each place's covector `p̂_i − r_i` on `2^(−24)`), at its boundary (`−log₂(1 − p̂_∅)` and `r_a = p̂_a/(1 − p̂_∅)`
//! at a letter place, `−log₂ p̂_∅` past the target) or on its letters off the void (`−log₂(m_a/(T − m_∅))`); a carried site's read leaves
//! its own echo out, `z ← z − B ℓ`, `B` on `2^(−63)`; a region read as a known stream hears at every site only what stands before it
//!
//! Kind: gate, a site (a region's admission, its weight and its port's rows). Kernels: none of its own; the echo's are the contact's and
//! the moment's (`field_echo_trips`, `field_echo_apply`), and a port's rows are read on the host from the faces the card fetches
//! (`hnn/resident.rs`).
//! Lean: `HNN/SynchronousTwoCycle` (the echo).
//! Atlas: `tower.field-joint-code`, `tower.field-opening-boundary`; with owners in other modules, `tower.field-answer-port`,
//! `tower.field-echo`, `tower.field-room-cut`, `tower.region-known-stream`, `tower.region-past`, `tower.region-second`, `tower.region-strand`.
//! Records: `2026-11-01_THE_FIELD_DISPERSES…`, `2026-11-02_THE_COMPARISON_IS…`, `2026-11-18_THE_WRITERS_FRONTIER_IS…`,
//! `2026-11-18_EVERY_PLACE_OF_A_PASSAGE…`, `2026-11-18_THE_CODEC_THE_REGION…` (the first lines this header replaced). The derivations'
//! history is in the records; the items below keep their reasons.

use crate::codec::Codec;
use crate::field::Shares;

/// A training region: its classes, its unresolved sites, its carried faces and its locks (each
/// empty where none).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OwnedRegion {
    pub classes: Vec<usize>,
    pub unresolved: Vec<bool>,
    pub faces: Vec<Option<Shares>>,
    pub locked: Vec<bool>,
    /// Each carried site's echo (§15.3), empty where none.
    pub echo: Vec<Option<Echo>>,
    /// The sites its open ones were drawn from (§16.23, [`Region::domain`]).
    pub domain: Option<usize>,
    /// Its answer port (§16.24, [`Region::port`]): the first place, the void, the cells, and whether it is compared at
    /// its boundary (§16.47) rather than through its coupling.
    pub port: Option<(usize, usize, Vec<usize>, bool, Option<usize>, Option<Vec<bool>>)>,
    /// Whether its port cuts the room to its windows ([`Port::window`]).
    pub window: bool,
    /// Whether its port compares its open places on their letters off the void ([`Port::letters`]).
    pub letters: bool,
    /// Whether it is read as a known stream ([`Region::before`]).
    pub before: bool,
    /// Whether it is read by two streams ([`Region::strand`]).
    pub strand: bool,
    /// Whether its odd strand contacts and its circles from the right face the past ([`Region::past`]).
    pub past: bool,
    /// Whether its row of the site after reads the second site before ([`Region::second`]).
    pub second: bool,
    /// What its strand's open places are compared with ([`Region::targets`]); none where they are compared with the known stream.
    pub targets: Option<Vec<usize>>,
}

impl OwnedRegion {
    /// A region carrying no face and no lock.
    pub fn plain(classes: Vec<usize>, unresolved: Vec<bool>) -> Self {
        Self { classes, unresolved, faces: Vec::new(), locked: Vec::new(), echo: Vec::new(), domain: None, port: None, window: false, letters: false, before: false, strand: false, past: false, second: false, targets: None }
    }
}

/// A region as the field reads it.
pub fn view_of(region: &OwnedRegion) -> Region<'_> {
    Region { classes: &region.classes, unresolved: &region.unresolved, faces: &region.faces, locked: &region.locked, echo: &region.echo, domain: region.domain, port: region.port.as_ref().map(|(start, void, target, boundary, stop, heard)| Port { start: *start, void: *void, target, boundary: *boundary, stop: *stop, heard: heard.as_deref(), window: region.window, letters: region.letters }), before: region.before, strand: region.strand, past: region.past, second: region.second, targets: region.targets.as_deref() }
}

/// The regions as the field reads them.
pub fn views_of(regions: &[OwnedRegion]) -> Vec<Region<'_>> {
    regions.iter().map(view_of).collect()
}

/// A problem's region classes: the question and its line, the answer, then `void` to `length`.
pub fn region_classes(codec: &Codec, q: &[usize], a: &[usize], length: usize) -> Vec<usize> {
    let mut out: Vec<usize> = q.iter().chain(a).copied().collect();
    out.resize(length, codec.void());
    out
}

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use rayon::prelude::*;

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
    /// cells, never the void) by the coupling at temperature one ([`crate::coupling::coupling_code`]), an
    /// unused place writing `void`. `None` where every open site is compared at its own place.
    pub port: Option<Port<'a>>,
    /// [definition; the lead, November 18, the frontier record §6; `agent-inferred`] **A region read as a known stream**: every site hears only
    /// what stands before it (the tick under [`crate::contact::Sided::Before`]: the support's and the crowds' side, a still head's class count,
    /// the opening's and the moments' after rows, the odd strand contacts, the circles from the right; the region's first site meets no
    /// source), the level is not heard, the field reads it once, and its opening is compared as the retarded one
    /// ([`Constitution::cavity_forward_sided`]). A site's state is then a function of the symbols up to its own place, so a place's reading
    /// stands whatever follows it: the regime a writer is in at its frontier, and the known stream of a passage read by two streams
    /// ([`Constitution::strand_pass`]). Where the field reads twice, the one read stands for both in the section's mean
    /// ([`Constitution::returned`]). Unset is the law as it stood.
    pub before: bool,
    /// [definition; the lead, November 18, the frontier record §6; `agent-inferred`] **A passage read by two streams**
    /// ([`Constitution::strand_pass`]): the region's sites, every one known, are the known stream (each hearing only what stands before
    /// it, as under [`Region::before`]), and at every place past the first an open place of a second stream reads what stands before it
    /// and is compared with the symbol there at weight one. Its faces are the open places', one a place (none at the first), so one
    /// forward compares every place of the passage at its own frontier: the same bits, place for place, as the open last place of the
    /// region that ends there read as a known stream. The level is not heard and the field reads it once, its return standing for both
    /// reads where the field reads twice; the opening is compared as the retarded one. Refused where a site is open or carried, or the
    /// region has a port.
    pub strand: bool,
    /// [definition; the lead, November 18, the record of the two streams §9; `agent-inferred`] **The strand's odd contacts face the past**:
    /// in a region read one-sided ([`Region::before`], [`Region::strand`]) an odd plain contact's mate is the second site before (the two
    /// nearest places that have arrived are then a site's two mates, as the sites before and after are under the law), and a circle of
    /// odd contact is scanned from the left with its own gate and drive. Unset, an odd contact has no mate in such a region and its
    /// circle stays at rest. Why: on the two-stream line's state the plain contacts carry 0.99 nats to the frontier and the circles
    /// 0.46 (`read-far`'s settings `8` and `7`), and half of each stood idle in a one-sided stream. No meaning on a region of the law.
    pub past: bool,
    /// [definition; the lead, November 18, the record of the two streams §15; `agent-inferred`] **The row of the site after reads the
    /// second site before**: in a region read one-sided ([`Region::before`], [`Region::strand`]) a site's opening takes, with its own
    /// row and the row of the site before it (`E₋`), the row `E₊` of the second site before it, and the open place at a place the row
    /// of the second known site before its place, where unset `E₊` reads no site there (the site after has not arrived). Why: read on
    /// the line's states an open place holds the place before it at nine tenths as it opens (that row), the second place before at a
    /// half and the third at a fifth, and no tick carries a farther place in; the frontier binds about three places, and `E₊`'s
    /// entries, as many as `E₋`'s, stood idle in a one-sided stream. No meaning on a region of the law.
    pub second: bool,
    /// [definition; the lead, November 23; `agent-inferred`] **What a
    /// strand's open places are compared with**: in a passage read by two streams ([`Region::strand`]) the known stream is `classes`
    /// and the open place at each place is compared with `targets` there, one a site. Her own draft can then stand in the known stream
    /// while the passage's own symbols are what each place is compared with: each place is read from what she wrote before it and
    /// compared with what the passage holds (the draft world's arms, the record of November 23 on her drafts; Brandon's 19:49Z note says
    /// that grading her drafts against a passage is not play). None, the law as it stood: the open places are
    /// compared with the known stream's own symbols. Refused on a region that is not read by two streams. A target of [`UNCOMPARED`]
    /// leaves its place uncompared: it is read and returns nothing (an act's own places, where the world answers the act).
    pub targets: Option<&'a [usize]>,
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
    /// place and the places within `(NEAR − 1)·ticks` of a heard one; every other receiver meets no source that tick. A field with carry
    /// circles keeps the room whole ([`Declaration::room_window`]): a circle carries a place's state the whole strand inside one tick.
    pub window: bool,
    /// [definition; agent-inferred, November 6, the unified-theory reading of 11:49] **Compared on its letters off the void**: each
    /// open place of the port on its target's class within the letters, `−log₂(m_a/(T − m_∅))`, the release's own draw where the
    /// end is given (a place before the end draws from its face restricted to the letters), so the void logit takes no covector
    /// there; a resolved place carries no face and is not compared ([`letters_reading`]).
    pub letters: bool,
}

/// [definition; agent-inferred, November 3, §16.24] **A port's reading**: its coupling code on `2^(−20)` bits and each
/// place's covector `p̂_i − r_i` on the face covector's `2^(−24)` (the face's own shares less the target the coupling
/// places there), from the faces at its places (each `(masses, total)`). The host's return and the card's read the same
/// rows from the same faces.
pub fn port_reading(faces: &[(&[u128], u128)], port: &Port) -> Result<(Vec<Vec<i64>>, i64)> {
    use crate::coupling::TemperatureRefusal as Why;
    if port.boundary {
        return boundary_reading(faces, port);
    }
    if port.letters {
        return letters_reading(faces, port);
    }
    let read = crate::coupling::coupling_code(faces, port.void, port.target, None).map_err(|why| {
        TowerError::Refused(match why {
            Why::Short { .. } => "a port with more target cells than places",
            Why::VoidCell => "a port whose target holds the void",
            Why::Face => "a port's face that is empty or misses a class",
            Why::Released { .. } => "a port whose coupling's mass released to zero",
        })
    })?;
    let mut rows = Vec::with_capacity(faces.len());
    for ((masses, total), placed) in faces.iter().zip(&read.placed) {
        let mut row: Vec<i64> = masses.iter().map(|&m| (((m << crate::field::COVECTOR_BITS) + total / 2) / total) as i64).collect();
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
/// [`Port::letters`]'s reading: at each open place `i` (within the target) the covector `p̂_a/(1 − p̂_∅) − [a = target_i]` over the
/// letters on the face covector's `2^(−24)`, zero at the void, and the code `−log₂(m_(target_i)/(T − m_∅))` on `2^(−20)` bits; a
/// resolved place (an empty face) is not compared.
pub(crate) fn letters_reading(faces: &[(&[u128], u128)], port: &Port) -> Result<(Vec<Vec<i64>>, i64)> {
    let one = 1i64 << crate::field::COVECTOR_BITS;
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
        let mut row: Vec<i64> = masses.iter().map(|&m| (((m << crate::field::COVECTOR_BITS) + rest / 2) / rest) as i64).collect();
        row[port.void] = 0;
        row[port.target[i]] -= one;
        code += crate::field::face_code(masses[port.target[i]], rest);
        rows.push(row);
    }
    Ok((rows, code))
}

pub(crate) fn boundary_reading(faces: &[(&[u128], u128)], port: &Port) -> Result<(Vec<Vec<i64>>, i64)> {
    let one = 1i128 << crate::field::COVECTOR_BITS;
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
        let mut row: Vec<i64> = masses.iter().map(|&m| (((m << crate::field::COVECTOR_BITS) + total / 2) / total) as i64).collect();
        let void = row[port.void] as i128;
        if i < port.target.len() {
            let rest = one - void;
            for (a, slot) in row.iter_mut().enumerate() {
                if a != port.void {
                    *slot = if rest == 0 { 0 } else { fit64(-div_nearest(*slot as i128 * void, rest))? };
                }
            }
            code += crate::field::face_code(total - masses[port.void], total);
        } else {
            row[port.void] -= one as i64;
            code += crate::field::face_code(masses[port.void], total);
        }
        rows.push(row);
    }
    Ok((rows, code))
}

impl Region<'_> {
    /// [definition; agent-inferred, November 6, the unified-theory reading of 06:50, E] **The windows a cut room computes**
    /// ([`Port::window`]): every site before the port, the silent stretch's first place ([`Constitution::silent_stretch`]) and each
    /// heard open place, each with the `(NEAR − 1)·ticks` places on either side; none where the port does not cut its room.
    /// Why exact (the unified-theory reading of 06:50): a silent place is no one's far source, so in one tick a receiver hears
    /// past its near field only definite sources (the question, whole) and its crowds of them, and the near field and the
    /// strand's pair contact carry a place's state at most `NEAR − 1` places a tick. A heard place's face after `ticks` ticks
    /// therefore reads only its window, and a receiver outside every window reads, at worst, its window's edge, which is
    /// `(NEAR − 1)·ticks` places from it; the stretch's clock past its first place runs at that place's rate (one passage), so
    /// the clock at every far place is `τ_front + (t − front)κ` from a computed face. Backward, the covector of a heard face
    /// reaches at most `(NEAR − 1)` places a tick, so it meets no receiver outside its window, and the clock's return reaches
    /// the stretch's first place, whose window is computed. Not exact where blanks sit between arrivals (masks, writer
    /// states), whose clocks read each blank's own face: those regions keep their room whole. Nor where the field has carry circles,
    /// whose scan carries a place's state the whole strand in one tick: the forward asks [`Declaration::room_window`], which keeps
    /// those rooms whole.
    pub fn window(&self, ticks: usize) -> Option<Vec<bool>> {
        let port = self.port.filter(|p| p.window)?;
        let sites = self.classes.len();
        let reach = (NEAR - 1) * ticks;
        let mut out: Vec<bool> = (0..sites).map(|t| t < port.start).collect();
        let stretch = Constitution::silent_stretch(self);
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

/// [definition; the lead, November 23, an act answered in kind; `agent-inferred`] **A place read and not compared**: a target of a
/// passage read by two streams ([`Region::targets`]) that leaves its place out of the comparison. The place is read as every place is,
/// in its known stream and as an open place, and its face takes no covector and counts in no code. Why: in an act answered in kind the
/// act's own places are her draft, and a comparison there would deposit toward her own act (G169's drift) or against a passage that is
/// no function of it (the draft world, `receipt.unanswered-act-is-discounted`); the comparison stands at the world's answer alone, with
/// the act as known context (the formal thread's record of November 23, §3.1).
pub const UNCOMPARED: usize = usize::MAX;

/// [definition; agent-inferred, November 1] **A read leaves its own echo out** (the dispersing field's
/// §15.3): a site carried as a face is read through contacts both ways, so its face returns to it a
/// round trip later; the read it meets is its cavity field, `z ← z − B ℓ`, with `ℓ` the logits its
/// carried face was formed from and `B` its echo on `2^(−63)`, the round trip's share read on the read
/// that formed `ℓ` ([`ReadLogits::echo`]). Both are data: no covector passes through them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Echo {
    pub b: u64,
    pub logits: Vec<i64>,
}

impl Constitution {

    /// Whether `region` is read with every site hearing only what stands before it: its own word ([`Region::before`]), or a ruler's forward
    /// at `3` ([`Constitution::ruler_far`]).
    pub(crate) fn sided(&self, region: &Region) -> bool {
        region.before || region.strand || matches!(self.ruler_far, 3 | 6 | 7 | 8 | 9)
    }

    /// Whether `region`'s odd strand contacts and its circles from the right face the past ([`Region::past`]): its own word on a region
    /// read one-sided, or a ruler's forward at `9`.
    pub(crate) fn past(&self, region: &Region) -> bool {
        (region.past && (region.before || region.strand)) || self.ruler_far == 9
    }

    /// Whether `region`'s row of the site after reads the second site before ([`Region::second`]): its own word on a region read
    /// one-sided.
    pub(crate) fn second(&self, region: &Region) -> bool {
        region.second && (region.before || region.strand)
    }

    /// Whether `region`'s forward hears the level: a field with one, read under the law or a ruler's forward at `5`, the region no known
    /// stream; or a ruler's known stream that hears a level ([`Constitution::ruler_level`] at `4` or `5`).
    pub(crate) fn levelled(&self, region: &Region) -> bool {
        self.scale.is_some() && !region.before && !region.strand && (self.ruler_far < 3 || self.ruler_far == 5 || (self.ruler_far == 3 && self.ruler_level >= 4))
    }

    pub(crate) fn admit_region(&self, region: &Region) -> Result<()> {
        if region.classes.len() != region.unresolved.len() || region.classes.len() < 2 {
            return refuse("a region needs one class and one resolution a site, and two sites to meet");
        }
        // A triad's third leg is read at the site after (`triad_products`), which a known stream's site has not met; no one-sided triad is built.
        // [definition; the lead, November 22] A crossing triad's three legs stand at the site itself (`Declaration::crossing`), so the reason
        // does not reach it: a known stream reads a crossing triad as every other place does.
        if self.sided(region) && self.declaration.triads > 0 && !self.declaration.crossing {
            return refuse("a known stream on a field with triads, whose third leg is the site after");
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
            if port.start > region.classes.len() || (!port.boundary && !port.letters && region.unresolved[port.start..].iter().any(|&u| !u)) || (port.start..region.classes.len()).any(|t| region.locked.get(t).copied().unwrap_or(false)) {
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
    pub(crate) fn definite(region: &Region, t: usize) -> bool {
        (!region.unresolved[t] && Self::carried(region, t).is_none()) || region.locked.get(t).copied().unwrap_or(false)
    }

    /// The face a site is carried as, if any.
    pub(crate) fn carried<'r>(region: &'r Region, t: usize) -> Option<&'r Shares> {
        region.faces.get(t).and_then(Option::as_ref)
    }

    /// [definition; agent-inferred, November 3, §16.28] **An open site is silent on the strand**: unresolved and carrying
    /// no face, nothing has arrived there, so it adds nothing to any site's moment and its clock runs at the strand's own
    /// place (`κ = 1`). Its own opening (`E(∗)` with its neighbours' contact rows) is its own and stays.
    pub(crate) fn silent(region: &Region, t: usize) -> bool {
        region.unresolved[t] && Self::carried(region, t).is_none()
    }

    /// [definition; agent-inferred, November 5, the unified-theory reading of 21:07] **A silent stretch past the last arrival
    /// is one passage**: the first silent place past a region's last arrival (its last site that is not silent), or the
    /// region's length where none is. Past it every place runs the free clock at that place's rate (its expected duration
    /// from the tick before's face there, bare at the first tick), so a place `D` past the last arrival reads the clock
    /// `c_f + D κ₁`: nothing arrives there, and a per-blank rate would be the field's guesses about the stretch driving its
    /// own clock (near an uncertain end the faces split between the void and a byte and the clock races, §16.28). Stretches
    /// between two arrivals keep their per-blank rates.
    pub(crate) fn silent_stretch(region: &Region) -> usize {
        let sites = region.classes.len();
        (0..sites).rev().find(|&t| !Self::silent(region, t)).map_or(0, |last| last + 1)
    }

    /// A pass's port reading ([`port_reading`]) from the faces at the port's places.
    pub(crate) fn port_of(&self, pass: &Forward, port: &Port) -> Result<(Vec<Vec<i64>>, i64)> {
        port_reading(&port_faces(&pass.faces, port)?, port)
    }
}
