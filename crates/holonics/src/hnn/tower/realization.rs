//! **The section's pass and its realizations** (#404, #76).
//!
//! [definition; agent-inferred, October 25] A training section ([`TowerLearner::section_realized`])
//! reads its streams forward, returns their covector by the reverse scan, and rereads them under
//! each candidate deposit. The forward and the reverse are the section's heavy part and its only
//! part that is parallel by streams, cells and modes; the moments, the step and the certificate are
//! a few passes over the material. A [`PassRealization`] is the declared owner of the heavy part:
//!
//! ```text
//! forward(Θ, opening, classes, targets) = (faces, swell)       faces[s][i] = (2^(z_t − z_max), Σ_b 2^(z_b − z_max)), t the target
//! reverse(Θ, opening, classes, compared) = Σ_s g_s              the streams' covectors on each family's natural grain
//! carry(Θ, states, opening)                                     each stream's state after the read the section keeps
//! ```
//!
//! Every realization returns the host's bits: the same faces (the target's mass and the total, on
//! `2^(−62)`), the same summed covector and the same continuing states, so the certificate, the
//! deposit and the saved learner are the host's whatever realizes the pass. Integer sums are
//! associative, so a realization may sum the streams' covectors in any order and on any partition
//! (the module law "Exact integers, grains declared"). [`HostPass`] is the reference: the streams'
//! forwards and reverses in parallel on the host, exactly as the learner ran them before this
//! owner. A card realization reads the tower's material through [`ResidentLaw`], the families'
//! places, reaches, the gated moves' founded faces and the navigators' resident faces as one
//! section reads them, and refuses any declaration it does not carry.
//!
//! The forward is read twice a section: once at the opening ([`Slot::Opened`]), whose temporaries
//! the reverse reads (a realization may keep them or read them again; [`HostPass`] reads them
//! again), and once under each candidate deposit ([`Slot::Reread`]), which needs only its
//! faces and its continuing states.
use super::split::{PairedContacts, SplitRead};
use super::*;

/// Which forward of a section a read is: the opening read (whose temporaries the reverse reads),
/// the certificate's reread under a candidate deposit, or a reread on the ticks the opening read
/// took at each cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Slot {
    Opened,
    Reread,
    /// [agent-inferred, October 30] A reread whose clocked levels tick where the section's opening
    /// read ticked, cell by cell, the news phase still advancing by the reread's own codes: a
    /// run's declared reading of a refused step (record §16), kept as a reread is. Refused without
    /// a news clock or before an opening read.
    OpeningTicks,
}

/// What a section reads of one forward: per stream, per cell, the face compared at its target, `(the
/// target's mass, the total)` on `2^(−62)` (`None` where the place is compared with nothing), and,
/// for the opening read, the swell per level (`TowerLearner::swell`; empty for a reread). Under the
/// heading, per stream and per level, each tick's closure face `(e_jj, Σ_i e_ji)` on `2^(−62)`
/// (`Tower::join_heading`; empty without it).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassRead {
    pub faces: Vec<Vec<Option<(u128, u128)>>>,
    pub swell: Vec<[u64; 4]>,
    pub closures: Vec<Vec<Vec<(u128, u128)>>>,
}

impl PassRead {
    /// [definition; agent-inferred, October 27] **A realization's read, admitted**: one face at each
    /// compared place and none elsewhere, each in the domain of [`face_code`] (a positive total
    /// and a mass no greater than it; a lawful face's largest class adds `2^62` to its total, so its
    /// total is never zero). Every caller admits a realization's read before a code or the
    /// certificate reads it, so a realization that returns a face outside the domain is refused,
    /// never divided by.
    pub fn admitted(self, targets: &[Vec<Option<usize>>]) -> Result<PassRead> {
        let placed = self.faces.len() == targets.len() && self.faces.iter().zip(targets).all(|(f, t)| f.len() == t.len() && f.iter().zip(t).all(|(f, t)| f.is_some() == t.is_some()));
        if !placed {
            return Err(TowerError::Refused("a realization returned faces that are not one a compared place"));
        }
        if self.faces.iter().flatten().flatten().chain(self.closures.iter().flatten().flatten()).any(|&(m, t)| t == 0 || m > t) {
            return Err(TowerError::Refused("a realization returned a face with no total or a mass past its total"));
        }
        if !self.closures.is_empty() && self.closures.len() != self.faces.len() {
            return Err(TowerError::Refused("a realization returned closures that are not one a stream"));
        }
        Ok(self)
    }
}

/// [definition; agent-inferred, October 25] **A realization of the section's pass** (the module
/// header): the streams' forward, their summed covector and their continuing states, each the host's
/// bits.
pub trait PassRealization {
    /// The realization as it actually runs (the hardware law's report).
    fn realization(&self) -> String;

    /// Every stream's section read forward from its opening state; `targets[s][i]` is the class
    /// the face after `classes[s][i]` is compared with. The realization keeps the read in `slot`.
    fn forward(&mut self, tower: &Tower, opening: &[TowerState], classes: &[&[usize]], targets: &[Vec<Option<usize>>], slot: Slot) -> Result<PassRead>;

    /// The streams' covector summed, from the read kept in [`Slot::Opened`] (`Tower::reverse_joined`
    /// without a joined covector).
    fn reverse(&mut self, tower: &Tower, opening: &[TowerState], classes: &[&[usize]], compared: Option<&[&[Option<usize>]]>) -> Result<Vec<i128>>;

    /// The streams' covector summed with their split read on paired contacts (`split`'s module
    /// header), from the read kept in [`Slot::Opened`]. A realization that does not form the split
    /// read refuses; [`PassRealization::forms_split`] says so before any section is read.
    fn reverse_split(&mut self, tower: &Tower, opening: &[TowerState], classes: &[&[usize]], compared: Option<&[&[Option<usize>]]>, paired: &PairedContacts) -> Result<(Vec<i128>, SplitRead)> {
        let _ = (tower, opening, classes, compared, paired);
        Err(TowerError::Realization(format!("{} does not form the paired contacts' split read", self.realization())))
    }

    /// Whether [`PassRealization::reverse_split`] is carried.
    fn forms_split(&self) -> bool {
        false
    }

    /// Each stream's continuing state from the read kept in `slot`, its credit moved along it.
    fn carry(&mut self, tower: &Tower, states: &mut [TowerState], opening: &[TowerState], slot: Slot) -> Result<()>;

    /// Every stream's whole face at the last cell of the read kept in [`Slot::Opened`]: each
    /// class's mass and their total on `2^(−62)`, the face a release draws from.
    fn last_faces(&mut self) -> Result<Vec<TowerFace>>;

    /// Whether this realization carries `tower`'s law. A run reads it before any model work or
    /// output, so a law the realization does not carry is refused at the run's start, never at its
    /// first section.
    fn admit(&self, tower: &Tower) -> Result<()>;

    /// [agent-inferred, October 30] Every compared cell's face logits (the alphabet's entries on
    /// `2^(−16)` bits, before their largest is taken), stream by stream in the faces' order, read
    /// forward from the opening as a reread reads it. The read keeps nothing: neither slot's read
    /// nor any stream's state changes (the meeting form's read, `meeting`'s module header). A
    /// realization that does not read the logits refuses.
    fn logits(&mut self, tower: &Tower, opening: &[TowerState], classes: &[&[usize]], targets: &[Vec<Option<usize>>]) -> Result<Vec<i64>> {
        let _ = (tower, opening, classes, targets);
        Err(TowerError::Realization(format!("{} does not read the faces' logits", self.realization())))
    }
}

/// One stream's forward as the host keeps it between calls: its continuing state, its face after
/// its last class, and its cells only where the stream carries a passage credit, whose carry reads
/// every cell (`Tower::carry_credit`).
struct KeptStream {
    cells: Vec<Cell>,
    end: TowerState,
    last: Option<TowerFace>,
    /// Under a news clock, the opening read's ticks at each cell, every level's (empty for a
    /// reread), which [`Slot::OpeningTicks`] reads.
    ticks: Vec<Vec<u32>>,
}

type Kept = (Vec<KeptStream>, Reaches);

/// [definition; agent-inferred, October 27] **The host's realization**: each stream's forward and
/// reverse on its own thread, the streams' covectors summed over the threads' partition. It keeps
/// no cell between calls (except a credit-carrying stream's): its reverse reads each stream's
/// forward again from the opening, the same exact steps, so a section holds the cells of the
/// streams its threads are reading, not of every stream. Measured before this partition: the
/// 24-stream, four-level parity's host reference peaked at 1,673,124 KiB holding every stream's
/// cells, which projects to about 22.3 GB at 320 streams.
#[derive(Default)]
pub struct HostPass {
    opened: Option<Kept>,
    reread: Option<Kept>,
    /// Whether the opening read is the last forward. The host keeps both reads, but a card keeps
    /// one frame of temporaries, which a reread replaces; the host refuses as the card does, so a
    /// learner that reverses an opening read a reread has replaced is caught on the host.
    current: bool,
}

impl HostPass {
    fn kept(&mut self, slot: Slot) -> &mut Option<Kept> {
        match slot {
            Slot::Opened => &mut self.opened,
            Slot::Reread | Slot::OpeningTicks => &mut self.reread,
        }
    }
}

/// Two covectors summed entry by entry; integer addition is associative, so any partition of the
/// streams gives the same sum.
fn summed(mut a: Vec<i128>, b: Vec<i128>) -> Vec<i128> {
    for (x, y) in a.iter_mut().zip(&b) {
        *x += *y;
    }
    a
}

impl PassRealization for HostPass {
    fn realization(&self) -> String {
        format!("host: one stream a thread on {} threads, the reverse reading each stream's forward again", rayon::current_num_threads())
    }

    fn forward(&mut self, tower: &Tower, opening: &[TowerState], classes: &[&[usize]], targets: &[Vec<Option<usize>>], slot: Slot) -> Result<PassRead> {
        if opening.len() != classes.len() || targets.len() != classes.len() {
            return Err(TowerError::Refused("a forward reads one opening state and one comparison a stream"));
        }
        tower.admit_read(classes, targets)?;
        let held: Option<Vec<&[Vec<u32>]>> = match slot {
            Slot::OpeningTicks => {
                if tower.news().is_none() {
                    return Err(TowerError::Refused("a reread on the opening's ticks without a news clock"));
                }
                let (kept, _) = self.opened.as_ref().ok_or(TowerError::Refused("a reread on the opening's ticks before an opening read"))?;
                if kept.len() != opening.len() {
                    return Err(TowerError::Refused("a reread on the opening's ticks reads the streams its opening read"));
                }
                Some(kept.iter().map(|k| k.ticks.as_slice()).collect())
            }
            _ => None,
        };
        let reaches = tower.reaches();
        let levels = if slot == Slot::Opened { tower.declaration.levels } else { 0 };
        type Read = (KeptStream, Vec<Option<(u128, u128)>>, Vec<[u64; 4]>, Vec<Vec<(u128, u128)>>);
        let streams: Vec<Read> = opening
            .par_iter()
            .zip(classes.par_iter())
            .zip(targets.par_iter())
            .enumerate()
            .map(|(s, ((open, c), t))| {
                let mut end = open.clone();
                let cells = match &held {
                    Some(held) => tower.forward_on(&mut end, c, &reaches, held[s])?,
                    None => tower.forward(&mut end, c, &reaches)?,
                };
                let faces = cells.iter().zip(t).map(|(cell, t)| t.map(|t| (cell.face.masses[t], cell.face.total))).collect();
                let swell = (0..levels)
                    .map(|l| {
                        let mut m = [0u64; 4];
                        for lc in cells.iter().map(|c| &c.levels[l]) {
                            m[0] = m[0].max(reach(&lc.input));
                            m[1] = m[1].max(reach64(&lc.state_face));
                            m[2] = m[2].max(lc.read_scale as u64);
                            m[3] = m[3].max(reach(&lc.drive)).max(reach(&lc.pair));
                        }
                        m
                    })
                    .collect();
                let last = cells.last().map(|c| c.face.clone());
                let closures = tower.closure_faces(&cells)?;
                let ticks = if slot == Slot::Opened && tower.news().is_some() { Tower::cell_ticks(&cells) } else { Vec::new() };
                let cells = if end.credit.is_some() { cells } else { Vec::new() };
                Ok((KeptStream { cells, end, last, ticks }, faces, swell, closures))
            })
            .collect::<Result<_>>()?;
        let mut swell = vec![[0u64; 4]; levels];
        for (_, _, m, _) in &streams {
            for (a, b) in swell.iter_mut().zip(m) {
                for (x, y) in a.iter_mut().zip(b) {
                    *x = (*x).max(*y);
                }
            }
        }
        let mut faces = Vec::with_capacity(streams.len());
        let mut kept = Vec::with_capacity(streams.len());
        let mut closures = Vec::with_capacity(if tower.heading() { streams.len() } else { 0 });
        for (k, f, _, c) in streams {
            faces.push(f);
            kept.push(k);
            if tower.heading() {
                closures.push(c);
            }
        }
        *self.kept(slot) = Some((kept, reaches));
        self.current = slot == Slot::Opened;
        Ok(PassRead { faces, swell, closures })
    }

    fn reverse(&mut self, tower: &Tower, opening: &[TowerState], classes: &[&[usize]], compared: Option<&[&[Option<usize>]]>) -> Result<Vec<i128>> {
        let (kept, reaches) = self.opened.as_ref().filter(|_| self.current).ok_or(TowerError::Refused("a reverse reads the section's opening forward, not replaced by a reread"))?;
        if kept.len() != opening.len() || classes.len() != opening.len() {
            return Err(TowerError::Refused("a reverse reads the streams its opening forward read"));
        }
        let n = tower.theta.len();
        opening
            .par_iter()
            .zip(kept.par_iter())
            .zip(classes.par_iter())
            .enumerate()
            .try_fold(
                || vec![0i128; n],
                |acc, (s, ((open, k), c))| -> Result<Vec<i128>> {
                    let read;
                    let cells = if k.cells.is_empty() {
                        let mut end = open.clone();
                        read = tower.forward(&mut end, c, reaches)?;
                        &read
                    } else {
                        &k.cells
                    };
                    Ok(summed(acc, tower.reverse(open, cells, c, compared.map(|m| m[s]))?))
                },
            )
            .try_reduce(|| vec![0i128; n], |a, b| Ok(summed(a, b)))
    }

    fn reverse_split(&mut self, tower: &Tower, opening: &[TowerState], classes: &[&[usize]], compared: Option<&[&[Option<usize>]]>, paired: &PairedContacts) -> Result<(Vec<i128>, SplitRead)> {
        let (kept, reaches) = self.opened.as_ref().filter(|_| self.current).ok_or(TowerError::Refused("a reverse reads the section's opening forward, not replaced by a reread"))?;
        if kept.len() != opening.len() || classes.len() != opening.len() {
            return Err(TowerError::Refused("a reverse reads the streams its opening forward read"));
        }
        let n = tower.theta.len();
        opening
            .par_iter()
            .zip(kept.par_iter())
            .zip(classes.par_iter())
            .enumerate()
            .try_fold(
                || (vec![0i128; n], SplitRead::default()),
                |(acc, split), (s, ((open, k), c))| -> Result<(Vec<i128>, SplitRead)> {
                    let read;
                    let cells = if k.cells.is_empty() {
                        let mut end = open.clone();
                        read = tower.forward(&mut end, c, reaches)?;
                        &read
                    } else {
                        &k.cells
                    };
                    let (g, r) = tower.reverse_split(open, cells, c, compared.map(|m| m[s]), paired)?;
                    Ok((summed(acc, g), split.summed(&r)?))
                },
            )
            .try_reduce(|| (vec![0i128; n], SplitRead::default()), |a, b| Ok((summed(a.0, b.0), a.1.summed(&b.1)?)))
    }

    fn forms_split(&self) -> bool {
        true
    }

    fn carry(&mut self, tower: &Tower, states: &mut [TowerState], opening: &[TowerState], slot: Slot) -> Result<()> {
        let (kept, reaches) = self.kept(slot).take().ok_or(TowerError::Refused("a carry reads a kept forward"))?;
        tower.carry_credit(states, kept.into_iter().map(|k| (k.cells, k.end)).collect(), opening, &reaches)
    }

    fn last_faces(&mut self) -> Result<Vec<TowerFace>> {
        let (kept, _) = self.opened.as_ref().filter(|_| self.current).ok_or(TowerError::Refused("a face is read from the opening forward, not replaced by a reread"))?;
        kept.iter().map(|k| k.last.clone().ok_or(TowerError::Refused("an opening read of no cell"))).collect()
    }

    /// The host realizes every law the tower states.
    fn logits(&mut self, tower: &Tower, opening: &[TowerState], classes: &[&[usize]], targets: &[Vec<Option<usize>>]) -> Result<Vec<i64>> {
        if opening.len() != classes.len() || targets.len() != classes.len() {
            return Err(TowerError::Refused("a logits read reads one opening state and one comparison a stream"));
        }
        tower.admit_read(classes, targets)?;
        let reaches = tower.reaches();
        let streams: Vec<Vec<i64>> = opening
            .par_iter()
            .zip(classes.par_iter())
            .zip(targets.par_iter())
            .map(|((open, c), t)| {
                let mut end = open.clone();
                let cells = tower.forward(&mut end, c, &reaches)?;
                Ok(cells.iter().zip(t).filter(|(_, t)| t.is_some()).flat_map(|(cell, _)| cell.z.iter().copied()).collect())
            })
            .collect::<Result<_>>()?;
        Ok(streams.concat())
    }

    fn admit(&self, _tower: &Tower) -> Result<()> {
        Ok(())
    }
}

/// One level's families in the material and their reaches, as a section reads them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidentLevel {
    pub move_re: usize,
    pub move_im: usize,
    pub push_re: usize,
    pub push_im: usize,
    pub read_re: usize,
    pub read_im: usize,
    pub contact: usize,
    pub contact_bias: usize,
    pub ret: usize,
    pub ret_bias: usize,
    pub gate: usize,
    pub gate_bias: usize,
    /// The turned modes' turn `W_φ` (`N × d`) and bias `b_φ` (zero when unturned).
    pub turn: usize,
    pub turn_bias: usize,
    /// The pumped modes' depth `W_κ` (`N × d`) and bias `b_κ`, and their axis `W_ψ` and bias `b_ψ`
    /// (each zero when unpumped).
    pub pump: usize,
    pub pump_bias: usize,
    pub pump_axis: usize,
    pub pump_axis_bias: usize,
    /// The pair contact's second drive `W_b` (`F × d`) and bias `b_b` (each zero under rectifying
    /// contacts).
    pub pair: usize,
    pub pair_bias: usize,
    /// `max |w|` of push (re, im), read (re, im), contact, return, gate, turn, pump depth, pump
    /// axis and the pair contact's second drive (`Tower::reaches`).
    pub reaches: [u64; 11],
    /// The gated moves' founded faces, one a mode, on `2^(−30)`: the unit `u = λ/|λ|`, the
    /// modulus `|λ|` and `ℓ = log₂|λ|` (empty when ungated).
    pub units: Vec<(i64, i64)>,
    pub moduli: Vec<i64>,
    pub logs: Vec<i64>,
    /// Participation's families (zero without it): the charts `Ȟ, H, Ψ` (re, im), the current's
    /// read `Cᵃ` (re, im), the contacts' `W₁ᵃ` and the heads' friction, and `max |w|` of the first
    /// nine.
    pub participation: [usize; 10],
    pub participation_reaches: [u64; 9],
    /// The passage's `W₁ˣ` (`F × d`) and its `max |w|` (each zero without the passage or below the
    /// news clock's first clocked level, [`Tower::join_passage`]).
    pub passage: usize,
    pub passage_reach: u64,
    /// The heading's read `C^→` (re, im, `w × n`), its descent `D` (`w × w`) and their `max |w|`
    /// (each zero without the heading or below the news clock's first clocked level,
    /// [`Tower::join_heading`]).
    pub heading_re: usize,
    pub heading_im: usize,
    pub descent: usize,
    pub heading_reaches: [u64; 3],
}

/// [definition; agent-inferred, October 27] **The pair face as a realization reads it**
/// ([`PairFace`]): the count of forms `k`, the places of its readout `V` (`A × k`) and its lift
/// into the encoding `P` (`d × k`) in the material, their reaches `[max |V|, max |P|]`, and the
/// face's resident values `c_v(prev, cur)` at `((prev · A + cur) · k + v)`, `prev` over the
/// alphabet and the start `A` (the forms' face at their founding, generated from `W_v` and `E₀`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidentPair {
    pub forms: usize,
    pub readout: usize,
    pub lift: usize,
    pub reaches: [u64; 2],
    pub values: Vec<i32>,
}

/// [definition; agent-inferred, October 27] **The ring face as a realization reads it**
/// ([`RingFace`]): the level and mode it rides, its ranks `R` and the harmonics `H` its readout
/// reads, the places of its readout `W` (`A × (d + 1)·2RH`) and of its factors (rank by rank `a₀`,
/// `a₁` over `2N`, `b₀`, `b₁` over `d + 1` and `g` over `2N + 1`) in the material, the readout's
/// reach `max |W|`, each rank's releases of `a`, `b` and `g` with its push and read shifts, the
/// encoding `E₀` its pools read (`A × d`), and each rank's founded pair moves `(prev, cur, [Re λ,
/// Im λ, Re β, Im β])` and restarting class. The pools are generated from `b` and `E₀` wherever the
/// material is read, never held.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidentRing {
    pub level: usize,
    pub mode: usize,
    pub ranks: usize,
    pub harmonics: usize,
    pub readout: usize,
    pub factors: usize,
    pub reach: u64,
    pub shifts: Vec<([u32; 3], u32, u32)>,
    pub opening: Vec<i32>,
    pub moves: Vec<Vec<(usize, usize, [i64; 4])>>,
    pub restarts: Vec<Option<usize>>,
}

/// [definition; agent-inferred, October 27] **The rotor as a realization reads it** ([`Rotor`]):
/// the count of moving modes a level and, for each level, class and moving mode `m` at
/// `((level · A + class) · moving + m) · 4`, the mode `s(m)` whose state `m` takes, the mode `m'`
/// with `s(m') = m` (whose covector returns to `m`), and `m`'s turn `e^(2πi r/q)` on `2^(−30)`,
/// the key's resident face. A zero key is held as the unit `(2^30, 0)`: released at `2^(−30)`, the
/// unit carries a mode exactly, as the host's zero key does, so a class that steps and turns
/// nothing reads every mode as itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidentRotor {
    pub moving: usize,
    pub keys: Vec<i64>,
}

/// [definition; agent-inferred, October 27] **The strands as a realization reads them**
/// ([`Strands`]): the level whose contacts read them, their rings' count `R`, the places of their
/// materials `W_sa` and `W_sb` (`f × 6R` each, `W_sb` under a pair law) with `max |W_sa|` and
/// `max |W_sb|`, and one table of words:
///
/// ```text
/// [0, 3)            the three laws: 0 turned, 1 stepped, 2 held
/// [3, 8)            where the bytes' acts, the digits' turns, the keys, the words' starts and the words begin
/// 8 + 3k            ring k's modulus q, its multiplier μ and where its faces begin
/// bytes             one act a byte: 0 moves nothing, 1 + d the d-th located digit, −(1 + k) the k-th keyed byte
/// turns             each digit's turn on each ring (D × R)
/// keys              each key's three sources and its sheet (0 kept, 1 flipped, 2 set to +1, 3 set to −1)
/// starts, words     class c's bytes at [start c, start c+1) of the words
/// faces             ring k's faces e^(2πi r/q) for r < q, real then imaginary, on 2^(−16)
/// ```
///
/// The faces are the navigator's resident face at the grain the contacts read it, generated by
/// [`Strands::face`] as the host's stream reads it; refused when the table outgrows 32-bit words.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidentStrands {
    pub level: usize,
    pub rings: usize,
    pub contact: usize,
    pub pair: usize,
    pub reaches: [u64; 2],
    pub table: Vec<i32>,
}

impl ResidentStrands {
    fn of(strands: &Strands, contact: usize, pair: usize, reaches: [u64; 2], alphabet: usize) -> Result<Self> {
        let n = strands.rings.len();
        let word_bytes: usize = strands.words.iter().map(Vec::len).sum();
        let faces: usize = strands.rings.iter().map(|g| 2 * g.modulus as usize).sum();
        let bytes_at = 8 + 3 * n;
        let turns_at = bytes_at + 256;
        let keys_at = turns_at + strands.digits.len() * n;
        let starts_at = keys_at + 4 * strands.keys.len();
        let words_at = starts_at + alphabet + 1;
        let faces_at = words_at + word_bytes;
        if faces_at.checked_add(faces).is_none_or(|len| len > i32::MAX as usize) {
            return refuse("the strands' resident table outgrows 32-bit words");
        }
        let word = |v: usize| v as i32;
        let mut table = Vec::with_capacity(faces_at + faces);
        table.extend(strands.laws.map(|law| match law {
            StrandLaw::Turned => 0,
            StrandLaw::Stepped => 1,
            StrandLaw::Held => 2,
        }));
        table.extend([bytes_at, turns_at, keys_at, starts_at, words_at].map(word));
        let mut at = faces_at;
        for g in &strands.rings {
            table.extend([word(g.modulus as usize), word(g.multiplier as usize), word(at)]);
            at += 2 * g.modulus as usize;
        }
        let mut acts = [0i32; 256];
        for (d, (b, _)) in strands.digits.iter().enumerate() {
            acts[usize::from(*b)] = word(d + 1);
        }
        for (k, (b, _)) in strands.keys.iter().enumerate() {
            acts[usize::from(*b)] = -word(k + 1);
        }
        table.extend(acts);
        for (_, turns) in &strands.digits {
            table.extend(turns.iter().map(|&t| word(t as usize)));
        }
        for (_, key) in &strands.keys {
            let sheet = match key.sheet {
                Sheet::Kept => 0,
                Sheet::Flipped => 1,
                Sheet::Plus => 2,
                Sheet::Minus => 3,
            };
            table.extend(key.source.map(i32::from));
            table.push(sheet);
        }
        let mut start = 0;
        table.push(0);
        for w in &strands.words {
            start += w.len();
            table.push(word(start));
        }
        for w in &strands.words {
            table.extend(w.iter().map(|&b| i32::from(b)));
        }
        for (k, g) in strands.rings.iter().enumerate() {
            for r in 0..g.modulus {
                let (a, b) = strands.face(k, r)?;
                table.extend([a, b]);
            }
        }
        Ok(Self { level: strands.level, rings: n, contact, pair, reaches, table })
    }
}

/// [definition; agent-inferred, October 25] **The tower's law as a realization reads it for one
/// section**: the declaration, every family's place in the material, the reaches, the gated moves'
/// founded faces, the exponential navigator's resident faces (`2^(2^(−i))` on `2^(−62)`, at the
/// face's grain and at the moves'), `ln 2` and `(ln 2)²` on `2^(−30)`, the pair face, the ring face,
/// the rotor and the strands when they are joined, and the news clock when one is joined. Read
/// from the tower's own owners, so a realization holds no second copy of a law, and a realization
/// that does not carry a joined part refuses the tower rather than reading it without that part.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidentLaw {
    pub declaration: TowerDeclaration,
    pub len: usize,
    pub encoding: usize,
    pub readout: usize,
    pub readout_bias: usize,
    pub readout_reach: u64,
    pub levels: Vec<ResidentLevel>,
    pub face_roots: Vec<u128>,
    pub move_roots: Vec<u128>,
    pub ln2_square: i128,
    /// `ln 2` on `2^(−30)`, which the pump's depth reads (`∂κ/∂q = 2 ln 2 r (1 − r)`).
    pub ln2: i128,
    /// The turned modes' ladder `e^(iπ/2^i)`, `i = 0..=16`, and the half turn `π`, on `2^(−30)`
    /// (empty and zero when unturned): the turn's navigator faces, generated where the tower reads
    /// its reaches.
    pub ladder: Vec<(i64, i64)>,
    pub half_turn: i64,
    pub pair: Option<ResidentPair>,
    pub ring: Option<ResidentRing>,
    pub rotor: Option<ResidentRotor>,
    pub strands: Option<ResidentStrands>,
    pub news: Option<NewsClock>,
    /// The levels' participation, when it is joined: a realization that does not carry it refuses
    /// the tower.
    pub participation: Option<super::ParticipationDeclaration>,
    /// The mutual contact's `b` (`β = 2^(−b)`), when the comparison is one (the readout's place
    /// then holds the contact's geometry `J`, `d × d`): a realization that does not carry it refuses
    /// the tower.
    pub mutual: Option<u32>,
    /// Whether the contacts of the levels the news clock holds (from its first clocked level) hear
    /// the passing current ([`Tower::join_passage`]): a realization that does not carry it refuses
    /// the tower.
    pub passage: bool,
    /// Whether the levels the news clock holds hear the packet their clock closed
    /// ([`Tower::join_packets`]): a realization that does not carry it refuses the tower.
    pub packets: bool,
    /// The closure's shift `s` when the levels the news clock holds carry a heading the fine
    /// levels read ([`Tower::join_heading`]; `z = 2^(−s) ⟨ĥ, τ⟩` on `2^(−16)`): a realization that
    /// does not carry it refuses the tower.
    pub heading: Option<u32>,
    /// `log₂` of the moves' margin radius on `2^(−16)`: a held move's met dissipation.
    pub held_log: i64,
}

impl Tower {
    /// [definition; agent-inferred, October 27] **A frozen read through a realization**: each part
    /// read from rest, the code `−log₂ p̂` of every class after its first on `2^(−20)` bits, as
    /// [`Tower::read_cells`] reads it, in windows of `section` cells whose continuing states are
    /// carried into the next window ([`Slot::Reread`]), so the held-out read runs where the
    /// training passes run. A part shorter than the longest is padded past its end with places
    /// compared with nothing; the forward reads in order, so the padding moves no face the part
    /// reads. The tower is not moved.
    pub fn read_parts_realized(&self, parts: &[&[usize]], section: usize, realization: &mut dyn PassRealization) -> Result<Vec<Vec<i64>>> {
        if section == 0 {
            return Err(TowerError::Refused("a realized read takes windows of at least one cell"));
        }
        self.admit_read(parts, &[])?;
        let longest = parts.iter().map(|p| p.len()).max().unwrap_or(0);
        let mut codes: Vec<Vec<i64>> = parts.iter().map(|p| Vec::with_capacity(p.len().saturating_sub(1))).collect();
        let mut states: Vec<TowerState> = parts.iter().map(|_| self.rest()).collect();
        let mut at = 0usize;
        while at + 1 < longest {
            let cells = section.min(longest - 1 - at);
            let windows: Vec<Vec<usize>> = parts.iter().map(|p| (at..=at + cells).map(|i| p.get(i).copied().unwrap_or(0)).collect()).collect();
            let targets: Vec<Vec<Option<usize>>> = parts.iter().map(|p| (at + 1..=at + cells).map(|i| p.get(i).copied()).collect()).collect();
            let classes: Vec<&[usize]> = windows.iter().map(Vec::as_slice).collect();
            let read = realization.forward(self, &states, &classes, &targets, Slot::Reread)?.admitted(&targets)?;
            for (code, faces) in codes.iter_mut().zip(&read.faces) {
                code.extend(faces.iter().flatten().map(|&(m, t)| face_code(m, t)));
            }
            let opening = states.clone();
            realization.carry(self, &mut states, &opening, Slot::Reread)?;
            at += cells;
        }
        Ok(codes)
    }

    /// [definition; agent-inferred, October 27] Every class a realization reads and every class it
    /// compares a face with lies in the declared alphabet. A face has no mass at a class outside
    /// it (the card's read is zero there, the host's face has no entry), and the certificate
    /// decides on positive masses, so such a read is refused before any realization reads it. The
    /// section, the realized read and the realized advance call it themselves, so a realization
    /// that does not is still never handed such a read.
    pub fn admit_read(&self, classes: &[&[usize]], targets: &[Vec<Option<usize>>]) -> Result<()> {
        let a = self.declaration.alphabet;
        if classes.iter().any(|c| c.iter().any(|&u| u >= a)) || targets.iter().flatten().flatten().any(|&t| t >= a) {
            return Err(TowerError::Refused("a class read or compared outside the declared alphabet"));
        }
        Ok(())
    }

    /// [definition; agent-inferred, October 27] **The advance through a realization**: each
    /// stream reads its classes from its state and returns the whole face after its last class
    /// and the code of each class after its first (`2^(−20)` bits), its state moved past every
    /// class: [`Tower::advance`] class by class, on whatever realizes the pass. A release (a
    /// prompt, then one drawn class at a time) runs where the training runs. The streams' class
    /// lists have one length; the read's last place is compared with nothing, so the face it
    /// returns is the one the next class is drawn from.
    ///
    /// [agent-inferred, October 29] A participating tower's section closes at its last site, and a
    /// realization reads a section to its close and no further (the card does; the host need not),
    /// so the advance is read in calls that end where a stream's open section closes, the streams'
    /// open sites carried between them. Each call's first class is compared with the face the call
    /// before it returned, so the codes are the whole read's.
    pub fn advance_realized(&self, states: &mut [TowerState], classes: &[&[usize]], realization: &mut dyn PassRealization) -> Result<(Vec<TowerFace>, Vec<i64>)> {
        let n = classes.first().map_or(0, |c| c.len());
        if n == 0 || classes.iter().any(|c| c.len() != n) || states.len() != classes.len() {
            return Err(TowerError::Refused("an advance reads one nonempty length of classes a stream"));
        }
        self.admit_read(classes, &[])?;
        let mut codes = vec![0i64; classes.len()];
        let mut faces: Vec<TowerFace> = Vec::new();
        let mut a = 0;
        while a < n {
            let close = match self.participation() {
                Some(p) => {
                    let open = states.iter().map(|s| p.section.checked_sub(s.sites.first().map_or(0, LevelSites::len)).filter(|&r| r > 0));
                    a + open.collect::<Option<Vec<usize>>>().ok_or(TowerError::Refused("an open section past its close"))?.into_iter().min().unwrap_or(n)
                }
                None => n,
            };
            let b = close.min(n);
            for (s, face) in faces.iter().enumerate() {
                codes[s] += face.code(classes[s][a]);
            }
            let parts: Vec<&[usize]> = classes.iter().map(|c| &c[a..b]).collect();
            let (read, read_codes) = self.advance_call(states, &parts, realization)?;
            for (sum, c) in codes.iter_mut().zip(read_codes) {
                *sum += c;
            }
            faces = read;
            a = b;
        }
        Ok((faces, codes))
    }

    /// One call of [`Tower::advance_realized`]: every stream's classes read from its state, within
    /// its open section.
    fn advance_call(&self, states: &mut [TowerState], classes: &[&[usize]], realization: &mut dyn PassRealization) -> Result<(Vec<TowerFace>, Vec<i64>)> {
        let windows: Vec<Vec<usize>> = classes.iter().map(|c| c.iter().copied().chain([0]).collect()).collect();
        let targets: Vec<Vec<Option<usize>>> = classes.iter().map(|c| c[1..].iter().map(|&u| Some(u)).chain([None]).collect()).collect();
        let reads: Vec<&[usize]> = windows.iter().map(Vec::as_slice).collect();
        let read = realization.forward(self, states, &reads, &targets, Slot::Opened)?.admitted(&targets)?;
        let codes = read.faces.iter().map(|faces| faces.iter().flatten().map(|&(m, t)| face_code(m, t)).sum()).collect();
        let faces = realization.last_faces()?;
        let alphabet = self.declaration.alphabet;
        if faces.len() != classes.len() || faces.iter().any(|f| f.masses.len() != alphabet || f.total == 0 || f.masses.iter().any(|&m| m > f.total)) {
            return Err(TowerError::Refused("a realization returned a last face that is not one a stream over the alphabet, with a positive total and no mass past it"));
        }
        let opening = states.to_vec();
        realization.carry(self, states, &opening, Slot::Opened)?;
        Ok((faces, codes))
    }

    /// The tower's [`ResidentLaw`] for a section read under its current material.
    pub fn resident_law(&self) -> Result<ResidentLaw> {
        let reaches = self.reaches();
        let narrow = |v: i128| fit64(v);
        let levels = collect_exact(self.layout.levels.iter().enumerate().map(|(l, lv)| {
            let r = &reaches.levels[l];
            let (units, moduli, logs) = match reaches.gates.get(l) {
                Some(faces) => (
                    collect_exact(faces.units.iter().map(|&(re, im)| Ok((narrow(re)?, narrow(im)?))))?,
                    collect_exact(faces.moduli.iter().map(|&m| narrow(m)))?,
                    collect_exact(faces.logs.iter().map(|&m| narrow(m)))?,
                ),
                None => (Vec::new(), Vec::new(), Vec::new()),
            };
            Ok(ResidentLevel {
                move_re: lv.move_re,
                move_im: lv.move_im,
                push_re: lv.push_re,
                push_im: lv.push_im,
                read_re: lv.read_re,
                read_im: lv.read_im,
                contact: lv.contact,
                contact_bias: lv.contact_bias,
                ret: lv.ret,
                ret_bias: lv.ret_bias,
                gate: lv.gate,
                gate_bias: lv.gate_bias,
                turn: lv.turn,
                turn_bias: lv.turn_bias,
                pump: lv.pump,
                pump_bias: lv.pump_bias,
                pump_axis: lv.pump_axis,
                pump_axis_bias: lv.pump_axis_bias,
                pair: lv.pair,
                pair_bias: lv.pair_bias,
                reaches: *r,
                units,
                moduli,
                logs,
                participation: [lv.pa_probe_re, lv.pa_probe_im, lv.pa_key_re, lv.pa_key_im, lv.pa_value_re, lv.pa_value_im, lv.pa_read_re, lv.pa_read_im, lv.pa_contact, lv.pa_friction],
                participation_reaches: reaches.participation.get(l).copied().unwrap_or([0; 9]),
                passage: lv.passage,
                passage_reach: reaches.passage.get(l).copied().unwrap_or(0),
                heading_re: lv.heading_re,
                heading_im: lv.heading_im,
                descent: lv.descent,
                heading_reaches: reaches.heading.get(l).copied().unwrap_or([0; 3]),
            })
        }))?;
        Ok(ResidentLaw {
            declaration: self.declaration,
            len: self.layout.len,
            encoding: self.layout.encoding,
            readout: self.layout.readout,
            readout_bias: self.layout.readout_bias,
            readout_reach: reaches.readout,
            levels,
            face_roots: self.exponential.roots().to_vec(),
            move_roots: self.fine.roots().to_vec(),
            ln2_square: release(ln2_face() * ln2_face(), MOVE_BITS),
            ln2: ln2_face(),
            ladder: collect_exact(reaches.ladder.iter().map(|&(re, im)| Ok((narrow(re)?, narrow(im)?))))?,
            half_turn: narrow(reaches.half_turn)?,
            pair: self.pair.as_ref().map(|face| ResidentPair {
                forms: face.forms(),
                readout: self.layout.pair_readout,
                lift: self.layout.pair_encoding,
                reaches: reaches.pair,
                values: face.values.clone(),
            }),
            ring: self.ring.as_ref().map(|face| ResidentRing {
                level: face.level,
                mode: face.mode,
                ranks: face.ranks(),
                harmonics: face.harmonics,
                readout: self.layout.ring_readout,
                factors: self.layout.ring_factors,
                reach: reaches.ring,
                shifts: face.shifts.clone(),
                opening: face.opening.clone(),
                moves: face.moves.clone(),
                restarts: face.restarts.clone(),
            }),
            rotor: self.rotor.as_ref().map(|rotor| {
                let (d, moving) = (&self.declaration, rotor.moving());
                let mut keys = vec![0i64; d.levels * d.alphabet * moving * 4];
                for (at, entry) in keys.chunks_mut(4).enumerate() {
                    let (lc, m) = (at / moving, at % moving);
                    let (level, class) = (lc / d.alphabet, lc % d.alphabet);
                    let source = rotor.source(level, class, m);
                    let first = rotor.places[m].1;
                    let width = rotor.rings[rotor.places[m].0].width;
                    let step = rotor.step(level, class, rotor.places[m].0);
                    let (a, b) = if rotor.turns[at] == 0 { (1i128 << MOVE_BITS, 0) } else { rotor.faces[at] };
                    entry.copy_from_slice(&[source as i64, (first + (m - first + width - step) % width) as i64, a as i64, b as i64]);
                }
                ResidentRotor { moving, keys }
            }),
            strands: self.strands.as_ref().map(|strands| ResidentStrands::of(strands, self.layout.strand_contact, self.layout.strand_pair, reaches.strands, self.declaration.alphabet)).transpose()?,
            news: self.news,
            participation: self.participation.clone(),
            mutual: self.mutual,
            passage: self.passage,
            packets: self.packets,
            heading: self.heading.then(|| super::closure_shift(self.declaration.width)),
            held_log: reaches.held_log,
        })
    }
}
