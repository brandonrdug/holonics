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
use super::*;

/// Which forward of a section a read is: the opening read (whose temporaries the reverse reads) or
/// the certificate's reread under a candidate deposit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Slot {
    Opened,
    Reread,
}

/// What a section reads of one forward: per stream, per cell, the face compared at its target, `(the
/// target's mass, the total)` on `2^(−62)` (`None` where the place is compared with nothing), and,
/// for the opening read, the swell per level (`TowerLearner::swell`; empty for a reread).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassRead {
    pub faces: Vec<Vec<Option<(u128, u128)>>>,
    pub swell: Vec<[u64; 4]>,
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

    /// Each stream's continuing state from the read kept in `slot`, its credit moved along it.
    fn carry(&mut self, tower: &Tower, states: &mut [TowerState], opening: &[TowerState], slot: Slot) -> Result<()>;

    /// Every stream's whole face at the last cell of the read kept in [`Slot::Opened`]: each
    /// class's mass and their total on `2^(−62)`, the face a release draws from.
    fn last_faces(&mut self) -> Result<Vec<TowerFace>>;

    /// Whether this realization carries `tower`'s law. A run reads it before any model work or
    /// output, so a law the realization does not carry is refused at the run's start, never at its
    /// first section.
    fn admit(&self, tower: &Tower) -> Result<()>;
}

/// One stream's forward as the host keeps it between calls: its continuing state, its face after
/// its last class, and its cells only where the stream carries a passage credit, whose carry reads
/// every cell (`Tower::carry_credit`).
struct KeptStream {
    cells: Vec<Cell>,
    end: TowerState,
    last: Option<TowerFace>,
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
}

impl HostPass {
    fn kept(&mut self, slot: Slot) -> &mut Option<Kept> {
        match slot {
            Slot::Opened => &mut self.opened,
            Slot::Reread => &mut self.reread,
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
        let reaches = tower.reaches();
        let levels = if slot == Slot::Opened { tower.declaration.levels } else { 0 };
        let streams: Vec<(KeptStream, Vec<Option<(u128, u128)>>, Vec<[u64; 4]>)> = opening
            .par_iter()
            .zip(classes.par_iter())
            .zip(targets.par_iter())
            .map(|((open, c), t)| {
                let mut end = open.clone();
                let cells = tower.forward(&mut end, c, &reaches)?;
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
                let cells = if end.credit.is_some() { cells } else { Vec::new() };
                Ok((KeptStream { cells, end, last }, faces, swell))
            })
            .collect::<Result<_>>()?;
        let mut swell = vec![[0u64; 4]; levels];
        for (_, _, m) in &streams {
            for (a, b) in swell.iter_mut().zip(m) {
                for (x, y) in a.iter_mut().zip(b) {
                    *x = (*x).max(*y);
                }
            }
        }
        let mut faces = Vec::with_capacity(streams.len());
        let mut kept = Vec::with_capacity(streams.len());
        for (k, f, _) in streams {
            faces.push(f);
            kept.push(k);
        }
        *self.kept(slot) = Some((kept, reaches));
        Ok(PassRead { faces, swell })
    }

    fn reverse(&mut self, tower: &Tower, opening: &[TowerState], classes: &[&[usize]], compared: Option<&[&[Option<usize>]]>) -> Result<Vec<i128>> {
        let (kept, reaches) = self.opened.as_ref().ok_or(TowerError::Refused("a reverse reads the section's opening forward"))?;
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

    fn carry(&mut self, tower: &Tower, states: &mut [TowerState], opening: &[TowerState], slot: Slot) -> Result<()> {
        let (kept, reaches) = self.kept(slot).take().ok_or(TowerError::Refused("a carry reads a kept forward"))?;
        tower.carry_credit(states, kept.into_iter().map(|k| (k.cells, k.end)).collect(), opening, &reaches)
    }

    fn last_faces(&mut self) -> Result<Vec<TowerFace>> {
        let (kept, _) = self.opened.as_ref().ok_or(TowerError::Refused("a face is read from the opening forward"))?;
        kept.iter().map(|k| k.last.clone().ok_or(TowerError::Refused("an opening read of no cell"))).collect()
    }

    /// The host realizes every law the tower states.
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
    /// `max |w|` of push (re, im), read (re, im), contact, return and gate (`Tower::reaches`).
    pub reaches: [u64; 7],
    /// The gated moves' founded faces, one a mode, on `2^(−30)`: the unit `u = λ/|λ|`, the
    /// modulus `|λ|` and `ℓ = log₂|λ|` (empty when ungated).
    pub units: Vec<(i64, i64)>,
    pub moduli: Vec<i64>,
    pub logs: Vec<i64>,
}

/// [definition; agent-inferred, October 25] **The tower's law as a realization reads it for one
/// section**: the declaration, every family's place in the material, the reaches, the gated moves'
/// founded faces, the exponential navigator's resident faces (`2^(2^(−i))` on `2^(−62)`, at the
/// face's grain and at the moves'), `(ln 2)²` on `2^(−30)` and whether a pair face, ring face,
/// rotor or strands are joined. Read from the tower's own owners, so a realization holds no second
/// copy of a law, and a realization that does not carry a joined part refuses the tower rather
/// than reading it without that part.
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
    pub pair_face: bool,
    pub ring_face: bool,
    pub rotor: bool,
    pub strands: bool,
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
            let read = realization.forward(self, &states, &classes, &targets, Slot::Reread)?;
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
    pub fn advance_realized(&self, states: &mut [TowerState], classes: &[&[usize]], realization: &mut dyn PassRealization) -> Result<(Vec<TowerFace>, Vec<i64>)> {
        let n = classes.first().map_or(0, |c| c.len());
        if n == 0 || classes.iter().any(|c| c.len() != n) || states.len() != classes.len() {
            return Err(TowerError::Refused("an advance reads one nonempty length of classes a stream"));
        }
        self.admit_read(classes, &[])?;
        let windows: Vec<Vec<usize>> = classes.iter().map(|c| c.iter().copied().chain([0]).collect()).collect();
        let targets: Vec<Vec<Option<usize>>> = classes.iter().map(|c| c[1..].iter().map(|&u| Some(u)).chain([None]).collect()).collect();
        let reads: Vec<&[usize]> = windows.iter().map(Vec::as_slice).collect();
        let read = realization.forward(self, states, &reads, &targets, Slot::Opened)?;
        let codes = read.faces.iter().map(|faces| faces.iter().flatten().map(|&(m, t)| face_code(m, t)).sum()).collect();
        let faces = realization.last_faces()?;
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
                reaches: [r[0], r[1], r[2], r[3], r[4], r[5], r[6]],
                units,
                moduli,
                logs,
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
            pair_face: self.pair.is_some(),
            ring_face: self.ring.is_some(),
            rotor: self.rotor.is_some(),
            strands: self.strands.is_some(),
        })
    }
}
