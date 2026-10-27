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
//! the reverse reads, and once under each candidate deposit ([`Slot::Reread`]), which needs only its
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
}

type Kept = (Vec<(Vec<Cell>, TowerState)>, Reaches);

/// [definition] **The host's realization**: each stream's forward and reverse on its own thread,
/// the streams' covectors summed in stream order.
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

impl PassRealization for HostPass {
    fn realization(&self) -> String {
        format!("host: one stream a thread on {} threads", rayon::current_num_threads())
    }

    fn forward(&mut self, tower: &Tower, opening: &[TowerState], classes: &[&[usize]], targets: &[Vec<Option<usize>>], slot: Slot) -> Result<PassRead> {
        let reaches = tower.reaches();
        let forwards: Vec<(Vec<Cell>, TowerState)> = opening
            .par_iter()
            .zip(classes.par_iter())
            .map(|(open, c)| {
                let mut s = open.clone();
                let cells = tower.forward(&mut s, c, &reaches)?;
                Ok((cells, s))
            })
            .collect::<Result<_>>()?;
        let swell = if slot == Slot::Opened {
            (0..tower.declaration.levels)
                .map(|l| {
                    let mut m = [0u64; 4];
                    for lc in forwards.iter().flat_map(|(cells, _)| cells.iter().map(move |c| &c.levels[l])) {
                        m[0] = m[0].max(reach(&lc.input));
                        m[1] = m[1].max(reach64(&lc.state_face));
                        m[2] = m[2].max(lc.read_scale as u64);
                        m[3] = m[3].max(reach(&lc.drive)).max(reach(&lc.pair));
                    }
                    m
                })
                .collect()
        } else {
            Vec::new()
        };
        let faces = forwards
            .iter()
            .zip(targets)
            .map(|((cells, _), t)| cells.iter().zip(t).map(|(cell, t)| t.map(|t| (cell.face.masses[t], cell.face.total))).collect())
            .collect();
        *self.kept(slot) = Some((forwards, reaches));
        Ok(PassRead { faces, swell })
    }

    fn reverse(&mut self, tower: &Tower, opening: &[TowerState], classes: &[&[usize]], compared: Option<&[&[Option<usize>]]>) -> Result<Vec<i128>> {
        let (forwards, _) = self.opened.as_ref().ok_or(TowerError::Refused("a reverse reads the section's opening forward"))?;
        let gradients: Vec<Vec<i128>> = opening
            .par_iter()
            .zip(forwards.par_iter())
            .zip(classes.par_iter())
            .enumerate()
            .map(|(s, ((open, (cells, _)), c))| tower.reverse(open, cells, c, compared.map(|m| m[s])))
            .collect::<Result<_>>()?;
        let mut g = vec![0i128; tower.theta.len()];
        for gs in &gradients {
            for (a, b) in g.iter_mut().zip(gs) {
                *a += *b;
            }
        }
        Ok(g)
    }

    fn carry(&mut self, tower: &Tower, states: &mut [TowerState], opening: &[TowerState], slot: Slot) -> Result<()> {
        let (forwards, reaches) = self.kept(slot).take().ok_or(TowerError::Refused("a carry reads a kept forward"))?;
        tower.carry_credit(states, forwards, opening, &reaches)
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

/// [definition; agent-inferred, October 25] **The tower's law as a realization reads it for one
/// section**: the declaration, every family's place in the material, the reaches, the gated moves'
/// founded faces, the exponential navigator's resident faces (`2^(2^(−i))` on `2^(−62)`, at the
/// face's grain and at the moves'), `(ln 2)²` on `2^(−30)`, the pair face and the ring face when
/// they are joined, and whether a rotor or strands are. Read from the tower's own owners, so a realization
/// holds no second copy of a law, and a realization that does not carry a joined part refuses the
/// tower rather than reading it without that part.
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
    pub pair: Option<ResidentPair>,
    pub ring: Option<ResidentRing>,
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
            rotor: self.rotor.is_some(),
            strands: self.strands.is_some(),
        })
    }
}
