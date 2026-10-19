//! The derived pair face at unit modulus. Counts have one writer; readers share exact snapshots.
use super::*;
use crate::ratio::linear::vector::combination;
use rayon::prelude::*;
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, RwLock};

#[derive(Clone)]
struct Reads {
    current_values: Vec<Vec<Rat>>,
    earlier_values: Vec<Vec<Rat>>,
    current: Vec<Chart>,
    earlier: Vec<Chart>,
}

impl Reads {
    fn matches(&self, port: &PairPort) -> bool {
        self.current_values.as_slice() == port.current_reads()
            && self.earlier_values.as_slice() == port.earlier_reads()
    }
}

#[derive(Clone)]
struct PhaseFace {
    population: u64,
    weights: Vec<BigInt>,
    // Class-major COW rows: one binding copies at most W and two rank-sized rows,
    // rather than all period × alphabet × rank integers held by the face.
    current: Vec<Arc<Vec<BigInt>>>,
    earlier: Vec<Arc<Vec<BigInt>>>,
}

impl PhaseFace {
    fn empty(alphabet: usize, rank: usize) -> Self {
        Self {
            population: 0,
            weights: vec![BigInt::zero(); rank],
            current: (0..alphabet)
                .map(|_| Arc::new(vec![BigInt::zero(); rank]))
                .collect(),
            earlier: (0..alphabet)
                .map(|_| Arc::new(vec![BigInt::zero(); rank]))
                .collect(),
        }
    }
}

/// The exact derived series W, R and L on the reads' integer charts, before population weight.
/// Outputs are excluded from the key. No occurrence, address or order is added to the moment.
#[derive(Clone)]
pub(crate) struct ResidentPairFace {
    reads: Arc<Reads>,
    phases: Vec<Arc<PhaseFace>>,
    population: u64,
    occupied_bindings: usize,
    sum_squares: BigInt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PairFaceGradient {
    pub(crate) outputs: Vec<Vec<Rat>>,
    pub(crate) current: Vec<Vec<Rat>>,
    pub(crate) earlier: Vec<Vec<Rat>>,
    pub(crate) energy: Rat,
    pub(crate) covector: Rat,
}

/// An exact, transient chart for one pair and direction, shared only during a comparison.
/// Borrowing the port binds both its reads and outputs; this is not a resident/history cache.
pub(crate) struct PreparedPairRay<'a> {
    port: &'a PairPort,
    width: usize,
    current: Vec<Vec<BigInt>>,
    earlier: Vec<Vec<BigInt>>,
    first_weight: Vec<Vec<BigInt>>,
    first_linear: Vec<Vec<BigInt>>,
    second: Vec<Vec<BigInt>>,
    first_den: BigInt,
    second_den: BigInt,
}

impl<'a> PreparedPairRay<'a> {
    pub(crate) fn new(port: &'a PairPort, direction: [&[Vec<Rat>]; 3]) -> Result<Self, HnnError> {
        if [port.outputs(), port.current_reads(), port.earlier_reads()]
            .into_iter().zip(direction).any(|(base, delta)| {
                base.len() != delta.len()
                    || base.iter().zip(delta).any(|(x, dx)| x.len() != dx.len())
            }) {
            return Err(HnnError::Unadmitted {
                reason: "a pair ray must read its contemporary factors and direction",
            });
        }
        let [de, da, db] = direction;
        let a: Vec<_> = port.current_reads().iter().map(|row| integral(row)).collect();
        let b: Vec<_> = port.earlier_reads().iter().map(|row| integral(row)).collect();
        let e: Vec<_> = port.outputs().iter().map(|row| integral(row)).collect();
        let de: Vec<_> = de.iter().map(|row| integral(row)).collect();
        let da: Vec<_> = da.iter().map(|row| integral(row)).collect();
        let db: Vec<_> = db.iter().map(|row| integral(row)).collect();
        // L_rho = lcm(Da*B, Db*A). The integer linear coefficient is
        // l_rho = (da.Cb)*(L/(Da*B)) + (db.Ca)*(L/(Db*A)).
        // Y1 = weight * sum(de*W/(De*A*B) + e*l/(E*L));
        // Y2' = weight * sum(de*l/(De*L)). Only the final two squared readings
        // normalize a rational. Population, phase and every signed term remain exact.
        let linear_den: Vec<_> = (0..port.rank())
            .map(|rho| lcm(&(&da[rho].1 * &b[rho].1), &(&db[rho].1 * &a[rho].1))).collect();
        let weight_den: Vec<_> = (0..port.rank())
            .map(|rho| &de[rho].1 * &a[rho].1 * &b[rho].1).collect();
        let read_den: Vec<_> = (0..port.rank()).map(|rho| &e[rho].1 * &linear_den[rho]).collect();
        let second_den_by_rank: Vec<_> = (0..port.rank()).map(|rho| &de[rho].1 * &linear_den[rho]).collect();
        let first_den = weight_den.iter().chain(&read_den)
            .fold(BigInt::one(), |den, value| lcm(&den, value));
        let second_den = second_den_by_rank.iter()
            .fold(BigInt::one(), |den, value| lcm(&den, value));
        let scaled = |row: &[BigInt], scale: BigInt| row.iter().map(|n| n * &scale).collect();
        Ok(Self {
            port,
            width: port.outputs().first().map_or(0, Vec::len),
            current: (0..port.rank()).map(|rho|
                scaled(&da[rho].0, &linear_den[rho] / (&da[rho].1 * &b[rho].1))).collect(),
            earlier: (0..port.rank()).map(|rho|
                scaled(&db[rho].0, &linear_den[rho] / (&db[rho].1 * &a[rho].1))).collect(),
            first_weight: (0..port.rank()).map(|rho|
                scaled(&de[rho].0, &first_den / &weight_den[rho])).collect(),
            first_linear: (0..port.rank()).map(|rho|
                scaled(&e[rho].0, &first_den / &read_den[rho])).collect(),
            second: (0..port.rank()).map(|rho|
                scaled(&de[rho].0, &second_den / &second_den_by_rank[rho])).collect(),
            first_den,
            second_den,
        })
    }
}

impl ResidentPairFace {
    fn build(
        counts: &[u64],
        period: usize,
        alphabet: usize,
        port: &PairPort,
    ) -> Result<Self, HnnError> {
        if counts.len() != period * alphabet * alphabet
            || port
                .current_reads()
                .iter()
                .chain(port.earlier_reads())
                .any(|r| r.len() != alphabet)
        {
            return Err(HnnError::Shape {
                what: "a resident pair face against its counts and port reads",
                expected: period * alphabet * alphabet,
                found: counts.len(),
            });
        }
        let reads = Arc::new(Reads {
            current_values: port.current_reads().to_vec(),
            earlier_values: port.earlier_reads().to_vec(),
            current: port.current_reads().iter().map(|r| integral(r)).collect(),
            earlier: port.earlier_reads().iter().map(|r| integral(r)).collect(),
        });
        let mut face = Self {
            reads,
            phases: (0..period)
                .map(|_| Arc::new(PhaseFace::empty(alphabet, port.rank())))
                .collect(),
            population: 0,
            occupied_bindings: 0,
            sum_squares: BigInt::zero(),
        };
        for (slot, &count) in counts.iter().enumerate().filter(|(_, n)| **n != 0) {
            let phase = slot / (alphabet * alphabet);
            let (x, y) = ((slot / alphabet) % alphabet, slot % alphabet);
            face.add(phase, x, y, count)?;
            face.occupied_bindings += 1;
            let n = BigInt::from(count);
            face.sum_squares += &n * &n;
        }
        Ok(face)
    }

    fn add(&mut self, phase: usize, x: usize, y: usize, count: u64) -> Result<(), HnnError> {
        self.population = self
            .population
            .checked_add(count)
            .ok_or(HnnError::CountOverflow)?;
        let p = Arc::make_mut(&mut self.phases[phase]);
        p.population = p
            .population
            .checked_add(count)
            .ok_or(HnnError::CountOverflow)?;
        let r = Arc::make_mut(&mut p.current[x]);
        let l = Arc::make_mut(&mut p.earlier[y]);
        let count = BigInt::from(count);
        for rho in 0..self.reads.current.len() {
            let a = &self.reads.current[rho].0[x];
            let b = &self.reads.earlier[rho].0[y];
            p.weights[rho] += &count * a * b;
            r[rho] += &count * b;
            l[rho] += &count * a;
        }
        Ok(())
    }

    fn bind(&mut self, phase: usize, x: usize, y: usize, old: u64) -> Result<(), HnnError> {
        self.add(phase, x, y, 1)?;
        self.occupied_bindings += usize::from(old == 0);
        self.sum_squares += (BigInt::from(old) << 1usize) + BigInt::one();
        Ok(())
    }

    pub(crate) fn population(&self) -> u64 {
        self.population
    }

    /// Each output coordinate is reduced once, after summing all ranks in integer charts.
    pub(crate) fn output_series(
        &self,
        port: &PairPort,
        width: usize,
        weight: &Rat,
    ) -> Result<Vec<Vec<Rat>>, HnnError> {
        if !self.reads.matches(port) || port.outputs().iter().any(|r| r.len() != width) {
            return Err(HnnError::Unadmitted {
                reason: "a resident pair face must read its own port factors",
            });
        }
        let outputs: Vec<_> = port.outputs().iter().map(|r| integral(r)).collect();
        let denominators: Vec<_> = (0..port.rank())
            .map(|rho| &self.reads.current[rho].1 * &self.reads.earlier[rho].1 * &outputs[rho].1)
            .collect();
        let denominator = denominators.iter().fold(BigInt::one(), |d, t| lcm(&d, t));
        let scales: Vec<_> = denominators.iter().map(|d| &denominator / d).collect();
        let denominator = denominator * weight.denom();
        let mut series = Vec::with_capacity(self.phases.len());
        for phase in &self.phases {
            let mut sums = vec![BigInt::zero(); width];
            for rho in 0..port.rank() {
                let coefficient = &phase.weights[rho] * &scales[rho];
                if coefficient.is_zero() {
                    continue;
                }
                for (sum, entry) in sums.iter_mut().zip(&outputs[rho].0) {
                    *sum += &coefficient * entry;
                }
            }
            series.push(
                sums.into_iter()
                    .map(|n| Rat::new(n * weight.numer(), denominator.clone()))
                    .collect(),
            );
        }
        Ok(series)
    }

    /// The three exact rank gradients on this face. Each family is normalized once per result
    /// coordinate; the occupied-slot loop is absent from this read.
    pub(crate) fn gradient(
        &self,
        port: &PairPort,
        turned: &[Vec<Rat>],
        turned_charts: &[Chart],
        weight: &Rat,
    ) -> Result<PairFaceGradient, HnnError> {
        if !self.reads.matches(port)
            || turned.len() != self.phases.len()
            || turned_charts.len() != self.phases.len()
            || turned
                .iter()
                .any(|h| h.len() != port.outputs().first().map_or(h.len(), Vec::len))
        {
            return Err(HnnError::Unadmitted {
                reason: "a pair gradient must read its contemporary face and turned opening",
            });
        }
        let width = turned.first().map_or(0, Vec::len);
        let alphabet = self.reads.current_values.first().map_or(0, Vec::len);
        let h_den = turned_charts
            .iter()
            .fold(BigInt::one(), |d, (_, t)| lcm(&d, t));
        let h: Vec<Vec<BigInt>> = turned_charts
            .iter()
            .map(|(v, d)| {
                let scale = &h_den / d;
                v.iter().map(|x| x * &scale).collect()
            })
            .collect();
        let ranks: Vec<_> = (0..port.rank())
            .into_par_iter()
            .map(|rho| {
                let (e, e_den) = integral(&port.outputs()[rho]);
                let mut out = vec![BigInt::zero(); width];
                let mut current = vec![BigInt::zero(); alphabet];
                let mut earlier = vec![BigInt::zero(); alphabet];
                for (phase, p) in self.phases.iter().enumerate() {
                    if p.population == 0 {
                        continue;
                    }
                    for (sum, entry) in out.iter_mut().zip(&h[phase]) {
                        *sum += &p.weights[rho] * entry;
                    }
                    let eh: BigInt = e.iter().zip(&h[phase]).map(|(a, b)| a * b).sum();
                    if eh.is_zero() {
                        continue;
                    }
                    for x in 0..alphabet {
                        current[x] += &eh * &p.current[x][rho];
                        earlier[x] += &eh * &p.earlier[x][rho];
                    }
                }
                let da = &self.reads.current[rho].1;
                let db = &self.reads.earlier[rho].1;
                let normalize = |v: Vec<BigInt>, d: BigInt| {
                    v.into_iter()
                        .map(|n| Rat::new(n * weight.numer(), d.clone()))
                        .collect::<Vec<_>>()
                };
                (
                    normalize(out, weight.denom() * da * db * &h_den),
                    normalize(current, weight.denom() * &e_den * &h_den * db),
                    normalize(earlier, weight.denom() * &e_den * &h_den * da),
                )
            })
            .collect();
        let (mut outputs, mut current, mut earlier) = (Vec::new(), Vec::new(), Vec::new());
        for (e, a, b) in ranks {
            outputs.push(e);
            current.push(a);
            earlier.push(b);
        }
        let covector = self
            .phases
            .iter()
            .zip(turned)
            .filter(|(p, _)| p.population != 0)
            .flat_map(|(_, h)| h.iter().map(Signed::abs))
            .max()
            .unwrap_or_else(Rat::zero);
        Ok(PairFaceGradient {
            outputs,
            current,
            earlier,
            covector,
            energy: Rat::new(
                weight.numer() * weight.numer() * &self.sum_squares,
                weight.denom() * weight.denom(),
            ),
        })
    }

    /// The two exact squared speeds on this comparison's unscaled direction.
    pub(crate) fn ray_speed(
        &self,
        port: &PairPort,
        direction: [&[Vec<Rat>]; 3],
        weight: &Rat,
    ) -> Result<[Rat; 2], HnnError> {
        self.ray_speed_prepared(&PreparedPairRay::new(port, direction)?, weight)
    }

    /// Reuse one transient direction chart across the source faces in a grouped comparison.
    /// The borrowed port cannot change while its coefficients are used; every face still checks
    /// its own contemporary reads. No chart, direction or timing becomes retained state.
    pub(crate) fn ray_speed_prepared(
        &self,
        ray: &PreparedPairRay<'_>,
        weight: &Rat,
    ) -> Result<[Rat; 2], HnnError> {
        if !self.reads.matches(ray.port) {
            return Err(HnnError::Unadmitted {
                reason: "a pair ray must read its contemporary factors and direction",
            });
        }
        let mut squared = [BigInt::zero(), BigInt::zero()];
        for phase in &self.phases {
            if phase.population == 0 { continue; }
            let mut first = vec![BigInt::zero(); ray.width];
            let mut second = vec![BigInt::zero(); ray.width];
            for rho in 0..ray.port.rank() {
                let current: BigInt = ray.current[rho].iter().zip(&phase.current)
                    .filter(|(dx, row)| !dx.is_zero() && !row[rho].is_zero())
                    .map(|(dx, row)| dx * &row[rho]).sum();
                let earlier: BigInt = ray.earlier[rho].iter().zip(&phase.earlier)
                    .filter(|(dx, row)| !dx.is_zero() && !row[rho].is_zero())
                    .map(|(dx, row)| dx * &row[rho]).sum();
                let linear = current + earlier;
                if !phase.weights[rho].is_zero() {
                    for (sum, coefficient) in first.iter_mut().zip(&ray.first_weight[rho]) {
                        if !coefficient.is_zero() { *sum += coefficient * &phase.weights[rho]; }
                    }
                }
                if !linear.is_zero() {
                    for (sum, coefficient) in first.iter_mut().zip(&ray.first_linear[rho]) {
                        if !coefficient.is_zero() { *sum += coefficient * &linear; }
                    }
                    for (sum, coefficient) in second.iter_mut().zip(&ray.second[rho]) {
                        if !coefficient.is_zero() { *sum += coefficient * &linear; }
                    }
                }
            }
            squared[0] += first.iter().map(|x| x * x).sum::<BigInt>();
            squared[1] += second.iter().map(|x| x * x).sum::<BigInt>();
        }
        let weight_square = weight.numer() * weight.numer();
        let weight_den_square = weight.denom() * weight.denom();
        Ok([
            Rat::new(&weight_square * &squared[0], &weight_den_square * &ray.first_den * &ray.first_den),
            Rat::new(&weight_square * &squared[1], &weight_den_square * &ray.second_den * &ray.second_den),
        ])
    }

}

#[derive(Clone)]
struct Slot {
    face: Arc<ResidentPairFace>,
    rebuilds: BigUint,
}

#[derive(Clone, Default)]
struct FaceState {
    slots: BTreeMap<(usize, usize), Slot>,
}

/// Derived cache only: equality, text and retained bits remain the moment's counts and fields.
#[derive(Default)]
pub(crate) struct ResidentPairFaces(RwLock<FaceState>, Arc<AtomicU64>);

impl Clone for ResidentPairFaces {
    fn clone(&self) -> Self {
        Self(
            RwLock::new(self.0.read().map(|s| s.clone()).unwrap_or_default()),
            Arc::clone(&self.1),
        )
    }
}
impl fmt::Debug for ResidentPairFaces {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("ResidentPairFaces(derived)")
    }
}
impl PartialEq for ResidentPairFaces {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for ResidentPairFaces {}

impl ResidentPairFaces {
    /// Exterior audit only. Clones share this number, never a cache or slot map.
    pub(crate) fn total_builds(&self) -> BigUint {
        BigUint::from(self.1.load(Ordering::Relaxed))
    }

    pub(crate) fn read_matches(&self, ring: usize, offset: usize, port: &PairPort) -> Option<bool> {
        self.0
            .read()
            .ok()?
            .slots
            .get(&(ring, offset))
            .map(|slot| slot.face.reads.matches(port))
    }

    pub(crate) fn read(
        &self,
        ring: usize,
        offset: usize,
        counts: &[u64],
        period: usize,
        alphabet: usize,
        port: &PairPort,
    ) -> Result<Arc<ResidentPairFace>, HnnError> {
        let key = (ring, offset);
        if let Ok(state) = self.0.read() {
            if let Some(slot) = state.slots.get(&key).filter(|s| s.face.reads.matches(port)) {
                return Ok(Arc::clone(&slot.face));
            }
        }
        let mut state = match self.0.write() {
            Ok(s) => s,
            Err(error) => {
                let mut s = error.into_inner();
                *s = FaceState::default();
                self.0.clear_poison();
                s
            }
        };
        if let Some(slot) = state.slots.get(&key).filter(|s| s.face.reads.matches(port)) {
            return Ok(Arc::clone(&slot.face));
        }
        let face = Arc::new(ResidentPairFace::build(counts, period, alphabet, port)?);
        let rebuilds = state
            .slots
            .get(&key)
            .map(|s| &s.rebuilds + BigUint::one())
            .unwrap_or_else(BigUint::one);
        // The shared audit count refuses at its carrier's end rather than wrapping.
        self.1
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
            .map_err(|_| HnnError::CountOverflow)?;
        state.slots.insert(
            key,
            Slot {
                face: Arc::clone(&face),
                rebuilds,
            },
        );
        Ok(face)
    }

    pub(crate) fn bind(
        &mut self,
        ring: usize,
        offset: usize,
        phase: usize,
        x: usize,
        y: usize,
        old: u64,
    ) -> Result<(), HnnError> {
        let state = match self.0.get_mut() {
            Ok(s) => s,
            Err(error) => {
                *error.into_inner() = FaceState::default();
                return Ok(());
            }
        };
        if let Some(slot) = state.slots.get_mut(&(ring, offset)) {
            Arc::make_mut(&mut slot.face).bind(phase, x, y, old)?;
        }
        Ok(())
    }

    pub(crate) fn summary(&self) -> Vec<(usize, usize, u64, usize, BigUint)> {
        self.0
            .read()
            .map(|s| {
                s.slots
                    .iter()
                    .map(|(&(g, o), slot)| {
                        (
                            g,
                            o,
                            slot.face.population,
                            slot.face.occupied_bindings,
                            slot.rebuilds.clone(),
                        )
                    })
                    .collect()
            })
            .unwrap_or_default()
    }
}
