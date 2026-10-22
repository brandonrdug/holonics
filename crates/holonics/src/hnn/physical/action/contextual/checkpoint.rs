//! Finite branch material + outstanding original frames only; no operation archive.
use super::*;
use std::fmt::Write;
fn put(o: &mut String, x: impl std::fmt::Display) {
    write!(o, "{x} ").expect("string output");
}
fn vecput(o: &mut String, v: &[Complex]) {
    for z in v {
        put(o, &z[0]);
        put(o, &z[1]);
    }
}
struct Input<'a>(std::str::SplitWhitespace<'a>);
impl Input<'_> {
    fn get<T: std::str::FromStr>(&mut self) -> Result<T, HnnError> {
        self.0
            .next()
            .and_then(|s| s.parse().ok())
            .ok_or(refusal("complete bounded contextual checkpoint fields"))
    }
    fn vector(&mut self, n: usize) -> Result<Vec<Complex>, HnnError> {
        (0..n).map(|_| Ok([self.get()?, self.get()?])).collect()
    }
}
impl ContextualFamily {
    pub fn to_text(&self) -> String {
        let mut o = format!(
            "contextual-return-v2\n{}\n",
            self.port.immutable_identity_text()
        );
        for v in [
            self.bounds.branches,
            self.bounds.pending,
            self.bounds.precision_bits as usize,
            self.bounds.rational_bits as usize,
            self.bounds.max_features,
            self.bounds.max_scalar_work as usize,
            self.next_id as usize,
            self.actual_tick,
            usize::from(self.automatic),
            self.actual_history_depth as usize,
            self.branches.len(),
        ] {
            put(&mut o, v);
        }
        for b in &self.branches {
            put(&mut o, b.id);
            put(&mut o, usize::from(b.prior_is_observed));
            vecput(&mut o, &b.previous);
            vecput(&mut o, &b.current);
            put(&mut o, b.material.observations);
            put(&mut o, &b.material.target_energy);
            for r in b
                .material
                .h
                .iter()
                .chain(&b.material.b)
                .chain(&b.material.applied)
            {
                vecput(&mut o, r);
            }
            put(&mut o, &b.material.residual_upper);
        }
        put(&mut o, self.pending.len());
        for (id, p) in &self.pending {
            for v in [
                *id as usize,
                p.native_tick,
                p.opened_at,
                p.producing_commit as usize,
            ] {
                put(&mut o, v);
            }
            for q in &p.incident {
                put(&mut o, q);
            }
            for c in &p.branches {
                put(&mut o, c.theta);
                put(&mut o, c.material_observations);
                put(&mut o, usize::from(c.previous_is_observed));
                put(&mut o, usize::from(c.current_is_observed));
                for v in [&c.previous, &c.current, &c.context, &c.feature, &c.produced] {
                    vecput(&mut o, v);
                }
            }
            put(&mut o, usize::from(p.actual.is_some()));
            if let Some(y) = &p.actual {
                vecput(&mut o, y);
            }
        }
        // Counters are receipts, not source constraints; retained for accounting continuity.
        for v in [
            self.work.sealed_occurrences,
            self.work.actual_returns,
            self.work.material_formations,
            self.work.branch_formations,
            self.work.normal_fits,
            self.work.response_contractions,
            self.work.prospective_word_passages,
            self.work.ce_candidate_word_replays,
        ] {
            put(&mut o, v);
        }
        o.push('\n');
        o
    }
    pub fn restored(port: WaveObservationPort, text: &str) -> Result<Self, HnnError> {
        if text.len() > 8 * 1024 * 1024 {
            return Err(refusal("bounded contextual checkpoint bytes"));
        }
        let mut lines = text.splitn(3, '\n');
        if lines.next() != Some("contextual-return-v2")
            || lines.next() != Some(port.immutable_identity_text().as_str())
        {
            return Err(refusal("the complete redeclared contextual port identity"));
        }
        let mut r = Input(
            lines
                .next()
                .ok_or(refusal("contextual checkpoint payload"))?
                .split_whitespace(),
        );
        let bounds = ContextualBounds {
            branches: r.get()?,
            pending: r.get()?,
            precision_bits: r.get()?,
            rational_bits: r.get()?,
            max_features: r.get()?,
            max_scalar_work: r.get()?,
        };
        bounds.admit()?;
        let next_id = r.get()?;
        let actual_tick = r.get()?;
        let automatic: u8 = r.get()?;
        let depth: u8 = r.get()?;
        let k: usize = r.get()?;
        if automatic > 1 || depth > 2 || k == 0 || k > bounds.branches {
            return Err(refusal(
                "bounded contextual checkpoint support and history roles",
            ));
        }
        let n = port.width / 2;
        let f = 4 * n + 3 * n * n;
        if f > bounds.max_features {
            return Err(refusal("bounded contextual checkpoint feature chart"));
        }
        let mut branches = Vec::new();
        let mut ids = std::collections::BTreeSet::new();
        for _ in 0..k {
            let id = r.get()?;
            let observed: u8 = r.get()?;
            if !ids.insert(id) || observed > 1 {
                return Err(refusal("unique contextual branch IDs and prior roles"));
            }
            let previous = r.vector(n)?;
            let current = r.vector(n)?;
            let observations = r.get()?;
            let energy = r.get()?;
            let h = (0..f).map(|_| r.vector(f)).collect::<Result<Vec<_>, _>>()?;
            let b = (0..n).map(|_| r.vector(f)).collect::<Result<Vec<_>, _>>()?;
            let applied = (0..n).map(|_| r.vector(f)).collect::<Result<Vec<_>, _>>()?;
            let error: Rat = r.get()?;
            let mut m = EmpiricalMaterial {
                h,
                b,
                applied: applied.clone(),
                target_energy: energy,
                residual_upper: error.clone(),
                observations,
            };
            if m.target_energy < Rat::zero() {
                return Err(refusal("nonnegative accumulated target energy"));
            }
            let mut rows = vec![vec![Rat::zero(); 2 * f]; 2 * f];
            for i in 0..2 * f {
                for j in 0..2 * f {
                    let z = &m.h[i / 2][j / 2];
                    rows[i][j] = if i % 2 == j % 2 {
                        z[0].clone()
                    } else if i % 2 == 0 {
                        -z[1].clone()
                    } else {
                        z[1].clone()
                    };
                    if i == j {
                        rows[i][j] -= integer(1);
                    }
                }
            }
            let form = crate::ratio::linear::inertia::SymmetricForm::from_rows(rows)
                .map_err(|_| refusal("Hermitian empirical source normal"))?;
            if crate::ratio::linear::inertia::inertia(&form).negative != 0 {
                return Err(refusal("unit-prior empirical normal bound H>=I"));
            }
            bounds.check(
                m.h.iter()
                    .flatten()
                    .chain(m.b.iter().flatten())
                    .flat_map(|z| z.iter())
                    .chain(std::iter::once(&m.target_energy)),
            )?;
            if observations == 0 {
                if m != EmpiricalMaterial::found(f, n) {
                    return Err(refusal("exact founding empirical material"));
                }
            } else {
                m.fit(&bounds)?;
                if m.applied != applied || m.residual_upper != error {
                    return Err(refusal(
                        "applied dyadic material and exact residual certificate",
                    ));
                }
            }
            branches.push(ContextualBranch {
                id,
                previous,
                current,
                prior_is_observed: observed != 0,
                material: m,
            });
        }
        let count: usize = r.get()?;
        if count > bounds.pending {
            return Err(refusal("bounded outstanding contextual snapshots"));
        }
        let mut pending = BTreeMap::new();
        for _ in 0..count {
            let id = r.get()?;
            let native_tick = r.get()?;
            let opened_at = r.get()?;
            let producing_commit = r.get()?;
            let incident = (0..port.width)
                .map(|_| r.get())
                .collect::<Result<Vec<Rat>, _>>()?;
            let mut cuts = Vec::new();
            if id >= next_id || opened_at >= native_tick {
                return Err(refusal("original contextual pending ID and source clock"));
            }
            for branch in &branches {
                let theta = r.get()?;
                let material_observations = r.get()?;
                let p_role: u8 = r.get()?;
                let c_role: u8 = r.get()?;
                if p_role > 1 || c_role > 1 {
                    return Err(refusal(
                        "original observed-versus-prior contextual source roles",
                    ));
                }
                let previous = r.vector(n)?;
                let current = r.vector(n)?;
                let context = r.vector(n)?;
                let feature = r.vector(f)?;
                let produced = r.vector(n)?;
                if theta != branch.id
                    || material_observations > branch.material.observations
                    || real(&context) != incident
                    || feature != features(&previous, &current, &context)
                {
                    return Err(refusal(
                        "original co-indexed contextual source/feature frame",
                    ));
                }
                cuts.push(BranchCut {
                    theta,
                    previous_is_observed: p_role != 0,
                    current_is_observed: c_role != 0,
                    previous,
                    current,
                    context,
                    feature,
                    produced,
                    material_observations,
                });
            }
            let received: u8 = r.get()?;
            if received > 1 {
                return Err(refusal("actual-versus-pending contextual testimony"));
            }
            let actual = if received != 0 {
                Some(r.vector(n)?)
            } else {
                None
            };
            if pending
                .insert(
                    id,
                    Pending {
                        native_tick,
                        opened_at,
                        producing_commit,
                        incident,
                        branches: cuts,
                        actual,
                    },
                )
                .is_some()
            {
                return Err(refusal("nonreplayed contextual pending ID"));
            }
        }
        let work = ContextualWork {
            sealed_occurrences: r.get()?,
            actual_returns: r.get()?,
            material_formations: r.get()?,
            branch_formations: r.get()?,
            normal_fits: r.get()?,
            response_contractions: r.get()?,
            prospective_word_passages: r.get()?,
            ce_candidate_word_replays: r.get()?,
        };
        if r.0.next().is_some() {
            return Err(refusal("no extra contextual checkpoint payload"));
        }
        let family = Self {
            port,
            bounds,
            branches,
            pending,
            next_id,
            actual_tick,
            automatic: automatic != 0,
            actual_history_depth: depth,
            work,
            last_refusal: None,
        };
        // Full retained source values are range checked, not merely numerical M.
        family.bounds.check(
            family
                .branches
                .iter()
                .flat_map(|b| b.previous.iter().chain(&b.current))
                .flat_map(|z| z.iter()),
        )?;
        Ok(family)
    }
}
