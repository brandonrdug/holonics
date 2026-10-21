//! Same-cut source response with its own signed error-feedback streams.
//!
//! This transient operand producer opens no Word and advances no physical clock. It executes
//! the producing Word's operators and crossings; the ordinary transpose is the executed linear
//! surrogate, not a derivative through nearest-cell rounding. Admission to a receiving read
//! requires its authenticated executed paired geometry. Unsplit path radii are separate
//! requested evidence; omission never denotes a zero radius or unsplit gain proof.

use super::*;

#[derive(Debug)]
pub(crate) struct ResponseColumn {
    pub(crate) records: Vec<Passage>,
    pub(crate) resonances: Vec<Option<Resonance>>,
    pub(crate) end: EndChange,
    /// Coordinate bounds against the unsplit physical source response at every crossing.
    pub(crate) anchor_errors: Vec<Vec<Vec<Rat>>>,
    carried: Carried,
    exact_opening: EndChange,
}

impl ResponseColumn {
    /// `source` is the mode-qualified physical injection before its opening split, with zero
    /// storage outside source rings. Interior contact and resonator states open at zero.
    /// Held exterior returns overwrite the corresponding response by zero at the actual tick.
    pub(crate) fn execute(word: &Word<'_>, source: Vec<Vec<Rat>>) -> Result<Self, HnnError> {
        let ops = word.operands();
        let widths: Vec<_> = word.field().rings().iter().map(|r| r.width()).collect();
        if source.len() != widths.len()
            || source.iter().zip(&widths).enumerate().any(|(r, (s, &n))| {
                s.len() != n
                    || (!word.field().sources().contains(&r) && s.iter().any(|v| !v.is_zero()))
            })
        {
            return Err(HnnError::Unadmitted {
                reason: "a response column opens on the actual source ports with zero interior",
            });
        }
        let exact_source = source.clone();
        let lattice = word.transient();
        let waves = || widths.iter().map(|&n| zeros(n)).collect::<Vec<_>>();
        let arrivals: Vec<_> = ops
            .contacts()
            .iter()
            .map(|c| {
                let (a, b) = c.ends();
                [zeros(widths[a]), zeros(widths[b])]
            })
            .collect();
        let states: Vec<_> = ops
            .contacts()
            .iter()
            .map(|c| [zeros(c.width()), zeros(c.width())])
            .collect();
        let mut carried = Carried {
            anchors: waves(),
            storage: waves(),
            element_drive: waves(),
            solves: ops.contacts().iter().map(|c| zeros(c.width())).collect(),
            arrivals: arrivals.clone(),
            states: states.clone(),
        };
        let storage = source
            .into_iter()
            .enumerate()
            .map(|(r, s)| {
                let (opened, rest) = split(lattice.as_ref(), s, &zeros(widths[r]));
                if ops.resonators()[r].is_some() {
                    carried.element_drive[r] = rest;
                } else {
                    carried.storage[r] = rest;
                }
                opened
            })
            .collect();
        let resonances: Vec<_> = ops
            .resonators()
            .iter()
            .enumerate()
            .map(|(r, op)| {
                op.as_ref().map(|_| Resonance {
                    open: Rat::zero(),
                    state: [zeros(widths[r]), zeros(widths[r])],
                    remainders: ResonatorRemainders::default(),
                    steps: Vec::new(),
                })
            })
            .collect();
        let end = EndChange {
            storage,
            arrivals,
            states,
            resonators: resonances
                .iter()
                .map(|r| r.as_ref().map(|r| r.state.clone()))
                .collect(),
            resonator_phases: ops
                .resonators()
                .iter()
                .map(|r| {
                    r.as_ref()
                        .map(|r| r.phase_at(word.opened_at().saturating_sub(1)))
                })
                .collect(),
        };
        let exact = EndChange {
            storage: exact_source,
            ..end.clone()
        };
        crate::hnn::prediction::charted::ResponseTube::admit_operands(ops)?;
        let mut tube = if word.response_error_requested() {Some(crate::hnn::prediction::charted::ResponseTube::open(ops, &exact, &end)?)} else {None};
        let mut result = Self {
            records: Vec::new(),
            resonances,
            end,
            carried,
            anchor_errors: Vec::new(),
            exact_opening: exact,
        };
        for crossing in 0..word.recorded().len() {
            // The actual return is imposed after `tick` full ticks and before this crossing.
            for overwrite in word.source_returns().iter().filter(|r| r.tick == crossing) {
                result.end.storage[overwrite.ring].fill(Rat::zero());
                if let Some(tube)=&mut tube {tube.held_overwrite(overwrite.ring)?;}
            }
            let point = result.end.clone();
            result.crossing(word, crossing)?;
            work::reached(work::Event::ResponseCrossing);
            if let Some(tube)=&mut tube { result.anchor_errors.push(tube.anchors(&point,&result.records[crossing].anchors)?); }
            if !(word.is_ended() && crossing + 1 == word.recorded().len()) {
                work::reached(work::Event::ResponseTick);
                if let Some(tube)=&mut tube {tube.advance(&point, &result.end, word.opened_at() + crossing)?;
                    work::reached(work::Event::ResponseCertificateTick);}
            }
        }
        if !word.is_ended() {
            for overwrite in word
                .source_returns()
                .iter()
                .filter(|r| r.tick == word.recorded().len())
            {
                result.end.storage[overwrite.ring].fill(Rat::zero());
            }
        }
        super::trajectory::TrajectoryView::column(word, &result.records, &result.resonances)?;
        Ok(result)
    }

    pub(crate) fn errors_at(&self, word:&Word<'_>)->Result<Vec<Vec<Vec<Rat>>>,HnnError> {
        if self.anchor_errors.len()==self.records.len() {return Ok(self.anchor_errors.clone());}
        let point=|t:usize| -> EndChange { let r=&self.records[t]; EndChange {
            storage:r.storage.clone(),arrivals:r.arrivals.clone(),states:r.states.clone(),
            resonators:self.resonances.iter().map(|r|r.as_ref().map(|r|r.steps.get(t).map_or_else(||r.state.clone(),|s|s.input.clone()))).collect(),
            resonator_phases:word.operands().resonators().iter().map(|r|r.as_ref().map(|r|r.phase_at((word.opened_at()+t).saturating_sub(1)))).collect() } };
        let mut tube=crate::hnn::prediction::charted::ResponseTube::open(word.operands(),&self.exact_opening,&point(0))?;
        let mut errors=Vec::new();
        for t in 0..self.records.len() {
            for overwrite in word.source_returns().iter().filter(|r|r.tick==t) {tube.held_overwrite(overwrite.ring)?;}
            let before=point(t); errors.push(tube.anchors(&before,&self.records[t].anchors)?);
            if t+1<self.records.len() || !word.is_ended() {let after=if t+1<self.records.len(){point(t+1)}else{self.end.clone()}; tube.advance(&before,&after,word.opened_at()+t)?;}
        }
        Ok(errors)
    }
    /// The two executed-surrogate seeds and the physical paired feature, in a caller-supplied
    /// passage frame. F1 makes its transport the identity; both paths share one covector.
    pub(crate) fn receiving_seed(
        &self,
        word: &Word<'_>,
        crossing: usize,
        ring: usize,
        map: &ExactRatMatrix,
        gradient: &[Rat],
    ) -> Result<(Vec<Rat>, Vec<Rat>, Vec<Rat>), HnnError> {
        let (Some(actual), Some(fresh)) = (
            word.recorded()
                .get(crossing)
                .and_then(|r| r.anchors.get(ring)),
            self.records.get(crossing).and_then(|r| r.anchors.get(ring)),
        ) else {
            return Err(HnnError::Unadmitted {
                reason: "a paired seed reads an executed shared crossing and ring",
            });
        };
        let n = fresh.len();
        if map.columns() != 2 * n || map.rows() != gradient.len() {
            return Err(HnnError::Unadmitted {
                reason: "a paired receiving map has two complete physical blocks",
            });
        }
        let mut feature = fresh.clone();
        feature.extend(sub(actual, fresh));
        let pulled = map.transpose()?.apply(gradient)?;
        let actual_seed = pulled[n..].to_vec();
        let fresh_seed = sub(&pulled[..n], &pulled[n..]);
        Ok((feature, actual_seed, fresh_seed))
    }

    fn crossing(&mut self, word: &Word<'_>, crossing: usize) -> Result<(), HnnError> {
        let ops = word.operands();
        let lattice = word.transient();
        let mut junctions = Vec::with_capacity(ops.rings().len());
        for r in 0..ops.rings().len() {
            let incoming: Vec<&[Rat]> = ops
                .incident(r)
                .iter()
                .map(|&a| self.end.arrivals[a][ops.end_slot(a, r)].as_slice())
                .collect();
            let image = participation(ops.weights(r), &self.end.storage[r], &incoming)?;
            let (anchor, rest) = split(lattice.as_ref(), image, &self.carried.anchors[r]);
            self.carried.anchors[r] = rest;
            junctions.push(scattering_about(anchor, &self.end.storage[r], &incoming));
        }
        let mut record = Passage {
            storage: self.end.storage.clone(),
            arrivals: self.end.arrivals.clone(),
            states: self.end.states.clone(),
            anchors: junctions.iter().map(|j| j.anchor.clone()).collect(),
            midpoints: Vec::new(),
            rates: Vec::new(),
        };
        if word.is_ended() && crossing + 1 == word.recorded().len() {
            for (r, j) in junctions.iter().enumerate() {
                self.end.storage[r] = j.storage_wave.clone();
                for (i, &a) in ops.incident(r).iter().enumerate() {
                    self.end.arrivals[a][ops.end_slot(a, r)] = j.outgoing[i].clone();
                }
            }
            self.records.push(record);
            return Ok(());
        }
        let tick = word.opened_at() + crossing;
        for (r, j) in junctions.iter().enumerate() {
            let element = element_step(&ops.rings()[r], &j.storage_wave, &j.contrast)?;
            record.midpoints.push(element.midpoint);
            let (next, rest) = if let (Some(op), Some(resonance)) =
                (&ops.resonators()[r], self.resonances[r].as_mut())
            {
                let (drive, rest) = split(
                    lattice.as_ref(),
                    element.next,
                    &self.carried.element_drive[r],
                );
                self.carried.element_drive[r] = rest;
                let driven = op.step(
                    tick,
                    &drive,
                    [&resonance.state[0], &resonance.state[1]],
                    &resonance.remainders,
                    lattice.as_ref(),
                )?;
                if !driven.closes() {
                    return Err(HnnError::Resonator {
                        ring: r,
                        what: "a response column tick exceeds its chart or split certificate",
                    });
                }
                let output = split(
                    lattice.as_ref(),
                    driven.output.clone(),
                    &self.carried.storage[r],
                );
                resonance.state = driven.state.clone();
                resonance.remainders = driven.remainders().clone();
                self.end.resonators[r] = Some(driven.state.clone());
                self.end.resonator_phases[r] = Some(op.phase_at(tick));
                resonance.steps.push(driven);
                output
            } else {
                split(lattice.as_ref(), element.next, &self.carried.storage[r])
            };
            self.end.storage[r] = next;
            self.carried.storage[r] = rest;
        }
        for (a, c) in ops.contacts().iter().enumerate() {
            let (from, to) = c.ends();
            let outgoing = |r: usize| {
                &junctions[r].outgoing[ops
                    .incident(r)
                    .iter()
                    .position(|&b| b == a)
                    .expect("incident endpoint")]
            };
            let [u, w] = &self.end.states[a];
            let (_, image) = transit_solve(c, ops.step(), outgoing(from), outgoing(to), u, w)?;
            let (solved, rest) = split(lattice.as_ref(), image, &self.carried.solves[a]);
            self.carried.solves[a] = rest;
            let passed = transit_update(c, ops.step(), &solved, outgoing(from), outgoing(to), u, w);
            for (slot, image) in [passed.arrive_from, passed.arrive_to]
                .into_iter()
                .enumerate()
            {
                let (next, rest) = split(lattice.as_ref(), image, &self.carried.arrivals[a][slot]);
                self.end.arrivals[a][slot] = next;
                self.carried.arrivals[a][slot] = rest;
            }
            for (slot, image) in [passed.displacement, passed.rate].into_iter().enumerate() {
                let (next, rest) = split(lattice.as_ref(), image, &self.carried.states[a][slot]);
                self.end.states[a][slot] = next;
                self.carried.states[a][slot] = rest;
            }
            record.rates.push(passed.midpoint);
        }
        self.records.push(record);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::constitution::CAMPAIGN_ONE_BUDGET;
    use crate::hnn::{Constitution, FieldDeclaration};
    use crate::ratio::rat;
    use num_traits::Signed;

    fn field() -> Field {
        let mut d = FieldDeclaration::campaign_one(1024);
        d.rings.truncate(2);
        for (ring, n) in d.rings.iter_mut().zip([2u64, 3]) {
            ring.period = n;
            ring.placements = (0..n)
                .map(|i| FieldDeclaration::quarter_turn(i, n))
                .collect();
            ring.reflector = (0..n).map(|i| ((n - i) % n) as usize).collect();
        }
        d.contacts.truncate(1);
        d.contacts[0].channel = vec![(0, 0), (1, 1)];
        d.loops.clear();
        d.alphabet = 2;
        d.receivers[0].ring = 1;
        d.receivers[0].depth = 2;
        d.crib.window = 2;
        d.lattice.clear();
        Field::declare(d.by_lattice_rule()).unwrap()
    }

    #[test]
    fn source_column_matches_the_actual_primitive_schedule_exact_and_charted() {
        let field = field();
        let theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
        let current = Current::at_rest(&field);
        for loaded in [false, true] {
            let theta = if loaded {
                let n = field.ring(0).width();
                let material = crate::hnn::ring::ResonatorMaterial::new(
                    crate::ratio::linear::ExactRatMatrix::identity(n).unwrap(),
                    crate::ratio::linear::ExactRatMatrix::zero(n, n).unwrap(),
                    crate::ratio::linear::ExactRatMatrix::zero(n, n).unwrap(),
                    None,
                )
                .unwrap();
                theta
                    .clone()
                    .with_ring_resonator(&field, 0, material)
                    .unwrap()
            } else {
                theta.clone()
            };
            let mut reference = None;
            for exact in [true, false] {
                let ops = if exact {
                    Operands::exact_at_cut(&field, &theta, &current).unwrap()
                } else {
                    Operands::at_cut(&field, &theta, &current).unwrap()
                };
                let mut source: Vec<_> = field.rings().iter().map(|r| zeros(r.width())).collect();
                for &r in field.sources() {
                    for (i, v) in source[r].iter_mut().enumerate() {
                        *v = rat((i as i64) - 2, 7);
                    }
                }
                let mut word = Word::on_operands(&field, ops, source.clone()).unwrap();
                for _ in 0..3 {
                    word.tick().unwrap();
                }
                word.last_junction().unwrap();
                let column = ResponseColumn::execute(&word, source.clone()).unwrap();
                word.response_error_requested=false;
                let deferred=ResponseColumn::execute(&word,source).unwrap();
                assert!(deferred.anchor_errors.is_empty(),"NotRequested stays absent rather than a numerical proof");
                assert_eq!(deferred.records,column.records);
                assert_eq!(deferred.end,column.end);
                assert_eq!(deferred.errors_at(&word).unwrap(),column.anchor_errors,"a later genuine demand uses original records/operands");
                assert_eq!(column.records, word.passage);
                assert_eq!(column.resonances, word.resonators);
                assert_eq!(column.carried, word.carried);
                assert_eq!(column.end.storage, word.storage);
                assert_eq!(column.end.arrivals, word.arrivals);
                assert_eq!(column.end.states, word.states);
                if exact {
                    reference = Some(column.records.clone());
                }
                for ((actual, exact), errors) in column
                    .records
                    .iter()
                    .zip(reference.as_ref().unwrap())
                    .zip(&column.anchor_errors)
                {
                    for ((actual, exact), radius) in actual
                        .anchors
                        .iter()
                        .flatten()
                        .zip(exact.anchors.iter().flatten())
                        .zip(errors.iter().flatten())
                    {
                        assert!((actual - exact).abs() <= *radius);
                    }
                }
            }
        }
    }

    #[test]
    fn source_column_keeps_the_actual_interior_and_nonzero_clock_independent() {
        let field = field();
        let theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
        let current = Current::at_rest(&field);
        let ops = Operands::at_cut(&field, &theta, &current).unwrap();
        let mut fresh = EndChange::rest(&field, &ops);
        fresh.storage[field.sources()[0]][0] = rat(2, 7);
        let source = fresh.storage.clone();
        let mut carried = fresh.clone();
        carried.storage[1][0] = rat(4, 9);
        carried.arrivals[0][1][0] = rat(-1, 3);
        carried.states[0][0][0] = rat(1, 5);
        let mut actual = Word::on_change(&field, ops.clone(), carried, 7).unwrap();
        let mut reference = Word::on_change(&field, ops, fresh, 7).unwrap();
        for _ in 0..3 {
            actual.tick().unwrap();
            reference.tick().unwrap();
        }
        actual.last_junction().unwrap();
        reference.last_junction().unwrap();
        let before = actual.end_change();
        let before_work = work::read();
        let column = ResponseColumn::execute(&actual, source).unwrap();
        assert_eq!(actual.end_change(), before);
        let charged = work::read().since(before_work).unwrap();
        assert_eq!(charged.words_opened, 0);
        assert_eq!(charged.response_crossings, 4);
        assert_eq!(charged.response_ticks, 3);
        assert_eq!(charged.response_certificate_ticks, 3);
        assert_eq!(column.records, reference.passage);
        assert_ne!(column.records, actual.passage);
        let n = field.ring(1).width();
        let map = ExactRatMatrix::shaped(
            2,
            2 * n,
            (0..2)
                .map(|i| (0..2 * n).map(|j| rat((i + j) as i64 - 3, 5)).collect())
                .collect(),
        )
        .unwrap();
        let gradient = vec![rat(2, 3), rat(-1, 7)];
        let (feature, actual_seed, fresh_seed) = column
            .receiving_seed(&actual, 2, 1, &map, &gradient)
            .unwrap();
        assert_eq!(
            dot(&map.apply(&feature).unwrap(), &gradient),
            dot(&actual_seed, &actual.passage[2].anchors[1])
                + dot(&fresh_seed, &column.records[2].anchors[1])
        );

        for (a, s) in actual.passage.iter().zip(&column.records) {
            for (a, s) in a.anchors.iter().flatten().zip(s.anchors.iter().flatten()) {
                let context = a - s;
                assert_eq!(s + context, *a);
            }
        }
    }

    #[test]
    fn source_column_uses_the_held_exterior_overwrite_schedule() {
        let field = field();
        let theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
        let current = Current::at_rest(&field);
        let ops = Operands::exact_at_cut(&field, &theta, &current).unwrap();
        let ring = field.sources()[0];
        let mut source: Vec<_> = field.rings().iter().map(|r| zeros(r.width())).collect();
        source[ring][0] = rat(2, 7);
        let mut actual = Word::on_operands(&field, ops.clone(), source.clone()).unwrap();
        let mut reference = Word::on_operands(&field, ops, source.clone()).unwrap();
        actual.tick().unwrap();
        reference.tick().unwrap();
        for (word, value) in [(&mut actual, rat(5, 3)), (&mut reference, Rat::zero())] {
            let incident = word.storage[ring].clone();
            let mut reflected = zeros(incident.len());
            reflected[0] = value;
            let work = field.step()
                * field.ring(ring).admittance()
                * (dot(&reflected, &reflected) - dot(&incident, &incident))
                / integer(4);
            word.return_source_wave(ring, 1, &incident, &reflected, &-work)
                .unwrap();
            word.tick().unwrap();
            word.last_junction().unwrap();
        }
        let column = ResponseColumn::execute(&actual, source).unwrap();
        assert_eq!(column.records, reference.passage);
        assert!(column.records[1].storage[ring].iter().all(Rat::is_zero));
        assert_ne!(column.records, actual.passage);
    }

    #[test]
    fn paired_response_returns_both_source_paths_and_only_actual_interior() {
        let field = field().with_exact_word();
        let theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
        let current = Current::at_rest(&field);
        let phases = crate::hnn::tests::learning::phases(&field, &theta, &current);
        let ops = Operands::exact_at_cut(&field, &theta, &current).unwrap();
        let mut interior = EndChange::rest(&field, &ops);
        interior.storage[1][0] = rat(3, 7);
        interior.arrivals[0][1][0] = rat(-1, 3);
        interior.states[0][1][0] = rat(1, 5);
        let mut opened = interior.clone();
        let mut source: Vec<_> = field.rings().iter().map(|r| zeros(r.width())).collect();
        source[field.sources()[0]][0] = rat(2, 9);
        for (wave, injection) in opened.storage.iter_mut().zip(&source) {
            *wave = add(wave, injection);
        }
        let mut word = Word::on_change(&field, ops, opened, 5).unwrap();
        word.forward(&phases).unwrap();
        let column = ResponseColumn::execute(&word, source.clone()).unwrap();
        let n = field.ring(phases.ring()).width();
        let rows = 2 * field.alphabet();
        let map = ExactRatMatrix::shaped(
            rows,
            2 * n,
            (0..rows)
                .map(|i| (0..2 * n).map(|j| rat((i + 2 * j) as i64 - 5, 7)).collect())
                .collect(),
        )
        .unwrap();
        let gradients: Vec<Vec<Rat>> = (0..phases.aperture())
            .map(|j| (0..rows).map(|i| rat((i + j) as i64 - 2, 5)).collect())
            .collect();
        let before = work::read();
        let (back, interior_dual) =
            crate::hnn::port::reverse_response(&word, &column, &gradients, &map, &phases).unwrap();
        let lhs: Rat = back
            .reads
            .iter()
            .map(|(f, g)| dot(&map.apply(f).unwrap(), g))
            .sum();
        let rhs: Rat = source
            .iter()
            .zip(&back.opening)
            .map(|(s, g)| dot(s, g))
            .sum::<Rat>()
            + interior_dual.pairing(&interior);
        assert_eq!(lhs, rhs);
        assert!(
            back.elements
                .iter()
                .all(|ticks| ticks.len() == 2 * (phases.junction_steps() - 1))
        );
        let charged = work::read().since(before).unwrap();
        assert_eq!(charged.returns, 1);
        assert_eq!(charged.response_returns, 1);
    }

    #[test]
    fn pending_paired_read_keeps_both_trajectories_and_both_defect_receipts() {
        let field = field();
        let mut theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
        let receiving = field.receivers()[0].ring;
        theta.bind_arrival_context_receiving(receiving).unwrap();
        let (current, moment) = crate::hnn::tests::learning::moment(&field, 71, 2);
        let phases = crate::hnn::tests::learning::phases(&field, &theta, &current);
        let ratio = crate::hnn::pending::PendingRatio::produce(
            &current,
            &moment,
            &crate::hnn::receiving::ActiveAddress::boundary(phases.depth()),
            &phases,
            theta.commit(),
        )
        .unwrap();
        let mut charts = Charts::new();
        let (word, _) = ratio
            .read_on(&field, &theta, &mut charts, &WordOpening::Rest)
            .unwrap();
        let carry = word.reception_end().unwrap();
        assert!(word.response().is_some());
        let word = word.keep().resume(&field);
        assert!(word.response().is_some());
        let (continued, faces) = ratio
            .read_on(
                &field,
                &theta,
                &mut charts,
                &WordOpening::Received {
                    carry,
                    absorption: Absorption::Nothing,
                },
            )
            .unwrap();
        assert!(continued.opened_at() > 0);
        let compared = crate::hnn::ratio::HolonRatio::compare(
            faces,
            &vec![0; phases.aperture()],
            &crate::hnn::ratio::TargetPhases {
                branch: 0.into(),
                phases: vec![Rat::zero(); phases.aperture()],
            },
        )
        .unwrap();
        let back = continued
            .pull_back(
                &compared.covector().unwrap(),
                theta.receiving_map(receiving).unwrap(),
                &phases,
            )
            .unwrap();
        assert_eq!(back.reads.len(), phases.aperture());
        assert!(
            back.reads
                .iter()
                .all(|(f, _)| f.len() == 2 * field.ring(receiving).width())
        );
        let geometry=back.response_geometry.as_ref().unwrap();let width=field.ring(receiving).width();
        geometry.admit(&field,&back.reads,width).unwrap();
        let mut stale=back.reads.clone();stale[0].0[0]+=crate::ratio::integer(1);
        assert!(geometry.admit(&field,&stale,width).is_err());
        assert!(geometry.admit(&field,&back.reads,width+1).is_err());
        let defect = back.response_defect.unwrap();
        let context = defect.context_bounds().unwrap();
        assert_eq!(context.len(), phases.aperture());
        assert!(context.iter().flatten().all(|x| x >= &Rat::zero()));
    }
}
