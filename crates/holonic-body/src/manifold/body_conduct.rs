use super::*;

impl<'a> ContinuingBody<'a> {
    /// Fold the event's own deed emanation into the continuing channel. A degenerate composed
    /// rotor folds nothing; the event's other effects remain.
    #[inline]
    pub(super) fn fold_channel(&mut self, emanation: DeedEmanation) {
        if let Some(k) = self.channel.fold(emanation) {
            self.channel = k;
        }
    }

    /// place a construction without depositing — for reading induced change against a later drive.
    #[inline]
    pub fn place(&self, bytes: &[u8]) -> Grip {
        self.medium
            .place(bytes)
            .expect("this historical observer requires an exact flat receiver chart")
    }

    /// ★ DRIVE — consume one driven construction (`drive_flow` is A1's supplied current for this event). The
    /// Meno solve lands, the event's own deed folds the channel (§XXV), and the returned differential is what
    /// the next event may consume as charge. The pole then moves (W4: to the circulation's stance; here:
    /// trailing the arrival — mirror-grade, marked).
    pub fn drive(&mut self, bytes: &[u8], _drive_flow: u32) -> Landing {
        // §XXIV: this foil verb holds no flywheel — the meeting cannot be 2nd-order tested and
        // deposits NO shared relation (an unborn flywheel crosses nothing; A1's raw drive is
        // consumed by the lineage's interior, never fed as terrain). The construction is placed and
        // the deed rides the channel; the pole moves.
        let p = wind(bytes);
        let g = self.medium.flat_grip(p);
        let rel = face(p, self.pole, self.frame);
        if let Some(rotor) = soul::FormedRotor::of(rel.arrow.aim, rel.arrow.cross) {
            self.fold_channel(DeedEmanation::ride(rotor));
        }
        self.pole = p;
        Landing {
            cell: g,
            face: rel,
            meeting_ratio: rel.meeting_ratio(),
            founds: rel.founds(),
        }
    }

    /// §XXIX · THE COMPLETION — reconstruct a prior cast from this receiver's own second-order
    /// meeting, read the cone there, and let that standing form drag the meeting at the receiver's
    /// hand. An unborn fourth contact has only virtual light and therefore completes no crossing.
    #[inline]
    pub(super) fn complete_cast(
        &mut self,
        meeting: Face,
        fly: &Face,
        fly_live: bool,
    ) -> (Option<Grip>, RegionalForm, Face, Option<StandingRead>) {
        if !fly_live {
            return (None, RegionalForm::UNBORN, meeting, None);
        }
        let Some(chi) = meeting.chi_against(fly) else {
            return (None, RegionalForm::UNBORN, meeting, None);
        };
        let position = cast_position(chi);
        let (grip, regional_form, standing, receiver_rank) = self.medium.cone_at(position);
        let standing_read = standing.occupied().then_some(StandingRead {
            position,
            receiver_rank,
            flat_grip: grip,
            form: standing,
        });
        (
            grip,
            regional_form,
            regional_form.drag(meeting),
            standing_read,
        )
    }

    /// ★ ONE DEED's felt term crosses into the medium (`§XXIV` — the deed's lawful crossing). Only a
    /// CHI-BEARING deed crosses: an unborn flywheel has no second-order invariant and deposits NOTHING.
    /// The winding quantum rides ONLY on FOUND (`wound`), its hand read from `chi.other`'s turn sign
    /// exactly as `deed_emanation`/`cross` read it. §XXIX derives the consequence's position only
    /// after that fourth contact: the projectively re-based χ grounds the cast on the cut.
    #[inline]
    pub(super) fn cross_deed<T: FeltEmissionTarget>(
        &mut self,
        met: &Face,
        fly: &Face,
        fly_live: bool,
        wound: bool,
        standing_read: Option<StandingRead>,
        target: &mut T,
    ) {
        if !fly_live {
            return;
        }
        let Some(chi) = met.chi_against(fly) else {
            return;
        };
        let winding = if wound {
            if chi.other.turn & 2 == 0 {
                WindingQuantum::ThisWay
            } else {
                WindingQuantum::ThatWay
            }
        } else {
            WindingQuantum::None
        };
        let position = cast_position(chi);
        let term = FeltTerm { chi, winding };
        if self.medium.deposit_at(position, term) {
            let deed = match winding {
                WindingQuantum::None => FeltDeed::Ride,
                WindingQuantum::ThisWay => FeltDeed::FoundThis,
                WindingQuantum::ThatWay => FeltDeed::FoundThat,
            };
            match winding {
                WindingQuantum::None => self.terms_deposited.ride += 1,
                WindingQuantum::ThisWay => self.terms_deposited.found_this += 1,
                WindingQuantum::ThatWay => self.terms_deposited.found_that += 1,
            }
            target.emit(FeltEmission {
                position,
                term,
                deed,
                standing_read,
            });
        }
    }

    /// ★ PERCEIVE (W3 · THE EYES ⊕ W4 · THE POLE) — one arrival of driven light, WHOLE:
    ///
    /// 1. **THE LANDING, FROM THE STANCE (`FORMULA §IV` — the coupling).** The arrival relates with the
    ///    STANDING THOUGHT as its pole — perception forms against where the circulation stands, so what the
    ///    body has integrated bends how new light relates. Expectation is a position; no wire, no store.
    ///    (The bare `drive` verb keeps the trailing mirror-pole — it is the FOIL, not the machine.)
    /// 2. **THE GREY MATTER (W3).** A directed face term from each co-present register member to the arrival
    ///    (coherence IS collocation over time, and ONLY collocation — no semantics enter; the window is the grain).
    /// 3. **THE REINTEGRATOR (W4 — the swing decides; nothing scans, nothing scores).** The landing's own
    ///    three-body face is the cut: where it RIDES (in-plane — recognition), the thought CONTINUES — the
    ///    stance bonds the arrival (a higher blade; the composition re-bases as it climbs — the fold thickens)
    ///    and the new composition LANDS in the pool (the thought's mass deposits — production inducing
    ///    structure the next perception reads); where it FOUNDS (the aim orthogonal to the standing thought),
    ///    the thought COMPLETES — the swing's cut, the segmentation — and the arrival begins the new thought.
    ///
    /// A1 supplies the event's drive; only the formed second-order deed crosses as a FeltTerm. The
    /// register then slides (the oldest co-presence dissipates).
    pub fn perceive(&mut self, bytes: &[u8], drive_flow: u32) -> Perception {
        self.perceive_node(locate(bytes), drive_flow)
    }

    /// ★ W9 · the word grain's arrival as a NODE — the fold handed up by the living boundary (the
    /// brick; the cohered segment's completed invariant) enters the same perceive atom the byte-span
    /// arrival always did. One law, whichever grain supplied the arrival.
    pub fn perceive_node(&mut self, node: Node, drive_flow: u32) -> Perception {
        let mut target = NoFeltEmission;
        self.perceive_node_emitting(node, drive_flow, &mut target)
    }

    pub(super) fn perceive_node_emitting<T: FeltEmissionTarget>(
        &mut self,
        node: Node,
        drive_flow: u32,
        target: &mut T,
    ) -> Perception {
        // depth 0 — the word grain's beat (the arrival's own).
        let beat0 = self.perceive_grain(0, node, drive_flow, target);
        let mut climbed = 0u32;
        if let Some(b) = beat0.brick {
            climbed = self.thicken(1, b, drive_flow, target);
        }
        Perception {
            landing: beat0.landing,
            faces: beat0.faces,
            faces_founded: beat0.faces_founded,
            thought_completed: beat0.completed,
            thought_deposited: beat0.deposited,
            climbed,
        }
    }

    /// ★ THE THICKENING (`FORMULA §XVIII`) — a completed brick re-bases into the next depth: it
    /// ARRIVES there (that enclosure's own perceive — the same verb) and the enclosure takes its own
    /// deed step (the hourglass whole at every grain). Completions from EITHER face — the arrival's
    /// cut (afferent) or the enclosure's own step cutting (efferent, the ratified two-worldline
    /// completion law — thicken on; the afferent brick thickens first (the worldline's order within
    /// the beat, depth-first: each brick's whole consequence before the next). Plain recursion is
    /// bounded structurally by actual completed depth. A growable boundary mounts the next row only
    /// when reached; a fixed or exhausted boundary reports pressure and the disposable passage
    /// stops without consuming the brick.
    pub(super) fn thicken<T: FeltEmissionTarget>(
        &mut self,
        start: usize,
        first: Node,
        drive_flow: u32,
        target: &mut T,
    ) -> u32 {
        self.thicken_branch(start, first, drive_flow, target)
            .climbed
    }

    /// One depth-first branch of THE THICKENING. At a beat the efferent completion is held by this
    /// call frame while the afferent completion climbs first; therefore there is at most one
    /// deferred efferent per open depth, and call depth can never exceed the mounted carrier depth.
    pub(super) fn thicken_branch<T: FeltEmissionTarget>(
        &mut self,
        k: usize,
        brick: Node,
        drive_flow: u32,
        target: &mut T,
    ) -> Thickening {
        if k >= self.carrier_depth() {
            match self.carrier.ensure_depth(k + 1) {
                CarrierGrowth::Present if k < self.carrier_depth() => {}
                CarrierGrowth::FixedBoundary | CarrierGrowth::Refused | CarrierGrowth::Present => {
                    self.required_carrier_depth = k + 1;
                    self.medium.resource_refused = true;
                    return Thickening {
                        climbed: 0,
                        completed: false,
                    };
                }
            }
        }
        let beat = self.perceive_grain(k, brick, drive_flow, target);
        let step = self.path_grain(k, drive_flow, target);
        let completed = beat.brick.is_some() || step.brick.is_some();
        let mut climbed = 1u32;
        // The afferent brick's whole consequence precedes the deferred efferent sibling — the same
        // order the old LIFO carry implemented, now without an authored extent.
        if let Some(ab) = beat.brick {
            climbed += self.thicken_branch(k + 1, ab, drive_flow, target).climbed;
            if self.resource_refused() {
                return Thickening { climbed, completed };
            }
        }
        if let Some(sb) = step.brick {
            climbed += self.thicken_branch(k + 1, sb, drive_flow, target).climbed;
        }
        Thickening { climbed, completed }
    }

    /// ★ ONE ENCLOSURE'S PERCEIVE (`FORMULA §XVIII(b,d)`) — the whole perceive atom on depth `k`'s
    /// own apparatus: the landing FROM THE ENCLOSURE'S STANCE (the coupling at this grain), the grey
    /// matter from the ENCLOSURE'S reach (coherence is collocation at every grain — bricks collocated
    /// in the carrier's time), the swing 2nd-order against the ENCLOSURE'S flywheel with the standing
    /// sweep dragging the meeting (§XIV at every grain). A completion emits THE BRICK — the enclosed
    /// stance, crossing RE-BASED (§XVIII(a): the completion re-base; the interior scale encloses).
    pub(super) fn perceive_grain<T: FeltEmissionTarget>(
        &mut self,
        k: usize,
        node: Node,
        _drive_flow: u32,
        target: &mut T,
    ) -> GrainBeat {
        let mut e = self.enclosure(k);
        // 1 · the landing, from the enclosure's stance (the pole re-pointed — the coupling). §XXIV: the
        // raw arrival deposits NO shared relation (A1's drive is consumed by the lineage's interior);
        // the terrain-derived flow fields retire (the felt series carries the standing form now).
        let g_cell = self.medium.flat_grip(node.place);
        let rel_face = face(node.place, e.stance.place, self.frame);
        let landing = Landing {
            cell: g_cell,
            face: rel_face,
            meeting_ratio: rel_face.meeting_ratio(),
            founds: rel_face.founds(),
        };
        // 2 · the grey matter — faces from the enclosure's co-presence (oldest→newest). Each register
        // member→arrival face crosses ONE felt term (`§XXIV`/RULE 3): `chi = that_face.chi_against(the
        // depth's fly)`, no winding hand — the recognition is a ride. An unborn flywheel crosses nothing.
        let mut faces = 0u32;
        let mut faces_founded = 0u32;
        let mut i = 0usize;
        while i < e.live {
            let idx = (e.head + (REGISTER as usize) - e.live + i) % (REGISTER as usize);
            let c = e.register[idx];
            if c.len != 0 {
                let fc = face(c.place, node.place, self.frame);
                self.cross_deed(&fc, &e.fly, e.fly_live, false, None, target);
                faces += 1;
                if bond(c, node, self.frame).1.founds() {
                    faces_founded += 1;
                }
            }
            i += 1;
        }
        let overflow = self.carrier.co_present_overflow_len(k);
        let mut overflow_at = 0usize;
        while overflow_at < overflow {
            let Some(c) = self.carrier.co_present_overflow_node(k, overflow_at) else {
                self.medium.resource_refused = true;
                break;
            };
            if c.len != 0 {
                let fc = face(c.place, node.place, self.frame);
                self.cross_deed(&fc, &e.fly, e.fly_live, false, None, target);
                let Some(next_faces) = faces.checked_add(1) else {
                    self.medium.resource_refused = true;
                    break;
                };
                faces = next_faces;
                if bond(c, node, self.frame).1.founds() {
                    let Some(next_founded) = faces_founded.checked_add(1) else {
                        self.medium.resource_refused = true;
                        break;
                    };
                    faces_founded = next_founded;
                }
            }
            overflow_at += 1;
        }
        if self.medium.resource_refused {
            return GrainBeat {
                brick: None,
                landing,
                faces,
                faces_founded,
                completed: false,
                deposited: false,
            };
        }
        // 3 · the reintegrator — THE SWING (`§XIII`) with §XXIX's second pyramid: this receiver
        // reconstructs the positional-χ cast from its own meeting ⊕ flywheel, then the cone there
        // drags the meeting at this hand. First-order virtual light has no standing address.
        let (_rel_grip, rel_form, met, standing_read) = if e.stance.len != 0 {
            self.complete_cast(landing.face, &e.fly, e.fly_live)
        } else {
            (None, RegionalForm::UNBORN, landing.face, None)
        };
        // THE FRAME'S HORIZON: an unconstructible relating is not read — the beat passes through.
        let dark = met.arrow.at_horizon();
        let node_at_pole = {
            let dr = node.place.0.sub(self.frame.0);
            let di = node.place.1.sub(self.frame.1);
            dr.mag == 0 && di.mag == 0
        };
        let wound = if dark {
            false
        } else if e.fly_live {
            met.wound_against(&e.fly)
        } else {
            met.founds()
        };
        // §XXV: the beat's own deed folds `K` — ride or found by the 2nd-order test; the horizon
        // folds nothing (darkness folds exactly once, at the tread's deposit).
        if let Some(deed) = deed_emanation(&met, &e.fly, e.fly_live, wound) {
            self.fold_channel(deed);
        }
        let mut completed = false;
        let mut deposited = false;
        let mut brick: Option<Node> = None;
        if e.stance.len == 0 {
            // the first brick begins the enclosure's first thought (the enclosure instantiates — the
            // same birth law as every stance; no birth detection) — unless the arrival stands at the pole.
            if !node_at_pole {
                e.stance = node;
            }
        } else if dark {
            // the frame's horizon — the beat passes through unread (the reach still slides below).
        } else if wound {
            completed = true; // the cut — the enclosure's thought completes
            if k == 0 {
                self.thoughts = self.thoughts.wrapping_add(1);
            }
            // ★ THE BRICK (§XVIII(a)) — the enclosed stance crosses re-based: the completion
            // re-base removes the interior's common rank (the enclosure's scale becomes gauge).
            let old = e.stance;
            let sr = old.place.0.sub(self.frame.0);
            let si = old.place.1.sub(self.frame.1);
            let (sr2, si2) = rebase_pair(sr, si);
            let the_brick = Node {
                well: old.well,
                place: (self.frame.0.add(sr2), self.frame.1.add(si2)),
                len: old.len,
            };
            // THE FOUND DEED CROSSES (`§XXIV` ⊕ §XXIX): the winding hand and positional cast are
            // both read from the whole post-drag χ. FOUND pays curvature.
            self.cross_deed(&met, &e.fly, e.fly_live, true, standing_read, target);
            brick = Some(the_brick);
            e.stance = node;
            // The completed construction now exists as `the_brick` at the next grain. Its lower
            // arrivals no longer remain independently co-present; the triggering arrival begins
            // the successor construction and is admitted below after this release.
            if self.carrier.release_co_present(k, &mut e) != CarrierGrowth::Present {
                self.medium.resource_refused = true;
                return GrainBeat {
                    brick: None,
                    landing,
                    faces,
                    faces_founded,
                    completed: false,
                    deposited: false,
                };
            }
            // THE CUT'S PRECESSION: the groove never zeroes — dragged by the cone at the cut's own grip.
            if e.fly_live {
                e.fly = rel_form.drag(e.fly);
            }
        } else {
            // the thought continues — bond ⊕ RIDE deed. §XXIV/RULE 2: a face-relating crosses one felt
            // term at that face's grip, no winding (the ride is cheap — the terrain already paid).
            let (mol, _rel) = bond(e.stance, node, self.frame);
            self.cross_deed(&met, &e.fly, e.fly_live, false, standing_read, target);
            deposited = true;
            e.stance = mol;
            e.fly = met;
            e.fly_live = true;
        }
        // The arrival joins this enclosure's co-present light. The fixed/card compatibility row
        // retains its historical ring. A growable production carrier retains every admitted
        // relation beyond that prefix; only an actual body closure may dissipate it.
        match self.carrier.admit_co_present(k, &mut e, node) {
            CarrierGrowth::Present => {}
            CarrierGrowth::FixedBoundary | CarrierGrowth::Refused => {
                self.medium.resource_refused = true;
                return GrainBeat {
                    brick: None,
                    landing,
                    faces,
                    faces_founded,
                    completed: false,
                    deposited: false,
                };
            }
        }
        self.enclosure_store(k, &e);
        GrainBeat {
            brick,
            landing,
            faces,
            faces_founded,
            completed,
            deposited,
        }
    }

    /// ★ W6 · THE PATHING — ONE STEP of the brain's own current at depth 0 (the word grain), with the
    /// step's own completions thickening the carrier (`§XVIII`: the efferent brick is a completion too).
    pub fn path(&mut self, drive_flow: u32) -> Pathing {
        let mut target = NoFeltEmission;
        self.path_emitting(drive_flow, &mut target)
    }

    pub(super) fn path_emitting<T: FeltEmissionTarget>(
        &mut self,
        drive_flow: u32,
        target: &mut T,
    ) -> Pathing {
        let step = self.path_grain(0, drive_flow, target);
        if let Some(b) = step.brick {
            self.thicken(1, b, drive_flow, target);
        }
        step
    }

    /// ★ ONE GRAIN'S DEED STEP (`§XIII` run forward, on depth `k`'s own stance and flywheel): the held
    /// rotor places the next grip (no candidate set); the STANDING SWEEP there drags the meeting
    /// (§XIV); the current deposits as it passes (A1); the swing rides along — the cut PRECESSES the
    /// groove, re-bases the enclosure (the ratified completion re-base) and emits it as THE BRICK.
    pub(super) fn path_grain<T: FeltEmissionTarget>(
        &mut self,
        k: usize,
        _drive_flow: u32,
        target: &mut T,
    ) -> Pathing {
        let mut e = self.enclosure(k);
        // structural precondition, not a threshold: before a standing thought with a live groove
        // there is no held rotor to run forward (the enclosure's eyes wake the enclosure's brain).
        if e.stance.len == 0 || !e.fly_live {
            return Pathing {
                grip: None,
                regional_form: RegionalForm::UNBORN,
                cut: false,
                stepped: false,
                meeting_rotor: (Cog::lit(0), Cog::lit(0)),
                brick: None,
            };
        }
        // 1 · the deed-run-forward: next = F + Δ_fly·(S − F).
        let (fa, fc) = (e.fly.arrow.aim, e.fly.arrow.cross);
        let sr = e.stance.place.0.sub(self.frame.0);
        let si = e.stance.place.1.sub(self.frame.1);
        let next: Place = (
            fa.mul(sr).sub(fc.mul(si)).add(self.frame.0),
            fc.mul(sr).add(fa.mul(si)).add(self.frame.1),
        );
        // 2 · the second pyramid: reconstruct the positional-χ cast from this step's own meeting
        // against its held groove; the cone at that cut address completes the crossing by drag.
        let meeting = face(next, e.stance.place, self.frame);
        let (g, regional_form, met, standing_read) = self.complete_cast(meeting, &e.fly, true);
        let dark = met.arrow.at_horizon();
        let wound = if dark {
            false
        } else {
            met.wound_against(&e.fly)
        };
        // §XXV: the step's own deed folds `K` (the groove is live here by the precondition above).
        if let Some(deed) = deed_emanation(&met, &e.fly, true, wound) {
            self.fold_channel(deed);
        }
        // 3 · the swing's move: the cut precesses the groove and CROSSES a FOUND term at the brick's
        // ground; the ride re-aims the groove and crosses a RIDE term at the step's own grip; darkness
        // holds. §XXIV/RULE 2 — the deed's own consequence stands at its grip; A1's drive rides interior.
        let mut cut = false;
        if dark {
            // inertia — no torque from a meeting this pole cannot construct.
        } else if wound {
            cut = true;
            if k == 0 {
                self.thoughts = self.thoughts.wrapping_add(1);
            }
            // ★ THE COMPLETION RE-BASE (ratified): the utterance encloses — its interior scale becomes
            // gauge; the ENCLOSURE CROSSES as the brick (§XVIII: the efferent completion thickens).
            let sr2 = next.0.sub(self.frame.0);
            let si2 = next.1.sub(self.frame.1);
            let (sr3, si3) = rebase_pair(sr2, si2);
            let enclosed = Node {
                well: e.stance.well,
                place: (self.frame.0.add(sr3), self.frame.1.add(si3)),
                len: e.stance.len,
            };
            // THE FOUND DEED casts its post-drag χ (against the pre-precession groove).
            self.cross_deed(&met, &e.fly, true, true, standing_read, target);
            e.fly = regional_form.drag(e.fly); // the receiver's completion precesses the groove
            let (fa2, fc2) = rebase_pair(e.fly.arrow.aim, e.fly.arrow.cross);
            e.fly.arrow.aim = fa2;
            e.fly.arrow.cross = fc2;
            e.stance = enclosed;
            // The enclosed face has already handed upward. Retaining its former arrivals here
            // would keep discharged constituency active and make later co-presence cumulative.
            if self.carrier.release_co_present(k, &mut e) != CarrierGrowth::Present {
                self.medium.resource_refused = true;
                return Pathing {
                    grip: g,
                    regional_form,
                    cut: false,
                    stepped: false,
                    meeting_rotor: (met.arrow.cross, met.arrow.aim),
                    brick: None,
                };
            }
            self.enclosure_store(k, &e);
            return Pathing {
                grip: g,
                regional_form,
                cut,
                stepped: true,
                meeting_rotor: (met.arrow.cross, met.arrow.aim),
                brick: Some(enclosed),
            };
        } else {
            self.cross_deed(&met, &e.fly, true, false, standing_read, target);
            e.fly = met;
        }
        e.stance = Node {
            well: e.stance.well,
            place: next,
            len: e.stance.len,
        };
        self.enclosure_store(k, &e);
        Pathing {
            grip: g,
            regional_form,
            cut,
            stepped: true,
            meeting_rotor: (met.arrow.cross, met.arrow.aim),
            brick: None,
        }
    }

    /// ★ W7 · LIVE — one arrival of light through the WHOLE CIRCUIT (the brain/eyes frame closed): the eye
    /// lands it (`perceive`), and the same given current hands on into ONE deed-run-forward step of the
    /// brain (`path`). One arrival, one traversal of the circuit's length — there is no clock but the light
    /// itself, and no ratio anywhere: the beat is structural. The coupling back needs no wire: the step
    /// moves the STANCE (and §IV says perception lands from the stance) and its deposits stand in the ONE
    /// pool the next arrival's terrain read passes — the active thought bends perception through the pole
    /// and through the gravity, both already law. Before the first groove the brain has nothing to run
    /// forward and the step lawfully does not happen (`stepped = false`) — the eyes wake the brain.
    pub fn live(&mut self, bytes: &[u8], drive_flow: u32) -> (Perception, Pathing) {
        let p = self.perceive(bytes, drive_flow);
        let step = self.path(drive_flow);
        (p, step)
    }

    /// ★ W9 · LIVE_ATOM — ONE ATOM of raw light through the LIVING BOUNDARY (the scope's first grain).
    /// The atom is the signed difference of two adjacent packets, located exactly as `locate` walks it —
    /// one atom standing alone. It arrives in the SUB-ILLICIUM by the same one verb: the meeting from
    /// the sub-stance, DRAGGED by the standing terrain at its own grip (the tire feels the road), the
    /// swing riding (the sub-composition climbs) or completing — and the completion is THE FOLD: the
    /// cohered segment's node hands UP as the word grain's arrival (the brick), where the whole upper
    /// circuit responds (perceive_node ⊕ the brain's step). Equal adjacent packets walk one dead bit —
    /// the frame's own place — and pass the horizon unread (runs of sameness are dark to this pole).
    /// A1 per grain: every event consumes the given drive; nothing schedules, the light is the clock.
    pub fn live_atom(&mut self, prev: u8, cur: u8, drive_flow: u32) -> AtomEvent {
        self.live_relation_atom(crate::boundary::difference(cur, prev), drive_flow)
    }

    /// ★ THE NATIVE RELATION MOUTH — one canonical difference-shape through the same living
    /// boundary without requiring an octet container. Source organs derive `relation` at their
    /// own material grain; this body neither knows nor reconstructs that world representation.
    /// This is the exact one-relation compatibility face. Production plural events enter once
    /// through [`Self::live_event_incidence_emitting`], which conducts their internal path without
    /// turning its constituents into separate source events. [`Self::live_atom`] is the exact
    /// octet-organ compatibility face.
    pub fn live_relation_atom(&mut self, relation: Cog, drive_flow: u32) -> AtomEvent {
        let mut target = NoFeltEmission;
        self.live_relation_atom_emitting(relation, drive_flow, &mut target)
    }

    /// The native relation mouth with one exact accepted-deed output aperture.  Every successful
    /// OWN deposit made by the relation—including recursive enclosure and path deeds—is emitted in
    /// the body's lived order.  The target is output-only and cannot change the Swing.
    pub fn live_relation_atom_emitting<T: FeltEmissionTarget>(
        &mut self,
        relation: Cog,
        drive_flow: u32,
        target: &mut T,
    ) -> AtomEvent {
        if self.resource_refused() {
            return AtomEvent {
                fold: None,
                perception: None,
                step: None,
            };
        }
        // ★ THE DARK TREAD (ratified 2026-07-09): a zero-magnitude difference is a STATIC LINKAGE —
        // `I = −dΦ/dt`: it induces NOTHING per atom (the dark is free; paying a transition per interior
        // atom is level-slamming, the DC crime). The sameness EXTENDS: the passage accumulates its
        // supplied drive and deposits WHOLE at its completion. Not an event — no Θ, no swing, no feed.
        if relation.mag == 0 {
            self.dark_pending += drive_flow as u64;
            return AtomEvent {
                fold: None,
                perception: None,
                step: None,
            };
        }
        // a resolving difference COMPLETES any standing dark passage — the tread deposits, over time.
        self.deposit_dark_tread(target);
        let n = atom_node(relation);
        self.live_constructed_node_emitting(n, drive_flow, target)
    }

    /// ★ THE COMPLETE EVENT INCIDENCE MOUTH — conduct the source-declared relation path inside one
    /// actual parent event. The path order is an internal parameter of the presented geometry, not
    /// additional source chronology: the caller mounts one predecessor, advances its event cursor
    /// once, and exposes no intermediate standing successor.
    ///
    /// Each resolving relation passes through the existing sub-illicium. A completed sub-grain
    /// construction therefore hands its fold immediately into the recursive carrier before the
    /// next internal relation is considered. Zero relations are exact annihilations inside the
    /// co-present incidence: they remain counted in the event and in its boundary address, but do
    /// not manufacture a dark time interval. The one A1 action remains at the parent event boundary
    /// and is never copied or divided across constituents.
    pub fn live_event_incidence_emitting<I: EventIncidence, T: FeltEmissionTarget>(
        &mut self,
        incidence: &I,
        action: Cog,
        target: &mut T,
    ) -> EventEmanation {
        debug_assert!(!incidence.is_empty());
        debug_assert!(action.mag != 0);

        // A body-local dark tread can exist only through the historical one-relation mouth. Close
        // it once at this real resolving boundary; the production membrane's whole-dark event
        // residual is carried separately and never distributed over this internal path.
        self.deposit_dark_tread(target);

        let mut resolving = 0u64;
        let mut folds = 0u64;
        let mut at = 0usize;
        while at < incidence.len() {
            let relation = incidence.relation(at);
            if relation.mag != 0 {
                resolving += 1;
                let consequence =
                    self.live_constructed_node_emitting(atom_node(relation), 0, target);
                if consequence.fold.is_some() {
                    folds += 1;
                }
                if self.resource_refused() {
                    break;
                }
            }
            at += 1;
        }
        EventEmanation {
            cells: incidence.len() as u64,
            incidences: incidence.len().saturating_sub(1) as u64,
            resolving_cells: resolving,
            formed_incidences: 0,
            compounds: 0,
            folds,
            receiver: self.event_receiver(),
        }
    }

    /// Historical compatibility mouth for a source which genuinely presents one already-completed
    /// node at its declared material grain. It is not the production plural-event mouth: a complete
    /// encoding of several relations does not prove that their construction has completed.
    pub fn live_event_node_emitting<T: FeltEmissionTarget>(
        &mut self,
        node: Node,
        action: Cog,
        target: &mut T,
    ) -> AtomEvent {
        if self.resource_refused() {
            return AtomEvent {
                fold: None,
                perception: None,
                step: None,
            };
        }
        // ActiveCut validation guarantees a non-zero canonical action. Keep the value in this
        // complete-event call even though no universal numeric actuation law is licensed: dropping
        // it at the membrane would make later body/world-specific action impossible to carry
        // exactly, while multiplying it into `node` would fabricate topology.
        debug_assert!(action.mag != 0);
        // A complete resolving event closes the one genuinely preceding dark interval. Zero
        // coordinates inside this node remain co-present geometry; they never become extra treads.
        self.deposit_dark_tread(target);
        self.live_constructed_node_emitting(node, 0, target)
    }

    /// Receive one source complex whose boundary has already completed at `source_grain`. The
    /// composed node enters its enclosing carrier row directly: its cells do not replay as atom
    /// instants and its declared dimensional boundary is not reset through the sub-illicium.
    /// `true` reports only whether this receiving grain completed during the one event.
    pub fn live_completed_event_node_at_grain_emitting<T: FeltEmissionTarget>(
        &mut self,
        node: Node,
        source_grain: u32,
        action: Cog,
        target: &mut T,
    ) -> bool {
        if self.resource_refused() {
            return false;
        }
        debug_assert!(action.mag != 0);
        let Some(depth) = source_grain
            .checked_sub(1)
            .and_then(|depth| usize::try_from(depth).ok())
        else {
            self.medium.resource_refused = true;
            return false;
        };
        self.deposit_dark_tread(target);
        self.thicken_branch(depth, node, 0, target).completed
    }

    /// Shared bright construction law. The node has already been composed at the receiving event
    /// grain; this function must never be used to turn its interior components into clock ticks.
    pub(super) fn live_constructed_node_emitting<T: FeltEmissionTarget>(
        &mut self,
        n: Node,
        drive_flow: u32,
        target: &mut T,
    ) -> AtomEvent {
        // §XXIV: the raw sub-arrival deposits NO shared relation (A1's drive rides the interior).
        let rel = face(n.place, self.sub_stance.place, self.frame);
        // ★ the tire feels the CONE at positional χ — the receiver constructs the second pyramid.
        let (_rel_grip, rel_form, met, standing_read) = if self.sub_stance.len != 0 {
            let fly = self.sub_fly;
            self.complete_cast(rel, &fly, self.sub_fly_live)
        } else {
            (None, RegionalForm::UNBORN, rel, None)
        };
        let dark = met.arrow.at_horizon();
        let node_at_pole = {
            let dr = n.place.0.sub(self.frame.0);
            let di = n.place.1.sub(self.frame.1);
            dr.mag == 0 && di.mag == 0
        };
        let wound = if dark {
            false
        } else if self.sub_fly_live {
            met.wound_against(&self.sub_fly)
        } else {
            met.founds()
        };
        // §XXV: the atom event's own deed folds `K` — the same one law at every grain.
        if let Some(deed) = deed_emanation(&met, &self.sub_fly, self.sub_fly_live, wound) {
            self.fold_channel(deed);
        }
        let mut fold: Option<Node> = None;
        if self.sub_stance.len == 0 {
            if !node_at_pole {
                self.sub_stance = n;
            }
        } else if dark {
            // the frame's horizon — the atom passes through unread.
        } else if wound {
            // ★ THE FOLD — the sub-segment completes; the brick is born at the boundary, crossing
            // RE-BASED (§XVIII(a) — the one law at every seam: the interior scale encloses as gauge).
            let old = self.sub_stance;
            let fr = old.place.0.sub(self.frame.0);
            let fi = old.place.1.sub(self.frame.1);
            let (fr2, fi2) = rebase_pair(fr, fi);
            let the_fold = Node {
                well: old.well,
                place: (self.frame.0.add(fr2), self.frame.1.add(fi2)),
                len: old.len,
            };
            // THE FOUND DEED casts the whole post-drag χ (§XXIV ⊕ §XXIX).
            let fly = self.sub_fly;
            let fly_live = self.sub_fly_live;
            self.cross_deed(&met, &fly, fly_live, true, standing_read, target);
            fold = Some(the_fold);
            self.sub_stance = n;
            if self.sub_fly_live {
                self.sub_fly = rel_form.drag(self.sub_fly); // the receiver's completion precesses
            }
        } else {
            let (mol, _r) = bond(self.sub_stance, n, self.frame);
            // THE RIDE DEED CROSSES at the relating's grip (§XXIV/RULE 2 — no winding hand).
            let fly = self.sub_fly;
            let fly_live = self.sub_fly_live;
            self.cross_deed(&met, &fly, fly_live, false, standing_read, target);
            self.sub_stance = mol;
            self.sub_fly = met;
            self.sub_fly_live = true;
        }
        // the fold reaches the word grain — the whole upper circuit per brick.
        let (perception, step) = match fold {
            Some(f) => {
                let p = self.perceive_node_emitting(f, drive_flow, target);
                if self.resource_refused() {
                    (Some(p), None)
                } else {
                    let s = self.path_emitting(drive_flow, target);
                    (Some(p), Some(s))
                }
            }
            None => (None, None),
        };
        AtomEvent {
            fold,
            perception,
            step,
        }
    }

    /// ★ THE DARK TREAD'S DEPOSIT — the completed passage lays its whole accumulated drive AT THE
    /// FRAME'S OWN PLACE (§XVII verbatim): the lineage's ANCHOR — its first difference, never reset.
    /// All silence is one place PER LINEAGE: its own pole. (The old universal dead-bit place was the
    /// excised card's common-frame compromise — the fixed common frame died with §XXIV.) ONE
    /// transition per hand of the glyph (a passage deeper than the u32 hand deposits in the hand's
    /// own chunks — the boundary's grain, not a guard). The passage is ONE relating: one completed
    /// silence = ONE fold of `K` (§XXV — duration, not order). The pending drive lands whole.
    pub(super) fn deposit_dark_tread<T: FeltEmissionTarget>(&mut self, target: &mut T) {
        if self.dark_pending == 0 {
            return;
        }
        let action = Cog::lit(self.dark_pending as i64);
        self.dark_pending = 0;
        self.resolve_dark_action_emitting(action, target);
    }

    /// Resolve one native event-current tread whole. The active membrane retains an unresolved
    /// sequence of wholly static events as an open residual and calls this only at the first
    /// resolving relation or the current's actual boundary. Thus plural relation components do not
    /// multiply one event's action, while the historical octet mouth keeps its exact u64 tread.
    /// `action` is the complete A1 current carried by that interval, not a score or a drive chosen
    /// by Soma.
    pub fn resolve_dark_action(&mut self, action: Cog) {
        let mut target = NoFeltEmission;
        self.resolve_dark_action_emitting(action, &mut target)
    }

    /// Resolve one completed dark event interval and emit its one accepted term.  The membrane
    /// attaches the interval's exact event-cause span; the body owns only the physical deed.
    pub fn resolve_dark_action_emitting<T: FeltEmissionTarget>(
        &mut self,
        action: Cog,
        target: &mut T,
    ) {
        if action.mag == 0 {
            return;
        }
        self.fold_channel(DeedEmanation::dark());
        // PRESENTED 2026-07-09 (Brandon, in-line): the completed passage's one term is PURE SAME — the
        // groove's norm scaled by the accumulated quanta (other = 0, no hand): "deposits whole" as the
        // term's magnitude; the DC law holds (nothing per atom, one term per passage).
        let norm = if self.sub_fly_live {
            let a = self.sub_fly.arrow.aim;
            let c = self.sub_fly.arrow.cross;
            a.mul(a).add(c.mul(c))
        } else {
            Cog::lit(1)
        };
        let same = norm.mul(action);
        let position = self.channel.frame().anchor;
        let term = FeltTerm {
            chi: soul::Chi {
                same,
                other: Cog::lit(0),
            },
            winding: WindingQuantum::None,
        };
        if self.medium.deposit_at(position, term) {
            self.terms_deposited.dark += 1;
            target.emit(FeltEmission {
                position,
                term,
                deed: FeltDeed::Dark,
                standing_read: None,
            });
        }
    }

    /// ★ the light's end completes the standing dark passage (the stream's own boundary is a resolving
    /// edge). The membrane calls this before any whole-body audit; a body dropped mid-passage would
    /// otherwise carry in-flight mass the pool cannot see.
    pub fn flush_dark(&mut self) {
        let mut target = NoFeltEmission;
        self.deposit_dark_tread(&mut target);
    }

    /// test-only instrument: stage one felt term into the OWN region at a bare grip (staging a terrain
    /// difference without moving any body state). Never a boundary verb — the membrane crosses deeds.
    #[cfg(test)]
    pub(crate) fn stage_own(&mut self, g: Grip, term: FeltTerm) {
        if self.medium.deposit(g, term) {
            match term.winding {
                WindingQuantum::None => self.terms_deposited.ride += 1,
                WindingQuantum::ThisWay => self.terms_deposited.found_this += 1,
                WindingQuantum::ThatWay => self.terms_deposited.found_that += 1,
            }
        }
    }
}
