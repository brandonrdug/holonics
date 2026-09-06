//! Live coordinate transport and physical incidence changes are different operations.
//! Historical emissions retain their actual frame and immutable material. Native reception
//! transports their source fields on-device; the exterior frame view below is only a codec.

use super::*;

#[derive(Debug)]
pub struct NativeCurrentFrame {
    pub(super) ordinal: u64,
    pub(super) root_to_local: Vec<NativePhaseCurrent>,
}

impl NativeCurrentFrame {
    pub fn ordinal(&self) -> u64 {
        self.ordinal
    }
    pub fn root_to_local(&self) -> &[NativePhaseCurrent] {
        &self.root_to_local
    }
}

pub(super) struct HeldCurrentFrame<'chart> {
    pub(super) native: ResidentSection<'chart>,
    pub(super) view: Rc<NativeCurrentFrame>,
}

#[derive(Debug)]
pub struct NativeRechartReceipt {
    pub before: Rc<NativeCurrentFrame>,
    pub after: Rc<NativeCurrentFrame>,
    pub at_state: Option<usize>,
    pub gauges: Vec<NativePhaseCurrent>,
}

#[derive(Debug)]
pub struct NativeIncidenceChange {
    pub at_state: Option<usize>,
    pub frame: Rc<NativeCurrentFrame>,
    pub node: usize,
    pub before: NativePhaseCurrent,
    pub after: NativePhaseCurrent,
}

impl<'chart> NativeConstitutiveEcology<'chart> {
    pub fn recharts(&self) -> &[NativeRechartReceipt] {
        &self.recharts
    }
    pub fn incidence_changes(&self) -> &[NativeIncidenceChange] {
        &self.incidence_changes
    }

    /// A fixed-node rational unit-phase change of chart. This stages a new representation of
    /// the same state/relation, never a second ecology or an independently running branch.
    /// Old buffers and all source handles remain valid until the complete native return succeeds.
    pub fn rechart(
        &mut self,
        gauges: &[NativePhaseCurrent],
    ) -> Result<&NativeRechartReceipt, ConstitutiveFibreError> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let nodes = self.material.len();
        if gauges.len() != nodes || gauges.iter().any(|g| !g.is_unit()) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let ordinal = self
            .frame
            .view
            .ordinal
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        self.recharts
            .try_reserve(1)
            .map_err(|_| ConstitutiveFibreError::Shape)?;
        let declared_gauges = gauges.to_vec();
        let surface = self.relation.surface;
        let width = 2 * nodes + 2;
        let words = gauges
            .iter()
            .zip(self.material.iter())
            .flat_map(|(g, seed)| g.words().into_iter().chain(seed.initial_held.words()))
            .map(|v| (v, v))
            .collect();
        let change = surface.mount_section_rest(
            &ResidentSectionRest::found(nodes, 6, ResidentGrain(0), 64, words)
                .map_err(|_| ConstitutiveFibreError::Shape)?,
        )?;
        let new_seed = surface.fresh_section(nodes, 5, ResidentGrain(0))?;
        let new_memory = surface.fresh_section(nodes, 3, ResidentGrain(0))?;
        let new_frame = surface.fresh_section(nodes, 3, ResidentGrain(0))?;
        let new_basis = surface.fresh_section(width, width, ResidentGrain(0))?;
        let report = surface.fresh_section(nodes, 9, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_constitutive_rechart(
                &lane,
                &self.seed,
                &self.memory,
                &self.frame.native,
                &self.relation.basis,
                &change,
                &new_seed,
                &new_memory,
                &new_frame,
                &new_basis,
                &report,
            )?;
        }
        passage.close(0, &report, 64)?;
        let reading = passage.finish()?.launch()?;
        if !reading.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "{:?}",
                reading.obstruction
            )));
        }
        let returned = surface.read_out(&report)?;
        if returned.iter().any(|(l, h)| l != h) {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let phase = |at: usize| {
            NativePhaseCurrent::new(returned[at].0, returned[at + 1].0, returned[at + 2].0)
        };
        let mut material = Vec::with_capacity(nodes);
        let mut root_to_local = Vec::with_capacity(nodes);
        for (node, old) in self.material.iter().enumerate() {
            let turn = phase(9 * node)?;
            let initial = phase(9 * node + 3)?;
            let root = phase(9 * node + 6)?;
            if !turn.is_unit() || !root.is_unit() {
                return Err(ConstitutiveFibreError::Uncertain);
            }
            material.push(NativeJunctionSeed {
                incoming_admittance: old.incoming_admittance,
                held_admittance: old.held_admittance,
                incoming_transport: turn,
                initial_held: initial,
            });
            root_to_local.push(root);
        }
        let frame = Rc::new(HeldCurrentFrame {
            native: new_frame,
            view: Rc::new(NativeCurrentFrame {
                ordinal,
                root_to_local,
            }),
        });
        let receipt = NativeRechartReceipt {
            before: Rc::clone(&self.frame.view),
            after: Rc::clone(&frame.view),
            at_state: self.history.len().checked_sub(1),
            gauges: declared_gauges,
        };
        // Recoverable ownership transfer: all staging and decoding succeeded before the one
        // live owner's representation changes. No historical section is rewritten.
        self.seed = new_seed;
        self.memory = new_memory;
        self.relation.basis = new_basis;
        self.material = material.into();
        self.frame = frame;
        self.recharts.push(receipt);
        Ok(self.recharts.last().expect("committed rechart"))
    }

    /// An explicit physical change of one incoming incidence, in the PRESENT local frame.
    /// This mounts new constitutive material; it does not rotate the held phase, learned relation
    /// or old source fields. The difference from `rechart` is intentional and testable.
    pub fn replace_incoming_transport(
        &mut self,
        node: usize,
        after: NativePhaseCurrent,
    ) -> Result<&NativeIncidenceChange, ConstitutiveFibreError> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        if node >= self.material.len() || !after.is_unit() {
            return Err(ConstitutiveFibreError::Shape);
        }
        self.incidence_changes
            .try_reserve(1)
            .map_err(|_| ConstitutiveFibreError::Shape)?;
        let mut material = self.material.to_vec(); // immutable declaration, never the live ecology
        let before = material[node].incoming_transport;
        material[node].incoming_transport = after;
        let words = material
            .iter()
            .flat_map(|n| {
                [
                    n.incoming_admittance,
                    n.held_admittance,
                    n.incoming_transport.real,
                    n.incoming_transport.imaginary,
                    n.incoming_transport.denominator,
                ]
            })
            .map(|v| (v, v))
            .collect();
        let seed = self.relation.surface.mount_section_rest(
            &ResidentSectionRest::found(material.len(), 5, ResidentGrain(0), 64, words)
                .map_err(|_| ConstitutiveFibreError::Shape)?,
        )?;
        let change = NativeIncidenceChange {
            at_state: self.history.len().checked_sub(1),
            frame: Rc::clone(&self.frame.view),
            node,
            before,
            after,
        };
        self.seed = seed;
        self.material = material.into();
        self.incidence_changes.push(change);
        Ok(self.incidence_changes.last().expect("committed material"))
    }
}

#[cfg(test)]
mod tests;
