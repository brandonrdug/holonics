//! Live field recharting and physical incoming-incidence changes.
//!
//! Recharting is a recoverable representation transfer of one continuing field. It rotates both
//! source branches (outgoing and held), the held memory, seed incidence and root frame. The
//! external incoming field stays in its declared target chart. A later linked reception carries
//! the old source frame to the current frame in the resident field kernel.

use super::*;

impl<'chart> NativeConstitutiveField<'chart> {
    /// Rechart the same fixed-node field by exact unit phases. Historical source sections retain
    /// their producing frame; only the contemporary standing representation is replaced.
    pub fn rechart(
        &mut self,
        gauges: &[NativePhaseCurrent],
    ) -> Result<&NativeRechartReceipt, ConstitutiveFibreError> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let nodes = self.material.len();
        if gauges.len() != nodes || gauges.iter().any(|gauge| !gauge.is_unit()) {
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
        let width = 6usize
            .checked_mul(nodes)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let change_words = gauges
            .iter()
            .zip(&self.material)
            .flat_map(|(gauge, seed)| gauge.words().into_iter().chain(seed.initial_held.words()))
            .map(|value| (value, value))
            .collect();
        let change = surface.mount_section_rest(
            &ResidentSectionRest::found(nodes, 6, ResidentGrain(0), 64, change_words)
                .map_err(|_| ConstitutiveFibreError::Shape)?,
        )?;
        let new_seed = surface.fresh_section(nodes, 5, ResidentGrain(0))?;
        let new_memory = surface.fresh_section(nodes, 3, ResidentGrain(0))?;
        let new_frame_native = surface.fresh_section(nodes, 3, ResidentGrain(0))?;
        let new_basis = surface.fresh_section(width, width, ResidentGrain(0))?;
        let report = surface.fresh_section(nodes, 9, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_constitutive_field_rechart(
                &lane,
                &self.seed,
                &self.memory,
                &self.frame.native,
                &self.relation.basis,
                &change,
                &new_seed,
                &new_memory,
                &new_frame_native,
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
        if returned.iter().any(|(lower, upper)| lower != upper) {
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
            native: new_frame_native,
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
        // The one representation transfer occurs only after all new sections and report fields
        // have returned exactly. Existing source sections continue to own their old frames.
        self.seed = new_seed;
        self.memory = new_memory;
        self.relation.basis = new_basis;
        self.material = material;
        self.frame = frame;
        self.recharts.push(receipt);
        Ok(self.recharts.last().expect("committed field rechart"))
    }

    /// Replace one physical incoming incidence in the current local frame. This changes seed
    /// transport only; it does not rotate held memory, rewrite historical source sections, or
    /// alter the learned relation basis.
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
        let mut material = self.material.clone();
        let before = material[node].incoming_transport;
        material[node].incoming_transport = after;
        let words = material
            .iter()
            .flat_map(|seed| {
                [
                    seed.incoming_admittance,
                    seed.held_admittance,
                    seed.incoming_transport.words()[0],
                    seed.incoming_transport.words()[1],
                    seed.incoming_transport.words()[2],
                ]
            })
            .map(|value| (value, value))
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
        self.material = material;
        self.incidence_changes.push(change);
        Ok(self
            .incidence_changes
            .last()
            .expect("committed field incidence change"))
    }
}

#[cfg(test)]
mod tests;
