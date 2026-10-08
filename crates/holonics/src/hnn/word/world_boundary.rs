//! Actual power-conjugate exterior return on one nonloaded native storage port.
//!
//! [agent-inferred; Refs #73 #62] After the native full tick emits `a`, the actual
//! co-clock World returns `b`. Replacing that storage wave before the next tick supplies
//! `W_boundary = h Y (|b|²-|a|²)/4 = -W_World`. No source moment is deposited or
//! injected again. The intervention operands live only until this Word's conditional
//! return; the Resident retains the resulting current and actual World state.

use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceWaveReturn {
    /// Local full-tick count; the actual clock is `Word::opened_at() + tick`.
    pub tick: usize,
    pub ring: usize,
    pub incident: Vec<Rat>,
    pub reflected: Vec<Rat>,
    pub work: Rat,
}

impl Word<'_> {
    pub fn source_returns(&self) -> &[SourceWaveReturn] {
        &self.source_returns
    }

    pub(crate) fn admit_source_boundary(&self, ring: usize) -> Result<(), HnnError> {
        if !self.field.sources().contains(&ring)
            || self
                .operands
                .resonators()
                .get(ring)
                .is_none_or(Option::is_some)
            || self.operands.lattice().is_some()
            || self.is_ended()
        {
            return Err(HnnError::Unadmitted {
                reason: "an exact nonloaded source storage port for the actual co-clock World return",
            });
        }
        Ok(())
    }

    pub(crate) fn source_wave(&self, ring: usize) -> Result<&[Rat], HnnError> {
        self.admit_source_boundary(ring)?;
        Ok(&self.storage[ring])
    }

    /// Read every fallible balance before publication; no partially changed native storage.
    pub(crate) fn return_source_wave(
        &mut self,
        ring: usize,
        native_tick: usize,
        incident: &[Rat],
        reflected: &[Rat],
        world_work: &Rat,
    ) -> Result<(), HnnError> {
        self.admit_source_boundary(ring)?;
        let tick = self.ticks();
        if tick == 0
            || self.opened_at.checked_add(tick) != Some(native_tick)
            || self.balances.len() != tick
            || self.fields.len() != tick
            || self.source_returns.last().is_some_and(|r| r.tick == tick)
            || self.storage[ring] != incident
            || reflected.len() != incident.len()
        {
            return Err(HnnError::Unadmitted {
                reason: "one actual returned wave on its just-executed source port and common clock",
            });
        }
        let work = self.field.step()
            * self.field.ring(ring).admittance()
            * (reflected.iter().map(|x| x * x).sum::<Rat>()
                - incident.iter().map(|x| x * x).sum::<Rat>())
            / integer(4);
        let before = self.power()?;
        let mut change = self.change()?;
        change.storage[ring] = reflected.to_vec();
        let after = global_power(
            &self.operands,
            &change.storage,
            &change.arrivals,
            &change.states,
        )?;
        if work != -world_work
            || &after - &before != work
            || !self.balances[tick - 1].closes()
            || !self.fields[tick - 1].closes()
        {
            return Err(HnnError::Unadmitted {
                reason: "the actual exterior wave exchange closes native storage and World port work",
            });
        }
        self.storage[ring] = reflected.to_vec();
        self.balances[tick - 1].after = after.clone();
        self.balances[tick - 1].boundary += &work;
        self.fields[tick - 1].after = after.clone();
        self.fields[tick - 1].boundary += &work;
        self.settled = Some(after);
        self.source_returns.push(SourceWaveReturn {
            tick,
            ring,
            incident: incident.to_vec(),
            reflected: reflected.to_vec(),
            work,
        });
        self.peak_bits = self.peak_bits.max(self.state_bits());
        Ok(())
    }
}
