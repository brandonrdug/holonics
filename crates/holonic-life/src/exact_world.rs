//! Transactional crossing from a typed exact law into the continuing Soma body.
//!
//! `holonic-engine` retains the domain standing and law. [`LiveCurrentMachine`] retains the
//! organ-neutral current body. An adapter owns only the stable organ capabilities and the typed
//! lowering of one complete proposed successor; it may not retain a second domain standing or
//! serialize the successor into an invented universal payload.

use holonic_engine::{
    CausalWorld, EventSuccessor, ExactEventLaw, ThroughTransitionError, TransitionReceipt,
};
use soma_membrane::{
    ContemporaryRadiation, LiveCurrentError, LiveCurrentExecutor, LiveCurrentMachine,
};

/// Domain-owned crossing between one exact law and the common live-current membrane.
///
/// `found` is deliberately separate because opening a new live lineage is itself causal ingress.
/// Once the required organs exist, `present_successor` must perform every fallible derivation and
/// validation before its final call which commits the live machine. No observer, cache, or report
/// may turn a completed live crossing back into a refused event.
pub trait ExactCurrentAdapter<L: ExactEventLaw> {
    type Error;

    fn found(&mut self, machine: &mut LiveCurrentMachine) -> Result<(), Self::Error>;

    fn present_successor(
        &mut self,
        event: &L::Event,
        standing_before: &L::Standing,
        successor: &EventSuccessor<L::Standing, L::Radiation>,
        machine: &mut LiveCurrentMachine,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<ContemporaryRadiation, Self::Error>;
}

/// One typed exact world whose events cross the common continuing current body atomically.
pub struct ExactWorldOrgan<L: ExactEventLaw, A> {
    world: CausalWorld<L>,
    adapter: A,
}

impl<L: ExactEventLaw, A> ExactWorldOrgan<L, A> {
    pub const fn new(world: CausalWorld<L>, adapter: A) -> Self {
        Self { world, adapter }
    }

    pub const fn world(&self) -> &CausalWorld<L> {
        &self.world
    }

    pub const fn adapter(&self) -> &A {
        &self.adapter
    }

    pub fn adapter_mut(&mut self) -> &mut A {
        &mut self.adapter
    }

    pub fn into_parts(self) -> (CausalWorld<L>, A) {
        (self.world, self.adapter)
    }
}

impl<L, A> ExactWorldOrgan<L, A>
where
    L: ExactEventLaw,
    A: ExactCurrentAdapter<L>,
{
    pub fn found(&mut self, machine: &mut LiveCurrentMachine) -> Result<(), A::Error> {
        self.adapter.found(machine)
    }

    /// Derive both successors before committing the typed world.
    ///
    /// A law refusal changes neither body. An adapter/live-current refusal discards the proposed
    /// typed successor. A successful live crossing leaves no fallible work before the typed
    /// successor and ordinal commit.
    pub fn receive_into(
        &mut self,
        event: &L::Event,
        machine: &mut LiveCurrentMachine,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<
        (TransitionReceipt<L::Radiation>, ContemporaryRadiation),
        ThroughTransitionError<L::Error, A::Error>,
    > {
        let adapter = &mut self.adapter;
        self.world.receive_through(event, |before, successor| {
            adapter.present_successor(event, before, successor, machine, executor)
        })
    }
}

/// Common error adapter for crossings whose only additional refusal is the direct machine.
pub type DirectExactWorldError<LawError> = ThroughTransitionError<LawError, LiveCurrentError>;
