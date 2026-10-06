//! Continuation of the reached joint state, bound to its producer, source and clock.
//!
//! [agent-inferred] A boundary owner declares its admitted source and clock once. Cloning that
//! binding retains their identity; equal numerical values do not identify two sources or clocks.
//! This checks continuation provenance, not the boundary's source-to-law derivation. That
//! derivation, the comparison covector and the material selection remain the consumer's laws.
//! No passage archive is retained: only the current state, constitution and clock are carried.
//!
//! The first material return is deliberately the same-chart storage specialization. It changes
//! only Q, certifies Q' <= (1 + epsilon) Q, reads work at the *same reached point*, and continues
//! that point with Q'. It makes no descent claim. A changed chart, coupling, source or clock
//! needs its own transported relation; accepting it here would silently omit those terms.
//! This first binding refuses pumped laws: a duration-step match alone does not bind the pump's
//! own phase and section. The HNN's lifted pump/word relation remains its existing owner's law.

use std::sync::Arc;

use num_bigint::BigUint;

use super::*;
use crate::holon::deposition::CommittedEnergyBound;
use crate::holon::element::storage_energy;
use crate::navigator::Clock;
use crate::ratio::linear::inertia::inertia;

/// An admitted joint-law producer with its boundary source and clock identities.
#[derive(Debug)]
pub struct JointProducer<S> {
    law: Arc<JointLaw>,
    source: Arc<S>,
    clock: Arc<Clock>,
}

impl<S> Clone for JointProducer<S> {
    fn clone(&self) -> Self {
        Self {
            law: self.law.clone(),
            source: self.source.clone(),
            clock: self.clock.clone(),
        }
    }
}

/// The current reached physical state, with the law that will continue it. No public constructor.
#[derive(Debug)]
pub struct BoundJointState<S> {
    producer: JointProducer<S>,
    state: HolonState,
    clock: Clock,
}

impl<S> BoundJointState<S> {
    pub fn state(&self) -> &HolonState {
        &self.state
    }
    pub fn clock(&self) -> &Clock {
        &self.clock
    }
}

/// A solved joint step and its bound continuation. The existing step owns all balance readings.
#[derive(Debug)]
pub struct BoundJointStep<S> {
    step: JointStep,
    reached: BoundJointState<S>,
}

impl<S> BoundJointStep<S> {
    pub fn step(&self) -> &JointStep {
        &self.step
    }
    pub fn reached(&self) -> &BoundJointState<S> {
        &self.reached
    }
}

/// Storage work at one reached point, distinct from the preceding passage's balance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StorageReturn {
    pub before: Rat,
    pub after: Rat,
    pub work: Rat,
    pub epsilon: Rat,
}

impl<S> JointProducer<S> {
    /// Bind an already admitted source law to its boundary owner's source and clock. The source
    /// must remain immutable. This does not authenticate foreign data or prove its encoding.
    pub fn declared(law: JointLaw, source: Arc<S>, clock: Arc<Clock>) -> Result<Self, HolonError> {
        if law.law().holon().pump().is_some() {
            return Err(HolonError::Unsupported {
                what: "a joint continuation binding",
                reason: "a pumped law needs its own phase and section binding",
            });
        }
        if law.law().step() != clock.step() {
            return Err(HolonError::ConformanceFailed {
                what: "the joint law uses the bound clock step",
            });
        }
        Ok(Self {
            law: Arc::new(law),
            source,
            clock,
        })
    }

    pub fn law(&self) -> &JointLaw {
        &self.law
    }

    fn check_boundary(&self, source: &Arc<S>, clock: &Arc<Clock>) -> Result<(), HolonError> {
        if !Arc::ptr_eq(&self.source, source) {
            return Err(HolonError::ConformanceFailed {
                what: "the continuation belongs to this source",
            });
        }
        if !Arc::ptr_eq(&self.clock, clock) {
            return Err(HolonError::ConformanceFailed {
                what: "the continuation belongs to this clock",
            });
        }
        Ok(())
    }

    fn check_reached(
        &self,
        reached: &BoundJointState<S>,
        source: &Arc<S>,
        clock: &Arc<Clock>,
    ) -> Result<(), HolonError> {
        self.check_boundary(source, clock)?;
        if !Arc::ptr_eq(&self.law, &reached.producer.law)
            || !Arc::ptr_eq(&self.source, &reached.producer.source)
            || !Arc::ptr_eq(&self.clock, &reached.producer.clock)
        {
            return Err(HolonError::ConformanceFailed {
                what: "the reached state belongs to this producer",
            });
        }
        Ok(())
    }

    /// Open at the boundary clock's actual reading, not a caller-chosen later commit.
    pub fn open(
        &self,
        state: HolonState,
        source: &Arc<S>,
        clock: &Arc<Clock>,
    ) -> Result<BoundJointState<S>, HolonError> {
        self.check_boundary(source, clock)?;
        if BigUint::from(state.commit) != clock.ticks() {
            return Err(HolonError::ConformanceFailed {
                what: "the opening commit is the bound clock reading",
            });
        }
        if state.configuration.len() != self.law.law().holon().counts().storage {
            return Err(HolonError::Shape {
                what: "bound joint state",
                expected: self.law.law().holon().counts().storage,
                found: state.configuration.len(),
            });
        }
        Ok(BoundJointState {
            producer: self.clone(),
            state,
            clock: (**clock).clone(),
        })
    }

    /// Solve the existing joint interaction from the reached state and advance its clock once.
    pub fn interact(
        &self,
        reached: &BoundJointState<S>,
        source: &Arc<S>,
        clock: &Arc<Clock>,
        input: &[Rat],
        face: &ReceiverFace,
        receipt: &ReceiptLaw,
    ) -> Result<InteractionReturn<BoundJointStep<S>>, HolonError> {
        self.check_reached(reached, source, clock)?;
        let returned = self.law.interact(&reached.state, input, face, receipt)?;
        let step = returned
            .forward
            .into_present()
            .ok_or(HolonError::ConformanceFailed {
                what: "joint reception returned its solved step",
            })?;
        let state = step.next_state();
        let mut next_clock = reached.clock.clone();
        next_clock.advance(&BigUint::from(1u8));
        if BigUint::from(state.commit) != next_clock.ticks() {
            return Err(HolonError::ConformanceFailed {
                what: "the solved commit and clock advance together",
            });
        }
        Ok(InteractionReturn {
            forward: Component::Present(BoundJointStep {
                step,
                reached: BoundJointState {
                    producer: self.clone(),
                    state,
                    clock: next_clock,
                },
            }),
            pullback: returned.pullback,
            deposit: returned.deposit,
            order: returned.order,
            phases: returned.phases,
            receipt: returned.receipt,
        })
    }

    /// Check a consumer's storage-only successor and return the *same* physical state under it.
    /// No dynamics are solved here, no covector is invented, and the clock does not advance.
    /// Pumped or recharted returns are refused by this specialization, not approximated.
    pub fn return_storage(
        &self,
        reached: &BoundJointState<S>,
        source: &Arc<S>,
        clock: &Arc<Clock>,
        successor: JointLaw,
        epsilon: Rat,
        receipt: &ReceiptLaw,
    ) -> Result<
        (
            Self,
            InteractionReturn<BoundJointState<S>, (), StorageReturn>,
        ),
        HolonError,
    > {
        self.check_reached(reached, source, clock)?;
        let old = self.law.law().holon();
        let new = successor.law().holon();
        let a = old.port_holon();
        let b = new.port_holon();
        if old.pump().is_some()
            || new.pump().is_some()
            || self.law.source_extent() != successor.source_extent()
            || self.law.law().step() != successor.law().step()
            || self.law.law().scheme() != successor.law().scheme()
            || a.counts() != b.counts()
            || a.dirac() != b.dirac()
            || a.resistance() != b.resistance()
            || old.active() != new.active()
            || old.ports() != new.ports()
            || old.complex() != new.complex()
            || old.connection() != new.connection()
            || old.interior() != new.interior()
            || old.port_faces() != new.port_faces()
            || old.navigators() != new.navigators()
            || old.restrictions() != new.restrictions()
        {
            return Err(HolonError::Unsupported {
                what: "a storage-only return",
                reason: "the successor also changes the chart, coupling, clock or other element relations",
            });
        }
        if inertia(a.storage()).negative > 0 || inertia(b.storage()).negative > 0 {
            return Err(HolonError::ConformanceFailed {
                what: "both storage forms are nonnegative",
            });
        }
        CommittedEnergyBound::certify_deposit(a.storage(), b.storage(), &epsilon)?;
        let x = &reached.state.configuration;
        let before = storage_energy(a.storage(), x)?;
        let after = storage_energy(b.storage(), x)?;
        let work = storage_energy(
            &matrix_form(&form_matrix(b.storage()).subtract(&form_matrix(a.storage()))?)?,
            x,
        )?;
        if &after - &before != work {
            return Err(HolonError::ConformanceFailed {
                what: "storage work equals the same-state energy difference",
            });
        }
        let producer = Self {
            law: Arc::new(successor),
            source: self.source.clone(),
            clock: self.clock.clone(),
        };
        let returned = InteractionReturn {
            forward: Component::Present(BoundJointState {
                producer: producer.clone(),
                state: reached.state.clone(),
                clock: reached.clock.clone(),
            }),
            pullback: Component::Absent("storage work does not certify a comparison covector"),
            deposit: Component::Present(StorageReturn {
                before,
                after,
                work,
                epsilon,
            }),
            order: Component::Absent("a storage return reads no source order"),
            phases: Component::Absent("a storage return advances no receiving phase"),
            receipt: receipt.receive(x)?,
        };
        Ok((producer, returned))
    }
}

#[cfg(test)]
mod tests;
