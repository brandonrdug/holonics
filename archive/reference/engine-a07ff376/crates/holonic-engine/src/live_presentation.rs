//! Persistent multicore realization of already-caused receiver faces.
//!
//! The simplicial/hinge world owns causal propagation. A terminal work span is
//! only a hidden physical partition of the bounded display quotient: it is
//! never a simplex, a chronology node, a wavefront, or a visible partial
//! successor. Every receiver generation is assembled privately and becomes
//! visible as one atomic continuous face. Different receivers retain
//! independent generations unless a world explicitly couples their events.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex, mpsc};
use std::thread::{self, JoinHandle};

use relational_geometry::ReceiverId;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    ContinuousPresentation, EventId, PresentationAddress, PresentationError, PresentationMember,
    PresentationTransducer, Rgb8, TerminalMatrixSpec, classify_receiver_address,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct TerminalTile {
    pub left: u32,
    pub top: u32,
    pub width: u32,
    pub height: u32,
}

impl TerminalTile {
    pub fn addresses(self) -> Vec<PresentationAddress> {
        let mut addresses = Vec::with_capacity(
            usize::try_from(self.width)
                .expect("tile width fits memory addressing")
                .saturating_mul(
                    usize::try_from(self.height).expect("tile height fits memory addressing"),
                ),
        );
        for row in self.top..self.top + self.height {
            for column in self.left..self.left + self.width {
                addresses.push(PresentationAddress { column, row });
            }
        }
        addresses
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ReceiverCoupling {
    pub source: ReceiverId,
    pub target: ReceiverId,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverCouplingSet {
    pub relations: BTreeSet<ReceiverCoupling>,
}

impl ReceiverCouplingSet {
    pub fn propagation_targets(&self, source: ReceiverId) -> BTreeSet<ReceiverId> {
        let mut reached = BTreeSet::from([source]);
        let mut frontier = vec![source];
        while let Some(receiver) = frontier.pop() {
            for relation in self
                .relations
                .iter()
                .filter(|relation| relation.source == receiver)
            {
                if reached.insert(relation.target) {
                    frontier.push(relation.target);
                }
            }
        }
        reached
    }
}

#[derive(Clone)]
pub struct LiveTileRequest {
    pub generation: u64,
    pub event: EventId,
    pub receiver: ReceiverId,
    pub tile: TerminalTile,
    pub presentation: Arc<ContinuousPresentation>,
    pub specification: Arc<TerminalMatrixSpec>,
}

#[derive(Clone, Debug)]
pub struct LiveTilePayload {
    pub members: Vec<PresentationMember>,
    pub colors: Vec<Rgb8>,
}

#[derive(Debug)]
pub struct LiveTileCompletion {
    pub generation: u64,
    pub event: EventId,
    pub receiver: ReceiverId,
    pub tile: TerminalTile,
    pub worker: usize,
    pub result: Result<LiveTilePayload, PresentationError>,
}

enum WorkerMessage {
    Realize(LiveTileRequest),
    Stop,
}

pub struct LiveCpuPresenter<T>
where
    T: PresentationTransducer + Send + Sync + 'static,
{
    tasks: mpsc::Sender<WorkerMessage>,
    completions: mpsc::Receiver<LiveTileCompletion>,
    workers: Vec<JoinHandle<()>>,
    latest_generations: Arc<Mutex<BTreeMap<ReceiverId, u64>>>,
    _transducer: Arc<T>,
}

impl<T> LiveCpuPresenter<T>
where
    T: PresentationTransducer + Send + Sync + 'static,
{
    pub fn new(workers: usize, transducer: Arc<T>) -> Result<Self, LivePresentationError> {
        if workers == 0 {
            return Err(LivePresentationError::NoWorkers);
        }
        let (task_sender, task_receiver) = mpsc::channel::<WorkerMessage>();
        let task_receiver = Arc::new(Mutex::new(task_receiver));
        let (completion_sender, completion_receiver) = mpsc::channel();
        let latest_generations = Arc::new(Mutex::new(BTreeMap::<ReceiverId, u64>::new()));
        let mut handles = Vec::with_capacity(workers);
        for worker in 0..workers {
            let tasks = Arc::clone(&task_receiver);
            let completions = completion_sender.clone();
            let transducer = Arc::clone(&transducer);
            let latest_generations = Arc::clone(&latest_generations);
            handles.push(thread::spawn(move || {
                loop {
                    let message = {
                        let receiver = tasks
                            .lock()
                            .expect("the live presentation task mouth remains available");
                        receiver.recv()
                    };
                    let Ok(message) = message else {
                        return;
                    };
                    let WorkerMessage::Realize(request) = message else {
                        return;
                    };
                    let is_current = latest_generations
                        .lock()
                        .expect("the receiver generation standing remains available")
                        .get(&request.receiver)
                        .is_some_and(|generation| *generation == request.generation);
                    if !is_current {
                        continue;
                    }
                    let result = request
                        .tile
                        .addresses()
                        .into_iter()
                        .map(|address| {
                            let member = classify_receiver_address(
                                &request.presentation,
                                &request.specification,
                                request.receiver,
                                address,
                            )?;
                            let color = transducer.transduce(&member);
                            Ok((member, color))
                        })
                        .collect::<Result<Vec<_>, PresentationError>>()
                        .map(|pairs| LiveTilePayload {
                            members: pairs.iter().map(|(member, _)| member.clone()).collect(),
                            colors: pairs.into_iter().map(|(_, color)| color).collect(),
                        });
                    if completions
                        .send(LiveTileCompletion {
                            generation: request.generation,
                            event: request.event,
                            receiver: request.receiver,
                            tile: request.tile,
                            worker,
                            result,
                        })
                        .is_err()
                    {
                        return;
                    }
                }
            }));
        }
        Ok(Self {
            tasks: task_sender,
            completions: completion_receiver,
            workers: handles,
            latest_generations,
            _transducer: transducer,
        })
    }

    pub fn submit(&self, request: LiveTileRequest) -> Result<(), LivePresentationError> {
        self.latest_generations
            .lock()
            .expect("the receiver generation standing remains available")
            .entry(request.receiver)
            .and_modify(|generation| *generation = (*generation).max(request.generation))
            .or_insert(request.generation);
        self.tasks
            .send(WorkerMessage::Realize(request))
            .map_err(|_| LivePresentationError::WorkersDeparted)
    }

    pub fn try_completion(&self) -> Result<Option<LiveTileCompletion>, LivePresentationError> {
        match self.completions.try_recv() {
            Ok(completion) => Ok(Some(completion)),
            Err(mpsc::TryRecvError::Empty) => Ok(None),
            Err(mpsc::TryRecvError::Disconnected) => Err(LivePresentationError::WorkersDeparted),
        }
    }

    pub fn workers(&self) -> usize {
        self.workers.len()
    }
}

impl<T> Drop for LiveCpuPresenter<T>
where
    T: PresentationTransducer + Send + Sync + 'static,
{
    fn drop(&mut self) {
        for _ in &self.workers {
            let _ = self.tasks.send(WorkerMessage::Stop);
        }
        while let Some(worker) = self.workers.pop() {
            let _ = worker.join();
        }
    }
}

#[derive(Debug, Error)]
pub enum LivePresentationError {
    #[error("a live CPU presenter requires at least one worker")]
    NoWorkers,
    #[error("the live CPU presentation workers departed")]
    WorkersDeparted,
    #[error(transparent)]
    Presentation(#[from] PresentationError),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coupling_is_explicit_directed_reachability() {
        let set = ReceiverCouplingSet {
            relations: BTreeSet::from([
                ReceiverCoupling {
                    source: ReceiverId(1),
                    target: ReceiverId(2),
                },
                ReceiverCoupling {
                    source: ReceiverId(2),
                    target: ReceiverId(3),
                },
            ]),
        };
        assert_eq!(
            set.propagation_targets(ReceiverId(1)),
            BTreeSet::from([ReceiverId(1), ReceiverId(2), ReceiverId(3)])
        );
        assert_eq!(
            set.propagation_targets(ReceiverId(3)),
            BTreeSet::from([ReceiverId(3)])
        );
    }
}
