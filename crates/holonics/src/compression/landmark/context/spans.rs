//! **A span located from a reading part: the joint address across two ports** (HNN_FORMULA's source
//! contract, item 7, the admitted receivers; campaign 5; #73, #148).
//!
//! [definition; agent-inferred] **The located continuation** ([`SpanReading`]). A part on one port
//! (a response) reads a closed span on another (its request): the exterior cells between the
//! span's section letter and the letter that closed it. After each received cell of the reading
//! part, its address across the two ports is the **longest suffix of the part's cells that recurs in
//! the span followed by a cell**: its length `L` and the span's cell after it, `x̂` ([`Located`]).
//! The occurrence is kept while it continues (the next received cell is `x̂` and the span holds a
//! cell after it: `L` grows by one, and no longer suffix can recur, since the suffix one shorter
//! was the longest); at a break it is located anew, the longest and, among the longest, the latest
//! in the span. Nothing is located before the part's first cell or where no cell of the part
//! recurs.
//!
//! So a reply that quotes its request, or a later message that quotes the reply it follows, is
//! addressed by the span itself, beyond the receiving tree's last `D` ticks: the landmarks the two
//! ports share (the retired per-port reader's finding, notebook README "The curated source's own
//! navigators").
//!
//! [definition] The computational object is the helical pair interaction, read here as two ports'
//! spans in contact. Of the winding guide's six general objects this owner touches **faces and
//! placement** (the located continuation placed on the reading part's next tick) and the **tube**
//! (a span from its letter to its close, and the reading part's span to its response); the helix,
//! pair, cell holonomy and tower thread stay attached through the receivers that read it
//! (`receiver::population::admitted`).

/// [definition] **A located continuation**: the length of the recurring suffix and the span's cell
/// after it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Located {
    pub length: u64,
    pub next: usize,
}

/// [definition; agent-inferred] **A reading part's address on a span** (module header): the part's
/// cells since its letter, and the located occurrence as `(j, L)`: the suffix of length `L` ends at
/// the span's cell `j − 1`, and `x̂` is the span's cell `j`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SpanReading {
    /// Only the suffix that can still be compared with a cell after the held target span.
    part: Vec<usize>,
    /// Total cells received on this open reading part. This is a count, not replay material.
    received: usize,
    at: Option<(usize, u64)>,
}

/// Future-sufficient state of a [`SpanReading`] for one fixed target span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpanReadingSnapshot {
    /// Total cells read on the open part.
    pub received: usize,
    /// Its suffix, bounded by the target span's addressable length.
    pub suffix: Vec<usize>,
    /// The current occurrence's end position and matched length, if any.
    pub at: Option<(usize, u64)>,
}

/// A malformed span-reading snapshot refused before it can index a target span.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum SpanReadingSnapshotError {
    #[error("span-reading suffix exceeds the held target's future-relevant length")]
    SuffixTooLong,
    #[error("span-reading snapshot has an inconsistent received count")]
    Received,
    #[error("span-reading address lies outside the held target")]
    Address,
    #[error("span-reading address does not match its retained suffix and target")]
    AddressMismatch,
}

impl SpanReading {
    /// A part before its first cell: nothing located.
    pub fn new() -> Self {
        Self::default()
    }

    /// The part's cells read so far.
    pub fn cells(&self) -> usize {
        self.received
    }

    /// Snapshot only the suffix that can affect future placement on this fixed held target.
    pub fn snapshot(
        &self,
        span: &[usize],
    ) -> Result<SpanReadingSnapshot, SpanReadingSnapshotError> {
        let maximum = span.len().saturating_sub(1);
        let expected = self.received.min(maximum);
        if self.part.len() != expected {
            return Err(SpanReadingSnapshotError::Received);
        }
        validate_address(&self.part, self.at, span)?;
        Ok(SpanReadingSnapshot {
            received: self.received,
            suffix: self.part.clone(),
            at: self.at,
        })
    }

    /// Restore a snapshot against the same retained target span.
    pub fn restore(
        snapshot: SpanReadingSnapshot,
        span: &[usize],
    ) -> Result<Self, SpanReadingSnapshotError> {
        let maximum = span.len().saturating_sub(1);
        if snapshot.suffix.len() > maximum {
            return Err(SpanReadingSnapshotError::SuffixTooLong);
        }
        if snapshot.suffix.len() != snapshot.received.min(maximum) {
            return Err(SpanReadingSnapshotError::Received);
        }
        validate_address(&snapshot.suffix, snapshot.at, span)?;
        let probe = Self {
            part: snapshot.suffix.clone(),
            received: snapshot.received,
            at: None,
        };
        if probe.locate(span) != snapshot.at {
            return Err(SpanReadingSnapshotError::AddressMismatch);
        }
        Ok(Self {
            part: snapshot.suffix,
            received: snapshot.received,
            at: snapshot.at,
        })
    }

    /// **The located continuation** on `span`, when a suffix recurs.
    pub fn located(&self, span: &[usize]) -> Option<Located> {
        self.at
            .and_then(|(j, length)| span.get(j).copied().map(|next| Located { length, next }))
    }

    /// **Read one cell of the part** (module header): the occurrence continues, or is located anew.
    pub fn read(&mut self, span: &[usize], cell: usize) {
        self.received += 1;
        self.part.push(cell);
        self.at = match self.at {
            Some((j, length)) if span.get(j) == Some(&cell) && j + 1 < span.len() => {
                Some((j + 1, length + 1))
            }
            _ => self.locate(span),
        };
        let maximum = span.len().saturating_sub(1);
        if self.part.len() > maximum {
            self.part.drain(..self.part.len() - maximum);
        }
    }

    /// The longest suffix of the part that recurs in the span with a cell after it, the latest
    /// among the longest.
    fn locate(&self, span: &[usize]) -> Option<(usize, u64)> {
        let n = self.part.len();
        let mut best: Option<(usize, usize)> = None;
        for j in (1..span.len()).rev() {
            let reach = n.min(j);
            let length = (1..=reach)
                .take_while(|&back| span[j - back] == self.part[n - back])
                .count();
            if length > best.map_or(0, |(_, longest)| longest) {
                best = Some((j, length));
                if length == n {
                    break;
                }
            }
        }
        best.map(|(j, length)| (j, length as u64))
    }
}

fn validate_address(
    suffix: &[usize],
    at: Option<(usize, u64)>,
    span: &[usize],
) -> Result<(), SpanReadingSnapshotError> {
    let Some((j, length)) = at else {
        return Ok(());
    };
    let length = usize::try_from(length).map_err(|_| SpanReadingSnapshotError::Address)?;
    if j >= span.len() || length == 0 || length > j || length > suffix.len() {
        return Err(SpanReadingSnapshotError::Address);
    }
    if suffix[suffix.len() - length..] != span[j - length..j] {
        return Err(SpanReadingSnapshotError::AddressMismatch);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn snapshot_keeps_only_the_future_relevant_suffix_and_continues_exactly() {
        let span = [0, 1, 2, 3, 4];
        let mut reading = SpanReading::new();
        for cell in [9, 8, 1, 2, 3] {
            reading.read(&span, cell);
        }
        let snapshot = reading.snapshot(&span).unwrap();
        assert_eq!(snapshot.received, 5);
        assert_eq!(snapshot.suffix, [8, 1, 2, 3]);
        let mut restored = SpanReading::restore(snapshot, &span).unwrap();
        assert_eq!(reading.located(&span), restored.located(&span));
        assert_eq!(reading.cells(), restored.cells());
        for cell in [4, 9, 0, 1] {
            reading.read(&span, cell);
            restored.read(&span, cell);
            assert_eq!(reading.located(&span), restored.located(&span));
            assert_eq!(reading.cells(), restored.cells());
        }
    }

    #[test]
    fn restore_rejects_a_forged_address_before_target_indexing() {
        let span = [0, 1, 2];
        let forged = SpanReadingSnapshot {
            received: 2,
            suffix: vec![1, 2],
            at: Some((9, 1)),
        };
        assert_eq!(
            SpanReading::restore(forged, &span),
            Err(SpanReadingSnapshotError::Address)
        );
    }

    #[test]
    fn restore_recomputes_the_latest_longest_address() {
        let span = [0, 1, 2, 1, 2, 3];
        let forged = SpanReadingSnapshot {
            received: 2,
            suffix: vec![1, 2],
            at: Some((2, 2)),
        };
        assert_eq!(
            SpanReading::restore(forged, &span),
            Err(SpanReadingSnapshotError::AddressMismatch)
        );
    }
}
