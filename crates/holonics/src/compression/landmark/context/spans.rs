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
    part: Vec<usize>,
    at: Option<(usize, u64)>,
}

impl SpanReading {
    /// A part before its first cell: nothing located.
    pub fn new() -> Self {
        Self::default()
    }

    /// The part's cells read so far.
    pub fn cells(&self) -> usize {
        self.part.len()
    }

    /// **The located continuation** on `span`, when a suffix recurs.
    pub fn located(&self, span: &[usize]) -> Option<Located> {
        self.at.map(|(j, length)| Located {
            length,
            next: span[j],
        })
    }

    /// **Read one cell of the part** (module header): the occurrence continues, or is located anew.
    pub fn read(&mut self, span: &[usize], cell: usize) {
        self.part.push(cell);
        self.at = match self.at {
            Some((j, length)) if span[j] == cell && j + 1 < span.len() => Some((j + 1, length + 1)),
            _ => self.locate(span),
        };
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
