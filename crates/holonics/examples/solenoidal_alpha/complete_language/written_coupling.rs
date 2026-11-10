//! The least-friction coupling of each written release with the held-out answer.
//!
//! An exterior reading: it reads a learner's written releases and the held-out text, nothing here
//! enters the learning machine or selects a release, and no float is stored or computed. The
//! repository's success test reads the contact of a release `H` with its target `T`
//! ([`holonics::receiver::coupling`]): `λ` is the greatest number of equal, strictly order-consistent
//! contacts and the friction `F* = |H| + |T| − 2λ`. It reads the whole answer's contact, so a receipt
//! is not the bits of a code alone.
//!
//! `read-written-coupling HELD HELD_SHA DIR` reads, pinned by its SHA-256, the held-out text `HELD`
//! split into problems (separated by a blank line, each a question line and its
//! answer lines) and `DIR/FREE.tsv` as it parses it (one line a release: the problem's index and the
//! release's bytes escaped as `read-unit-tower-written` writes them, tab-separated; a line without
//! two fields is refused). FREE.tsv may hold releases for some of the problems, indices rising; the
//! rest are not read. For each problem `i` that holds a release:
//!
//! - `H` is the release's bytes up to its first blank line, `T` the held-out answer's lines joined
//!   by a line end (without the line end that closes the problem, so a release that copies the
//!   answer and then the blank line is exactly `T`), `Q_i` the problem's question line and `Q_next`
//!   the next problem's (the last problem's next is the first, over all of HELD's problems).
//! - Each pair is read in two charts: the bytes, and the numerals, the matches of `\d+(?:\.\d+)?`
//!   (ASCII digits) each compared as its bytes.
//!
//! Per chart one line is printed, summed over the problems that hold a release:
//! `WRITTEN_COUPLING chart=<bytes|numerals> problems=N held=Σ|T| written=Σ|H| lambda=Σλ(H,T)
//! friction=ΣF*(H,T) plateaus=Σ(plateau count) longest=max plateau length question_own=Σλ(H,Q_i)
//! question_next=Σλ(H,Q_next)`. The last two read how much of its own question a release takes up
//! against another question's: the question's contact, whether the release is steered by its
//! question. `DIR/COUPLING.tsv` (created, never overwritten; no header) holds one row a problem and
//! chart: index, chart, `|H|`, `|T|`, `λ`, `F*`, plateau count, longest plateau, `λ` with its own
//! question, `λ` with the next.
//!
//! [definition; agent-inferred, October 31] Two choices the task left to the reading. `T` drops the
//! line end that closes a problem, because a release that copies its answer and then the blank line
//! is cut to exactly `T` and must read `F* = 0`; with the closing line end in `T` a perfect copy
//! would read `F* = 1`. A `FREE.tsv` may hold releases for some of the problems, so a partial read of
//! a run is read as it stands; indices must still rise.
//!
//! Recorded failures this reading cannot repeat: it is read only after the release is written, so no
//! release is chosen by it; and a code's bits, or a copied passage, are not progress by themselves:
//! `question_own` against `question_next` separates a release that takes up its own question from one
//! that takes up any.

use super::tower_train::problems_of;
use super::*;
use holonics::receiver::coupling::coupling;

/// A numeral: a match of `\d+(?:\.\d+)?`, the digits and, when digits follow it, a '.' with them.
fn numerals(bytes: &[u8]) -> Vec<&[u8]> {
    let digits = |from: usize| bytes[from..].iter().take_while(|b| b.is_ascii_digit()).count();
    let mut found = Vec::new();
    let mut at = 0;
    while at < bytes.len() {
        if !bytes[at].is_ascii_digit() {
            at += 1;
            continue;
        }
        let mut end = at + digits(at);
        if bytes.get(end) == Some(&b'.') {
            let after = digits(end + 1);
            if after > 0 {
                end += 1 + after;
            }
        }
        found.push(&bytes[at..end]);
        at = end;
    }
    found
}

/// A free release's answer: its bytes up to its first blank line.
fn cut_release(release: &[u8]) -> &[u8] {
    release.windows(2).position(|w| w == b"\n\n").map_or(release, |at| &release[..at])
}

/// A problem's question line and its answer lines joined by line ends: the text past the first line
/// end, without the one line end that closes the problem.
fn question_and_answer(problem: &[u8]) -> (&[u8], &[u8]) {
    let line = problem.iter().position(|&b| b == b'\n').unwrap_or(problem.len());
    let answer = &problem[(line + 1).min(problem.len())..];
    (&problem[..line], answer.strip_suffix(b"\n").unwrap_or(answer))
}

/// The bytes a `FREE.tsv` field escapes: `\\`, `\'`, `\"`, `\t`, `\n`, `\r` and `\xNN`, as
/// `read-lines` and `release-field` write them. Any other escape is refused.
pub(super) fn unescape(field: &[u8]) -> Result<Vec<u8>> {
    let hex = |b: u8| (b as char).to_digit(16).map(|d| d as u8);
    let mut out = Vec::with_capacity(field.len());
    let mut at = 0;
    while at < field.len() {
        let b = field[at];
        at += 1;
        if b != b'\\' {
            out.push(b);
            continue;
        }
        let escape = *field.get(at).ok_or("a field ends in a lone backslash")?;
        at += 1;
        match escape {
            b'\\' | b'\'' | b'"' => out.push(escape),
            b't' => out.push(b'\t'),
            b'n' => out.push(b'\n'),
            b'r' => out.push(b'\r'),
            b'x' => {
                let pair = field.get(at..at + 2).ok_or("a field ends in a truncated \\x escape")?;
                match (hex(pair[0]), hex(pair[1])) {
                    (Some(high), Some(low)) => out.push(high << 4 | low),
                    _ => return Err("a \\x escape without two hexadecimal digits".into()),
                }
                at += 2;
            }
            other => return Err(format!("an escape \\{} that a release field never holds", other.escape_ascii()).into()),
        }
    }
    Ok(out)
}

/// `FREE.tsv`: the releases it holds, as (problem index, release bytes) with rising indices below
/// `problems`.
fn read_free(tsv: &[u8], problems: usize) -> Result<Vec<(usize, Vec<u8>)>> {
    let mut lines: Vec<&[u8]> = tsv.split(|&b| b == b'\n').collect();
    if lines.last().is_some_and(|l| l.is_empty()) {
        lines.pop();
    }
    let mut rows: Vec<(usize, Vec<u8>)> = Vec::new();
    for line in lines {
        let fields: Vec<&[u8]> = line.split(|&b| b == b'\t').collect();
        if fields.len() != 2 {
            return Err(format!("FREE.tsv: a line with {} fields, not 2", fields.len()).into());
        }
        let index: usize = std::str::from_utf8(fields[0])?.parse()?;
        if index >= problems || rows.last().is_some_and(|(last, _)| *last >= index) {
            return Err(format!("FREE.tsv: release index {index} is not a rising index below the {problems} problems").into());
        }
        rows.push((index, unescape(fields[1])?));
    }
    Ok(rows)
}

/// One problem's release read against its answer in one chart.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Reading {
    written: usize,
    held: usize,
    lambda: usize,
    friction: usize,
    plateaus: usize,
    longest: usize,
    own: usize,
    next: usize,
}

/// `H` against `T` by [`coupling`], and against the problem's own question and the next problem's.
fn read_chart<C: Eq>(h: &[C], t: &[C], own: &[C], next: &[C]) -> Result<Reading> {
    let c = coupling(h, t).map_err(|e| e.to_string())?;
    Ok(Reading {
        written: h.len(),
        held: t.len(),
        lambda: c.lambda,
        friction: c.least_friction,
        plateaus: c.maximal_contiguous_plateaus.len(),
        longest: c.maximal_contiguous_plateaus.iter().map(|p| p.length).max().unwrap_or(0),
        own: coupling(h, own).map_err(|e| e.to_string())?.lambda,
        next: coupling(h, next).map_err(|e| e.to_string())?.lambda,
    })
}

/// A chart's readings summed over the problems that hold a release.
#[derive(Default)]
struct Summary {
    problems: usize,
    sum: [usize; 7],
    longest: usize,
}

impl Summary {
    fn add(&mut self, r: &Reading) {
        self.problems += 1;
        for (sum, value) in self.sum.iter_mut().zip([r.held, r.written, r.lambda, r.friction, r.plateaus, r.own, r.next]) {
            *sum += value;
        }
        self.longest = self.longest.max(r.longest);
    }

    fn line(&self, chart: &str) -> String {
        let [held, written, lambda, friction, plateaus, own, next] = self.sum;
        format!(
            "WRITTEN_COUPLING chart={chart} problems={} held={held} written={written} lambda={lambda} friction={friction} \
             plateaus={plateaus} longest={} question_own={own} question_next={next}",
            self.problems, self.longest
        )
    }
}

/// The `COUPLING.tsv` text and the two summary lines (bytes, then numerals) of the releases in a
/// `FREE.tsv` against the held-out text.
fn read_written(held: &[u8], free: &[u8]) -> Result<(String, [String; 2])> {
    let problems: Vec<(&[u8], &[u8])> = problems_of(held).into_iter().map(question_and_answer).collect();
    if problems.is_empty() {
        return Err("a held text without problems".into());
    }
    let (mut tsv, mut bytes, mut numeral) = (String::new(), Summary::default(), Summary::default());
    for (i, release) in read_free(free, problems.len())? {
        let (own, truth) = (problems[i].0, problems[i].1);
        let next = problems[(i + 1) % problems.len()].0;
        let release = cut_release(&release);
        let readings = [
            ("bytes", read_chart(release, truth, own, next)?),
            ("numerals", read_chart(&numerals(release), &numerals(truth), &numerals(own), &numerals(next))?),
        ];
        for ((chart, r), summary) in readings.iter().zip([&mut bytes, &mut numeral]) {
            tsv.push_str(&format!(
                "{i}\t{chart}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                r.written, r.held, r.lambda, r.friction, r.plateaus, r.longest, r.own, r.next
            ));
            summary.add(r);
        }
    }
    Ok((tsv, [bytes.line("bytes"), numeral.line("numerals")]))
}

/// `read-written-coupling HELD HELD_SHA DIR`: the module's reading. `DIR` holds the `FREE.tsv` a
/// release route writes and receives `COUPLING.tsv`.
pub(super) fn read(args: &[String]) -> Result<()> {
    if args.len() != 4 {
        return Err("read-written-coupling HELD HELD_SHA DIR".into());
    }
    let held = pinned_read(&args[1], &args[2], READ_BUDGET as usize)?;
    let dir = Path::new(&args[3]);
    let free = dir.join("FREE.tsv");
    if std::fs::metadata(&free)?.len() > READ_BUDGET {
        return Err("declared input extent exceeded".into());
    }
    let (tsv, lines) = read_written(&held, &std::fs::read(free)?)?;
    write_new(&dir.join("COUPLING.tsv"), tsv.as_bytes())?;
    for line in lines {
        println!("{line}");
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The longest common subsequence by the plain recurrence, as an independent count of `λ`.
    fn lcs<C: Eq>(a: &[C], b: &[C]) -> usize {
        let mut row = vec![0usize; b.len() + 1];
        for x in a {
            let mut diagonal = 0;
            for (j, y) in b.iter().enumerate() {
                let above = row[j + 1];
                row[j + 1] = if x == y { diagonal + 1 } else { above.max(row[j]) };
                diagonal = above;
            }
        }
        row[b.len()]
    }

    fn escape(bytes: &[u8]) -> String {
        bytes.escape_ascii().to_string()
    }

    /// Three problems: questions write {12, 5}, {9} and {100, 7}; answers `12 pears …`, `9 pens …`
    /// and `100 coins …`.
    const QUESTIONS: [&str; 3] = ["Ann has 12 pears and 5 figs?", "Bob has 9 pens?", "Cy has 100 coins and 7 hats."];
    const ANSWERS: [&str; 3] = ["12 pears and 5 figs make 17.\n#### 17", "9 pens.\n#### 9", "100 coins, 7 hats = 107.\n#### 107"];

    fn held() -> Vec<u8> {
        QUESTIONS.iter().zip(ANSWERS).map(|(q, a)| format!("{q}\n{a}\n\n")).collect::<String>().into_bytes()
    }

    fn free(releases: &[(usize, &str)]) -> Vec<u8> {
        releases.iter().map(|(i, r)| format!("{i}\t{}\n", escape(r.as_bytes()))).collect::<String>().into_bytes()
    }

    fn rows(tsv: &str) -> Vec<Vec<String>> {
        tsv.lines().map(|l| l.split('\t').map(str::to_owned).collect()).collect()
    }

    #[test]
    fn a_numeral_is_the_digits_and_a_decimal_point_followed_by_digits() {
        let found = |s: &str| numerals(s.as_bytes()).into_iter().map(|n| String::from_utf8(n.to_vec()).expect("ascii")).collect::<Vec<_>>();
        assert_eq!(found("12 pears, 3.5 kg, 3. 4.50.7 1,500 x9"), ["12", "3.5", "3", "4.50", "7", "1", "500", "9"]);
        assert_eq!(found(".5 5. a"), ["5", "5"]);
        assert!(found("none, #### ").is_empty());
    }

    #[test]
    fn a_release_is_cut_at_its_first_blank_line_and_a_field_unescapes_exactly() {
        assert_eq!(cut_release(b"a\nb\n\nc\n\nd"), b"a\nb");
        assert_eq!(cut_release(b"a\nb\n"), b"a\nb\n");
        assert_eq!(cut_release(b"\n\n\nx"), b"");
        let all: Vec<u8> = (0..=255u8).collect();
        assert_eq!(unescape(escape(&all).as_bytes()).expect("round trip"), all);
        assert_eq!(unescape(b"a\\x7c\\t\\\\").expect("pipe"), b"a|\t\\");
        assert!(unescape(b"a\\").is_err());
        assert!(unescape(b"\\x4").is_err());
        assert!(unescape(b"\\xzz").is_err());
        assert!(unescape(b"\\101").is_err());
    }

    #[test]
    fn a_problem_is_its_question_line_and_its_answer_lines_joined() {
        let held = held();
        let problems: Vec<_> = problems_of(&held).into_iter().map(question_and_answer).collect();
        assert_eq!(problems.len(), 3);
        for (i, (q, a)) in problems.iter().enumerate() {
            assert_eq!((*q, *a), (QUESTIONS[i].as_bytes(), ANSWERS[i].as_bytes()));
        }
        // The last problem without the blank line that closes it reads the same.
        let open = &held[..held.len() - 2];
        let last = problems_of(open).into_iter().map(question_and_answer).last().expect("problem");
        assert_eq!(last, (QUESTIONS[2].as_bytes(), ANSWERS[2].as_bytes()));
    }

    #[test]
    fn a_release_equal_to_its_answer_couples_at_every_cell_and_a_disjoint_one_at_none() {
        let held = held();
        // Problem 0 copies its answer, then its blank line and more (cut at the blank line); problem 1
        // writes letters (and no space) its answer never holds.
        let tsv = free(&[(0, "12 pears and 5 figs make 17.\n#### 17\n\nBob has 9 pens?"), (1, "zzzzzzzz")]);
        let (rows_tsv, lines) = read_written(&held, &tsv).expect("read");
        let rows = rows(&rows_tsv);
        let (t0, t1) = (ANSWERS[0].len(), ANSWERS[1].len());
        // index, chart, |H|, |T|, λ, F*, plateaus, longest, own, next
        assert_eq!(rows[0], ["0", "bytes", &t0.to_string(), &t0.to_string(), &t0.to_string(), "0", "1", &t0.to_string(), &lcs(ANSWERS[0].as_bytes(), QUESTIONS[0].as_bytes()).to_string(), &lcs(ANSWERS[0].as_bytes(), QUESTIONS[1].as_bytes()).to_string()]);
        assert_eq!(rows[1], ["0", "numerals", "4", "4", "4", "0", "1", "4", "2", "0"]);
        assert_eq!(rows[2], ["1", "bytes", "8", &t1.to_string(), "0", &(8 + t1).to_string(), "0", "0", "0", "0"]);
        assert_eq!(rows[3], ["1", "numerals", "0", "2", "0", "2", "0", "0", "0", "0"]);
        assert_eq!(rows.len(), 4);
        assert!(lines[0].starts_with("WRITTEN_COUPLING chart=bytes problems=2 "), "{}", lines[0]);
        assert!(lines[1].starts_with("WRITTEN_COUPLING chart=numerals problems=2 held=6 written=4 lambda=4 friction=2 plateaus=1 longest=4 "), "{}", lines[1]);
    }

    #[test]
    fn the_numerals_chart_and_the_own_and_next_questions_are_read_apart() {
        let held = held();
        let tsv = free(&[
            // Copies its answer: both questions' contacts are Q0's numerals in order, and Q1's `9`.
            (0, "12 pears and 5 figs make 17.\n#### 17"),
            // Takes up the next problem's question (`100`, `7`), not its own (`9`).
            (1, "100 coins and 7 pens"),
            // Wrong at its first and last numerals, writes the first problem's question, which is its
            // next (the last problem's next is the first).
            (2, "100 coins, 8 hats = 108 with 12 and 5.\n#### 108"),
        ]);
        let (rows_tsv, lines) = read_written(&held, &tsv).expect("read");
        let rows = rows(&rows_tsv);
        let numerals_rows: Vec<_> = rows.iter().filter(|r| r[1] == "numerals").collect();
        // H = [12 5 17 17] against T = [12 5 17 17]: λ 4, one plateau of 4; Q0 = [12 5]: 2; Q1 = [9]: 0.
        assert_eq!(numerals_rows[0], &["0", "numerals", "4", "4", "4", "0", "1", "4", "2", "0"]);
        // H = [100 7], T = [9 9]: nothing; own Q1 = [9]: 0; next Q2 = [100 7]: 2.
        assert_eq!(numerals_rows[1], &["1", "numerals", "2", "2", "0", "4", "0", "0", "0", "2"]);
        // H = [100 8 108 12 5 108], T = [100 7 107 107]: λ 1 (the `100`), one plateau of 1; own Q2 =
        // [100 7]: 1; next Q0 = [12 5]: 2.
        assert_eq!(numerals_rows[2], &["2", "numerals", "6", "4", "1", "8", "1", "1", "1", "2"]);
        assert_eq!(
            lines[1],
            "WRITTEN_COUPLING chart=numerals problems=3 held=10 written=12 lambda=5 friction=12 plateaus=2 longest=4 question_own=3 question_next=4"
        );
        // The bytes chart agrees with the plain recurrence on every pair, and F* = |H| + |T| − 2λ.
        let releases = ["12 pears and 5 figs make 17.\n#### 17", "100 coins and 7 pens", "100 coins, 8 hats = 108 with 12 and 5.\n#### 108"];
        let mut sums = [0usize; 5];
        for i in 0..3 {
            let (h, t) = (releases[i].as_bytes(), ANSWERS[i].as_bytes());
            let (own, next) = (QUESTIONS[i].as_bytes(), QUESTIONS[(i + 1) % 3].as_bytes());
            let row = &rows[2 * i];
            assert_eq!(row[1], "bytes");
            let lambda = lcs(h, t);
            assert_eq!(row[4], lambda.to_string());
            assert_eq!(row[5], (h.len() + t.len() - 2 * lambda).to_string());
            assert_eq!(row[8], lcs(h, own).to_string());
            assert_eq!(row[9], lcs(h, next).to_string());
            sums = [sums[0] + t.len(), sums[1] + h.len(), sums[2] + lambda, sums[3] + h.len() + t.len() - 2 * lambda, sums[4] + lcs(h, own)];
        }
        assert!(lines[0].starts_with(&format!(
            "WRITTEN_COUPLING chart=bytes problems=3 held={} written={} lambda={} friction={} ",
            sums[0], sums[1], sums[2], sums[3]
        )), "{}", lines[0]);
        assert!(lines[0].contains(&format!(" question_own={} ", sums[4])), "{}", lines[0]);
    }

    #[test]
    fn only_the_problems_that_hold_a_release_are_read_and_the_next_question_wraps_over_all() {
        let held = held();
        // Releases for problems 0 and 2 only: problem 0's next is problem 1's question (no release),
        // problem 2's is problem 0's.
        let tsv = free(&[(0, "9 pens"), (2, "12 and 5")]);
        let (rows_tsv, lines) = read_written(&held, &tsv).expect("read");
        let rows = rows(&rows_tsv);
        assert_eq!(rows.len(), 4);
        assert_eq!(rows[1], ["0", "numerals", "1", "4", "0", "5", "0", "0", "0", "1"]);
        assert_eq!(rows[3], ["2", "numerals", "2", "4", "0", "6", "0", "0", "0", "2"]);
        assert!(lines[1].contains("problems=2 "), "{}", lines[1]);
    }

    #[test]
    fn a_free_file_that_is_not_one_rising_release_a_problem_is_refused() {
        let held = held();
        for bad in ["0\ta\n0\tb\n", "1\ta\n0\tb\n", "3\ta\n", "0\ta\tb\n", "0\n", "x\ta\n", "0\ta\\q\n", "\n"] {
            assert!(read_written(&held, bad.as_bytes()).is_err(), "{bad:?}");
        }
        assert!(read_written(b"\n\n", b"").is_err());
        assert_eq!(read_written(&held, b"").expect("no releases").0, "");
    }

    #[test]
    fn the_route_pins_the_held_text_and_never_overwrites_the_coupling() {
        let dir = std::env::temp_dir().join(format!("holonics-written-coupling-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("dir");
        let held = held();
        std::fs::write(dir.join("HELD"), &held).expect("held");
        std::fs::write(dir.join("FREE.tsv"), free(&[(0, ANSWERS[0]), (1, "9 pens.\n#### 9\n\nQ?")])).expect("free");
        let at = |name: &str| dir.join(name).to_string_lossy().into_owned();
        let sha = sha256(&held).expect("sha");
        let command = |pin: &str| ["read-written-coupling".to_owned(), at("HELD"), pin.to_owned(), dir.to_string_lossy().into_owned()];
        assert!(read(&command(&"0".repeat(64))).is_err());
        assert!(!dir.join("COUPLING.tsv").exists());
        read(&command(&sha)).expect("read");
        let tsv = std::fs::read_to_string(dir.join("COUPLING.tsv")).expect("coupling");
        assert_eq!(tsv.lines().count(), 4);
        assert!(read(&command(&sha)).is_err());
        assert_eq!(std::fs::read_to_string(dir.join("COUPLING.tsv")).expect("coupling"), tsv);
        assert!(read(&["read-written-coupling".to_owned()]).is_err());
        std::fs::remove_dir_all(&dir).expect("cleanup");
    }
}
