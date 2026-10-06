//! **The proofs of the guards built at the notebook's exterior boundary** (THE_MACHINE, "Guards
//! that make the rejected forms impossible", 19, 21 and 22). The constructions live in
//! `research/notebook/hnn_design/exterior.rs`, outside the library, because they read files and
//! run `git`; each doctest below includes that file as a module (`#[path]`, resolved from this
//! file's directory), so the guard is checked against the boundary the harnesses actually use.
//! This module exists only while rustdoc collects doctests (`#[cfg(doctest)]` in `lib.rs`): it adds
//! nothing to the library. Gate 1 runs it (`tools/gate.sh`, every library doctest, with the error
//! codes checked under `RUSTC_BOOTSTRAP=1`).
//!
//! # Guard 21: seen material is never graded as unseen
//!
//! A cut is read as its two parts: the development range as `Seen` and the held-out range as
//! `Held`. A `Seen` is refused where a `Held` is required (structural, `E0308`):
//!
//! ```compile_fail,E0308
//! #[path = "../../../research/notebook/hnn_design/exterior.rs"]
//! mod exterior;
//! fn grade(_truth: exterior::Held) {}
//! fn main() {
//!     let cut = exterior::read_cut("a cut.bin");
//!     grade(cut.seen);
//! }
//! ```
//!
//! A `Held` is never forged from bytes, seen ones included (structural, `E0451`: its fields are
//! the boundary's):
//!
//! ```compile_fail,E0451
//! #[path = "../../../research/notebook/hnn_design/exterior.rs"]
//! mod exterior;
//! fn main() {
//!     let cut = exterior::read_cut("a cut.bin");
//!     let _forged = exterior::Held { start: 0, bytes: cut.seen.bytes().to_vec() };
//! }
//! ```
//!
//! Its bytes are not read by reference, so no development read reaches them first (structural,
//! `E0599`):
//!
//! ```compile_fail,E0599
//! #[path = "../../../research/notebook/hnn_design/exterior.rs"]
//! mod exterior;
//! fn main() {
//!     let cut = exterior::read_cut("a cut.bin");
//!     let _training = cut.held.bytes();
//! }
//! ```
//!
//! and it is read once, by value: read, it is gone (structural, `E0382`):
//!
//! ```compile_fail,E0382
//! #[path = "../../../research/notebook/hnn_design/exterior.rs"]
//! mod exterior;
//! fn main() {
//!     let cut = exterior::read_cut("a cut.bin");
//!     let start = cut.held.range().start;
//!     let _graded = cut.held.windows(&[start], 48);
//!     let _again = cut.held.windows(&[start], 48);
//! }
//! ```
//!
//! The lawful forms compile: a grading takes the `Held` by value, a training passage reads the
//! `Seen` by reference, and the prequential exposure consumes the cut whole.
//!
//! ```no_run
//! #[path = "../../../research/notebook/hnn_design/exterior.rs"]
//! mod exterior;
//! fn grade(truth: exterior::Held) -> usize {
//!     let start = truth.range().start;
//!     truth.windows(&[start], 48).len()
//! }
//! fn main() {
//!     let cut = exterior::read_cut("a cut.bin");
//!     let _training = &cut.seen.bytes()[..48];
//!     let _graded = grade(cut.held);
//!     let (_whole, _held_out) = exterior::read_cut("a cut.bin").prequential();
//! }
//! ```
//!
//! # Guard 22: a run's limits are a committed pin's
//!
//! A pin is never built in code (structural, `E0451`) and its deadline has no setter (structural,
//! `E0616`):
//!
//! ```compile_fail,E0451
//! #[path = "../../../research/notebook/hnn_design/exterior.rs"]
//! mod exterior;
//! fn main() {
//!     let _raised = exterior::Pin {
//!         path: String::new(),
//!         command: "executed text".to_string(),
//!         projection: String::new(),
//!         deadline_ms: 900_000,
//!         unit_bound_ms: None,
//!         threads: 8,
//!         commit: String::new(),
//!     };
//! }
//! ```
//!
//! ```compile_fail,E0616
//! #[path = "../../../research/notebook/hnn_design/exterior.rs"]
//! mod exterior;
//! fn main() {
//!     let mut pin = exterior::Pin::read("research/runs/a.pin", "executed text");
//!     pin.deadline_ms = 900_000;
//! }
//! ```
//!
//! A missing pin refuses the run (a runtime law):
//!
//! ```should_panic
//! #[path = "../../../research/notebook/hnn_design/exterior.rs"]
//! mod exterior;
//! fn main() {
//!     exterior::Pin::read("no-such-directory/no-such.pin", "executed text");
//! }
//! ```
//!
//! A pin committed once is read; a pin edited after its commit, and a pin committed a second time
//! (a raised limit), are refused (runtime laws, read in a scratch repository):
//!
//! ```
//! #[path = "../../../research/notebook/hnn_design/exterior.rs"]
//! mod exterior;
//! use std::process::Command;
//! fn main() {
//!     let dir = std::env::temp_dir().join(format!("holonics-pin-{}", std::process::id()));
//!     let _ = std::fs::remove_dir_all(&dir);
//!     std::fs::create_dir_all(&dir).unwrap();
//!     let git = |args: &[&str]| {
//!         let status = Command::new("git")
//!             .arg("-C").arg(&dir)
//!             .args(["-c", "user.name=pin", "-c", "user.email=pin@example.invalid"])
//!             .args(["-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null"])
//!             .args(args)
//!             .output()
//!             .unwrap()
//!             .status;
//!         assert!(status.success(), "git {args:?}");
//!     };
//!     let pin = dir.join("text.pin");
//!     let path = pin.to_str().unwrap().to_string();
//!     let write = |deadline: u64| {
//!         std::fs::write(&pin, format!(
//!             "# a development read\ncommand = executed text\nprojection = 1 request of 60,000 ms\n\
//!              deadline_ms = {deadline}\nunit_bound_ms = 75000\nthreads = 8\n"
//!         )).unwrap();
//!     };
//!     git(&["init", "-q"]);
//!     write(75_000);
//!     // Untracked: refused.
//!     let read = |command: &'static str| {
//!         let path = path.clone();
//!         std::panic::catch_unwind(move || exterior::Pin::read(&path, command))
//!     };
//!     assert!(read("executed text").is_err());
//!     git(&["add", "text.pin"]);
//!     git(&["commit", "-q", "-m", "the pin"]);
//!     // Committed once: read, its numbers the file's.
//!     let once = read("executed text").expect("a pin committed once is read");
//!     assert_eq!((once.deadline_ms(), once.unit_bound_ms(), once.threads()), (75_000, Some(75_000), 8));
//!     // Another command's pin: refused.
//!     assert!(read("executed train").is_err());
//!     // Raised in the working tree: refused.
//!     write(900_000);
//!     assert!(read("executed text").is_err());
//!     // Raised and committed a second time: refused.
//!     git(&["commit", "-q", "-am", "a raised limit"]);
//!     assert!(read("executed text").is_err());
//!     std::fs::remove_dir_all(&dir).unwrap();
//! }
//! ```
//!
//! # Guard 19: one release, shown whole, with its copy length
//!
//! The copy length is `tools/copy_length.py`'s law: here against the quadratic definition (the
//! longest common substring with one passage, the bytes covered by windows of `K` release bytes
//! occurring in one passage) on pseudo-random releases and passages, and on the tool's own cases.
//!
//! ```
//! #[path = "../../../research/notebook/hnn_design/exterior.rs"]
//! mod exterior;
//! /// (copy length, release start, passage, covered) from the definition.
//! fn reference(release: &[u8], passages: &[&[u8]], k: usize) -> (usize, Option<usize>, Option<usize>, usize) {
//!     let (mut best, mut at) = (0usize, None);
//!     let mut covered = vec![false; release.len()];
//!     let occurs = |w: &[u8], p: &[u8]| p.windows(w.len()).any(|x| x == w);
//!     for (f, passage) in passages.iter().enumerate() {
//!         for a in 0..release.len() {
//!             for b in a + 1..=release.len() {
//!                 if !occurs(&release[a..b], passage) {
//!                     break;
//!                 }
//!                 let candidate = (b - a, a, f);
//!                 if candidate.0 > best || (candidate.0 == best && at.is_some_and(|(s, g)| (a, f) < (s, g))) {
//!                     best = candidate.0;
//!                     at = Some((a, f));
//!                 }
//!             }
//!         }
//!         for a in 0..(release.len() + 1).saturating_sub(k) {
//!             if occurs(&release[a..a + k], passage) {
//!                 covered[a..a + k].iter_mut().for_each(|c| *c = true);
//!             }
//!         }
//!     }
//!     let count = covered.iter().filter(|&&c| c).count();
//!     (best, at.map(|(s, _)| s), at.map(|(_, f)| f), if best == 0 { 0 } else { count })
//! }
//! fn main() {
//!     let none = exterior::copy_length(b"abcdef", &[b"uvwxyz", b"ghijkl"], 8);
//!     assert_eq!(none.to_string(), "copy_length 0\nrelease_start -1\npassage_file -1\npassage_offset -1\ncovered_bytes 0\nmin_run 8\nrelease_bytes 6\npassage_bytes 12");
//!     let fox = exterior::copy_length(b"brown fox jumps", &[b"the quick brown fox jumps over the lazy dog"], 8);
//!     assert_eq!((fox.copy_length, fox.release_start, fox.passage_file, fox.passage_offset, fox.covered_bytes), (15, Some(0), Some(0), Some(10), 15));
//!     // A run never spans two passages.
//!     let split = exterior::copy_length(b"abcdefgh", &[b"xxabcd", b"efghyy"], 2);
//!     assert_eq!((split.copy_length, split.release_start, split.passage_file, split.passage_offset), (4, Some(0), Some(0), Some(2)));
//!     let mut state: u64 = 0x2026_1005;
//!     let mut next = |modulus: u64| {
//!         state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
//!         (state >> 33) % modulus
//!     };
//!     for case in 0..300 {
//!         let alphabet = 2 + next(4);
//!         let release: Vec<u8> = (0..next(24)).map(|_| b'a' + next(alphabet) as u8).collect();
//!         let passages: Vec<Vec<u8>> = (0..1 + next(3))
//!             .map(|_| (0..next(40)).map(|_| b'a' + next(alphabet) as u8).collect())
//!             .collect();
//!         let views: Vec<&[u8]> = passages.iter().map(Vec::as_slice).collect();
//!         let k = 1 + next(6) as usize;
//!         let receipt = exterior::copy_length(&release, &views, k);
//!         assert_eq!(
//!             (receipt.copy_length, receipt.release_start, receipt.passage_file, receipt.covered_bytes),
//!             reference(&release, &views, k),
//!             "case {case}"
//!         );
//!         if let (Some(start), Some(file), Some(offset)) = (receipt.release_start, receipt.passage_file, receipt.passage_offset) {
//!             let run = &release[start..start + receipt.copy_length];
//!             assert_eq!(&views[file][offset..offset + run.len()], run);
//!             assert!(!views[file][..offset + run.len() - 1].windows(run.len()).any(|w| w == run));
//!         }
//!     }
//! }
//! ```
//!
//! `show_release` writes the release whole, beside the private show of the release with its
//! receipt:
//!
//! ```
//! #[path = "../../../research/notebook/hnn_design/exterior.rs"]
//! mod exterior;
//! fn main() {
//!     let out = std::env::temp_dir().join(format!("holonics-show-{}", std::process::id()));
//!     std::fs::create_dir_all(&out).unwrap();
//!     let out = out.to_str().unwrap();
//!     let release = b"ab\ncd\x01";
//!     let receipt = exterior::show_release(out, "r_0.release", release, &[b"xxcd\x01", b"ab"]);
//!     assert_eq!(std::fs::read(format!("{out}/r_0.release")).unwrap(), release);
//!     let show = std::fs::read_to_string(format!("{out}/releases.show")).unwrap();
//!     assert!(show.starts_with("r_0.release (6 bytes): ab\\ncd\\x01\ncopy_length 3\n"), "{show}");
//!     assert_eq!((receipt.copy_length, receipt.passage_file), (3, Some(0)));
//!     std::fs::remove_dir_all(out).unwrap();
//! }
//! ```
