//! [definition; agent-inferred, October 29] **The continuing body's commands**
//! (`hnn::tower::body`; record `2026-10-29_THE_CONTINUING_BODY_RESTS_WITH_ITS_CURRENTS_…`). Each
//! command reads a body pinned by its SHA-256 (a learner, to found one), runs one operation through
//! the declared realization (the host's here; the card's through `holonics-cuda`'s `tower_pass`
//! example), and writes the body after it create-new. A body therefore rests between every two
//! operations and the next starts cold from its text; each write is read back and re-encoded before
//! it is reported.
//!
//! - `found-tower-body STATE STATE_SHA CURRENTS SECTION OUT`: `CURRENTS` hearing currents and the
//!   conversation, each at rest with the end letter pending.
//! - `hear-tower-body BODY BODY_SHA PASSAGE PASSAGE_SHA OUT`: a class passage heard, cut into one
//!   contiguous part a hearing current, every whole section closed.
//! - `ask-tower-body BODY BODY_SHA PROMPTS PROMPTS_SHA KEYS KEYS_SHA COUNT AGREE OUT`: each prompt of
//!   the class file (closed by its end letter) asked in turn on the conversation, each releasing at
//!   most `COUNT` classes by `AGREE` agreeing draws from the declared key stream at the body's draw
//!   state. `OUT` is a directory: the body after the asks (`BODY`), the releases
//!   (`RELEASES.tsv`, `RELEASES.classes`) and, on a participating body, each answer's participation at
//!   its opening (`PARTICIPATION.tsv`), the sites of the conversation's open section.
//! - `answer-tower-body BODY BODY_SHA ANSWER ANSWER_SHA OUT`: the class file heard as the target of the
//!   last ask, compared with its end letter.
//!
//! Nothing here is text-specific: the classes are the exterior codec's (octets and the end letter,
//! the alphabet's last), and the releases print their octets beside the classes.
use super::tower_classes::{classes_of, participation_rows, PARTICIPATION_HEAD};
use super::tower_train::{agreement, per, positive, STATE_BUDGET};
use super::*;
use holonics::hnn::tower::body::{Hearing, TowerBody};
use holonics::hnn::tower::realization::{HostPass, PassRealization};
use holonics::hnn::tower::TowerLearner;

pub(super) fn found(args: &[String]) -> Result<()> {
    if args.len() != 6 {
        return Err("found-tower-body STATE STATE_SHA CURRENTS SECTION OUT".into());
    }
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let body = TowerBody::found(learner, positive(&args[3])?, positive(&args[4])?).map_err(|e| e.to_string())?;
    rest(&body, Path::new(&args[5]), "found", &Hearing::default(), std::time::Instant::now())
}

pub(super) fn hear(args: &[String]) -> Result<()> {
    hear_realized(args, &mut HostPass::default())
}

pub(crate) fn hear_realized(args: &[String], realization: &mut dyn PassRealization) -> Result<()> {
    if args.len() != 6 {
        return Err("hear-tower-body BODY BODY_SHA PASSAGE PASSAGE_SHA OUT".into());
    }
    let started = std::time::Instant::now();
    let mut body = read_body(&args[1], &args[2], realization)?;
    let passage = classes_of(&pinned_read(&args[3], &args[4], READ_BUDGET as usize)?, body.learner.tower.declaration.alphabet)?;
    let heard = body.hear(&passage, realization).map_err(|e| e.to_string())?;
    rest(&body, Path::new(&args[5]), "hear", &heard, started)
}

pub(super) fn ask(args: &[String]) -> Result<()> {
    ask_realized(args, &mut HostPass::default())
}

pub(crate) fn ask_realized(args: &[String], realization: &mut dyn PassRealization) -> Result<()> {
    if args.len() != 10 {
        return Err("ask-tower-body BODY BODY_SHA PROMPTS PROMPTS_SHA KEYS KEYS_SHA COUNT AGREE OUT".into());
    }
    let started = std::time::Instant::now();
    let mut body = read_body(&args[1], &args[2], realization)?;
    let end = body.learner.tower.declaration.alphabet - 1;
    let classes = classes_of(&pinned_read(&args[3], &args[4], READ_BUDGET as usize)?, end + 1)?;
    let keys = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let count = positive(&args[7])?;
    let agree = agreement(args.get(8))?;
    let out = Path::new(&args[9]);
    let prompts: Vec<&[usize]> = classes.split_inclusive(|&c| c == end).collect();
    if prompts.is_empty() || prompts.iter().any(|p| p.len() < 2 || p.last() != Some(&end)) {
        return Err("every prompt is nonempty and closes with the end letter".into());
    }
    std::fs::create_dir(out)?;
    let mut rows = String::from("prompt\tprompt_classes\tdrawn_from\treleased\tended\toctets\n");
    let mut participation = String::from(PARTICIPATION_HEAD);
    let (mut written, mut heard) = (Vec::new(), Hearing::default());
    for (p, prompt) in prompts.iter().enumerate() {
        let from = body.drawn();
        let answer = body.ask(&prompt[..prompt.len() - 1], &keys, count, agree, realization).map_err(|e| e.to_string())?;
        if let Some(levels) = &answer.participation {
            participation_rows(p, &answer.read, levels, &mut participation);
        }
        for &c in &answer.released {
            written.extend_from_slice(&(c as u16).to_be_bytes());
        }
        let shown: String = answer.released.iter().filter(|&&c| c < 256).map(|&c| (c as u8).escape_ascii().to_string()).collect();
        rows.push_str(&format!("{p}\t{}\t{from}\t{}\t{}\t{shown}\n", prompt.len() - 1, answer.released.len(), answer.ended));
        println!("TOWER_BODY_ASK prompt={p} prompt_classes={} drawn_from={from} released={} ended={} sites={}", prompt.len() - 1, answer.released.len(), answer.ended, answer.read.len());
        heard.join(answer.hearing);
    }
    write_new(&out.join("RELEASES.classes"), &written)?;
    write_new(&out.join("RELEASES.tsv"), rows.as_bytes())?;
    if body.learner.tower.participation().is_some() {
        write_new(&out.join("PARTICIPATION.tsv"), participation.as_bytes())?;
    }
    rest(&body, &out.join("BODY"), "ask", &heard, started)
}

pub(super) fn answer(args: &[String]) -> Result<()> {
    answer_realized(args, &mut HostPass::default())
}

pub(crate) fn answer_realized(args: &[String], realization: &mut dyn PassRealization) -> Result<()> {
    if args.len() != 6 {
        return Err("answer-tower-body BODY BODY_SHA ANSWER ANSWER_SHA OUT".into());
    }
    let started = std::time::Instant::now();
    let mut body = read_body(&args[1], &args[2], realization)?;
    let answer = classes_of(&pinned_read(&args[3], &args[4], READ_BUDGET as usize)?, body.learner.tower.declaration.alphabet)?;
    let heard = body.answer(&answer, realization).map_err(|e| e.to_string())?;
    rest(&body, Path::new(&args[5]), "answer", &heard, started)
}

/// The body read from its pinned text, admitted by the realization.
fn read_body(path: &str, sha: &str, realization: &mut dyn PassRealization) -> Result<TowerBody> {
    let body = TowerBody::from_text(std::str::from_utf8(&pinned_read(path, sha, STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    realization.admit(&body.learner.tower).map_err(|e| e.to_string())?;
    println!("TOWER_REALIZATION {}", realization.realization());
    Ok(body)
}

/// The body written create-new, read back and re-encoded equal, and its receipt printed: the
/// operation's learned and read sections, its deposits, the learned sections' compared cells and
/// their code before and after a class, the body's currents, section and keys drawn, the pending
/// classes it holds, and its SHA-256.
fn rest(body: &TowerBody, out: &Path, operation: &str, heard: &Hearing, started: std::time::Instant) -> Result<()> {
    let text = body.to_text();
    write_new(out, text.as_bytes())?;
    let read = std::fs::read(out)?;
    if TowerBody::from_text(std::str::from_utf8(&read)?).map_err(|e| e.to_string())?.to_text() != text {
        return Err("the body's text does not re-encode equal".into());
    }
    let pending: Vec<String> = body.currents().iter().chain([body.conversation()]).map(|c| c.pending.len().to_string()).collect();
    let bits = if heard.cells == 0 { "-".to_string() } else { format!("{}->{}", per(heard.code_before, heard.cells), per(heard.code_after, heard.cells)) };
    println!(
        "TOWER_BODY op={operation} learned={} read={} deposits={} cells={} bits_a_class={bits} currents={} section={} drawn={} pending={} rest=exact body_sha={} elapsed_ms={}",
        heard.learned,
        heard.read,
        heard.deposits,
        heard.cells,
        body.currents().len(),
        body.section(),
        body.drawn(),
        pending.join(","),
        sha256(&read)?,
        started.elapsed().as_millis()
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonics::hnn::tower::{ContactLaw, Tower, TowerDeclaration};

    /// The commands chain through files on a tiny participating tower: a founded body hears a
    /// passage, asks two prompts and hears an answer, each body written create-new and read back by
    /// its SHA-256, the asks' releases and participation beside the body.
    #[test]
    fn the_body_commands_rest_between_every_operation() {
        let dir = std::env::temp_dir().join(format!("holonics-tower-body-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("dir");
        let at = |name: &str| dir.join(name).to_string_lossy().into_owned();
        let pinned = |name: &str| sha256(&std::fs::read(dir.join(name)).expect("read")).expect("sha");
        let put = |name: &str, bytes: &[u8]| {
            std::fs::write(dir.join(name), bytes).expect("write");
            (at(name), sha256(bytes).expect("sha"))
        };
        let classes = |v: &[usize]| -> Vec<u8> { v.iter().flat_map(|&c| (c as u16).to_be_bytes()).collect() };
        let run = |command: fn(&[String]) -> Result<()>, args: &[&str]| command(&args.iter().map(|s| s.to_string()).collect::<Vec<_>>()).expect("ran");
        let key: Vec<u8> = (0..4096u32).flat_map(|i| (i.wrapping_mul(2654435761) ^ i.wrapping_mul(i)).to_be_bytes()).collect();
        let declaration = TowerDeclaration { alphabet: 5, width: 4, modes: 4, contacts: 4, levels: 2, gated: true, turned: false, pumped: false, contact: ContactLaw::Rectifying };
        let mut tower = Tower::found(declaration, &key).expect("founded");
        let heads = tower.founded_participation(8).expect("declared");
        tower.join_participation(heads).expect("joined");
        let (state, state_sha) = put("STATE", TowerLearner::new(tower, 6).to_text().as_bytes());
        let passage: Vec<usize> = (0..60).map(|i| (i * i + i / 3) % 4).collect();
        let (passage, passage_sha) = put("PASSAGE", &classes(&passage));
        let (prompts, prompts_sha) = put("PROMPTS", &classes(&[1, 2, 3, 4, 2, 0, 4]));
        let (keys, keys_sha) = put("KEYS", &key);
        let (answered, answered_sha) = put("ANSWER", &classes(&[3, 1, 2, 0, 1]));
        run(found, &["found-tower-body", &state, &state_sha, "2", "8", &at("FOUND")]);
        run(hear, &["hear-tower-body", &at("FOUND"), &pinned("FOUND"), &passage, &passage_sha, &at("HEARD")]);
        run(ask, &["ask-tower-body", &at("HEARD"), &pinned("HEARD"), &prompts, &prompts_sha, &keys, &keys_sha, "6", "1", &at("ASKED")]);
        run(answer, &["answer-tower-body", &at("ASKED/BODY"), &pinned("ASKED/BODY"), &answered, &answered_sha, &at("ANSWERED")]);
        let rows = std::fs::read_to_string(dir.join("ASKED/RELEASES.tsv")).expect("releases");
        assert_eq!(rows.lines().count(), 3, "a row a prompt");
        assert!(std::fs::read_to_string(dir.join("ASKED/PARTICIPATION.tsv")).expect("participation").lines().count() > 1);
        let heard = TowerBody::from_text(&std::fs::read_to_string(dir.join("HEARD")).expect("heard")).expect("restored");
        let answered = TowerBody::from_text(&std::fs::read_to_string(dir.join("ANSWERED")).expect("answered")).expect("restored");
        assert!(answered.drawn() > 0 && answered.drawn() <= 12);
        assert_ne!(answered.learner.to_text(), heard.learner.to_text(), "the passage and the answer were learned");
        assert!(answered.currents().iter().chain([answered.conversation()]).all(|c| (1..=8).contains(&c.pending.len())));
        assert!(found(&["found-tower-body", &state, &state_sha, "2", "8", &at("FOUND")].map(String::from)).is_err(), "a body is written create-new");
        std::fs::remove_dir_all(&dir).expect("removed");
    }
}
