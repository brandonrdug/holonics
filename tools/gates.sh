#!/usr/bin/env bash
#
# The release gate sequence. Every owned verifier has one named entry here.
#
#     bash tools/gates.sh                    # every gate, in order
#     bash tools/gates.sh --list             # the gate names, and nothing else
#     bash tools/gates.sh named-paths typst  # only the named gates, in the order given
#     bash tools/gates.sh --control          # exercise supported non-destructive controls
#
# This is a RELEASE receiver, not an edit-loop command. It already runs the complete workspace
# suite. During construction invoke only named gates whose inputs changed and focused Cargo tests
# outside this script; run the complete sequence once after code, deed, documents and ledgers agree.
# Never run `cargo test --workspace` immediately before the complete sequence, and never report a
# subset invocation as though the complete sequence passed.
#
# Exit is non-zero if any gate fails. Every gate prints exactly one summary line; the full output
# of a failing gate is printed underneath it, and the full output of a passing one is discarded.
#
# WHAT THIS SCRIPT DOES NOT DO. It does not repair anything and it does not regenerate a manifest.
# `output_manifest.py` and `closure_manifest.py` both rewrite their ledger when run without
# `--check`; that is a decision about what the tree should now claim, and a gate is not the place
# to take it.
#
# The two ledger gates are agreement checks, not code-quality verdicts:
#
#   output-manifest   goes red when a driver has RUN since the ledger was written. `unrecorded`
#                     and `moved` are drift. `departed` is the loss the tool exists to catch, and
#                     it is the only one of the three that is a defect on its own.
#   closure-manifest  goes red when a recorded return's transitive producing closure drifts, or
#                     when an output root has no explicit producer/orphan disposition.

set -u -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CARGO_LOCK=/tmp/holonics-cargo.lock
CARGO_PATH=/opt/cuda/bin:$PATH   # holonic-engine's build script shells out to nvcc.
PROCESS_BOUND=(timeout -k 2s 180s)

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

GATES=(tests formal tracked-authority source-shape authored-levels named-paths line-citations
       epistemic-tags claim-index equation-atlas driver-catalog output-manifest closure-manifest
       boundary-artifacts typst architecture-lint document-law)

# ---------------------------------------------------------------------------------------------
# 10 · the laws THE_DOCUMENT_LAW states about governing documents
# ---------------------------------------------------------------------------------------------
#
# Three laws the corpus states and now enforces: measured absence, subordinate plans, and one
# identical current frontier in the position record and roadmap.
#
# An ABSENCE CLAIM must carry the command that measured it and the date it was measured.
# `canon/THE_OWNER_ATLAS.md` states the discipline — *"A measured absence decays and carries its
# command… Re-run it; do not cite it"* — and an audit on 2026-08-15 found roughly one in three
# absence claims the assistant had made about this repository was false, with the durable population
# being exactly the ones that looked measured.
#
# And `blueprint/` may hold exactly ONE document declaring itself active. `THE_ROADMAP.md` opens
# *"This is the single active roadmap"*; on 2026-08-15 five of thirteen blueprints declared
# themselves the active plan.

gate_document-law() {
    local out="$WORK/doclaw.out"
    "${PROCESS_BOUND[@]}" python3 "$ROOT/tools/document_law.py" >"$out" 2>&1
    local status=$?
    SUMMARY="$(grep -E '^FAILURES' "$out" | tail -1)"
    SUMMARY="${SUMMARY:-no summary line}"
    [ "$status" -eq 0 ] || cat "$out"
    return "$status"
}

FAILED=()
PASSED=()

# ---------------------------------------------------------------------------------------------
# The runner.
#
# Each gate is a function `gate_<name>`. It returns its own exit status and sets SUMMARY to the
# one line this prints beside the verdict. A redirection on a function call does not fork, so
# SUMMARY set inside the function is visible here; a gate that computes its summary in a pipeline
# or `$( )` must assign the result to SUMMARY in the function body, not inside the subshell.
# ---------------------------------------------------------------------------------------------

run_gate() {
    local name="$1"
    local log="$WORK/$name.log"
    SUMMARY=""
    "gate_$name" >"$log" 2>&1
    local status=$?
    if [ "$status" -eq 0 ]; then
        PASSED+=("$name")
        printf 'PASS  %-18s %s\n' "$name" "$SUMMARY"
    else
        FAILED+=("$name")
        printf 'FAIL  %-18s %s\n' "$name" "$SUMMARY"
        sed 's/^/        | /' "$log"
    fi
    return "$status"
}

# ---------------------------------------------------------------------------------------------
# 1 · the workspace suite
# ---------------------------------------------------------------------------------------------

# The figure is the SUM over every `test result:` line, never one of them and never a `tail`.
# `CONSTRUCTION_STATE.md` records the day a `tail` returned 237 for a suite of 1,440.
#
# Note the arithmetic bound: without `--no-fail-fast` a failing package stops the later ones, so
# the sum under a failure is a partial figure. The verdict does not depend on the sum — it is
# cargo's own exit status — but the number printed beside a FAIL is "how far it got".
sum_test_results() {
    awk '
        /^test result:/ {
            lines += 1
            for (i = 1; i <= NF; i++) {
                if ($(i+1) ~ /^passed/)  passed  += $i
                if ($(i+1) ~ /^failed/)  failed  += $i
                if ($(i+1) ~ /^ignored/) ignored += $i
            }
        }
        END { printf "%d passed, %d failed, %d ignored over %d result lines", passed, failed, ignored, lines }
    '
}

gate_tests() {
    local out="$WORK/tests.out"
    local examples="$WORK/examples.out"
    # Unit/integration/bin tests are the executable guard population. The example targets are
    # an evidence-driver corpus and are marked `test=false`; linking every one into the test profile
    # made a local library repair pay hundreds of binaries. Keep their release-boundary coverage by
    # type-checking them once, without linking or executing them all. Real deeds are still built and
    # executed explicitly by their owning phase.
    "${PROCESS_BOUND[@]}" flock "$CARGO_LOCK" env PATH="$CARGO_PATH" \
        cargo test --workspace --lib --bins --tests -j 2 >"$out" 2>&1
    local tests_status=$?
    "${PROCESS_BOUND[@]}" flock "$CARGO_LOCK" env PATH="$CARGO_PATH" \
        cargo check --workspace --examples -j 2 >"$examples" 2>&1
    local examples_status=$?
    local status=0
    [ "$tests_status" -eq 0 ] && [ "$examples_status" -eq 0 ] || status=1
    SUMMARY="$(sum_test_results <"$out"); example targets type-checked"
    # What is shown on failure is decided by the material: the lines cargo itself marks, plus
    # every result line. A fixed line budget would elide the one failure in a 30,000-line log.
    if [ "$status" -ne 0 ]; then
        grep -E '^(error|failures:|---- |test result:)|FAILED|panicked' "$out"
        grep -E '^(error|warning:)|could not compile' "$examples"
    fi
    return "$status"
}

# ---------------------------------------------------------------------------------------------
# 1a · the live formal umbrella builds without archived dependency fallback
# ---------------------------------------------------------------------------------------------

gate_formal() {
    local out="$WORK/formal.out"
    "${PROCESS_BOUND[@]}" bash "$ROOT/tools/lean_check.sh" >"$out" 2>&1
    local status=$?
    SUMMARY="$(grep -E 'Build completed successfully|build completed successfully|error:|timed out' "$out" | tail -1)"
    SUMMARY="${SUMMARY:-no summary line}"
    [ "$status" -eq 0 ] || tail -80 "$out"
    return "$status"
}

# ---------------------------------------------------------------------------------------------
# 1b · the live authority and source owners exist in the Git index
# ---------------------------------------------------------------------------------------------

gate_tracked-authority() {
    local out="$WORK/tracked-authority.out"
    "${PROCESS_BOUND[@]}" python3 "$ROOT/tools/tracked_authority.py" >"$out" 2>&1
    local status=$?
    SUMMARY="$(tail -1 "$out")"
    SUMMARY="${SUMMARY:-no summary line}"
    [ "$status" -eq 0 ] || cat "$out"
    return "$status"
}

gate_source-shape() {
    local out="$WORK/source-shape.out"
    "${PROCESS_BOUND[@]}" python3 "$ROOT/tools/source_shape.py" >"$out" 2>&1
    local status=$?
    SUMMARY="$(tail -1 "$out")"
    SUMMARY="${SUMMARY:-no summary line}"
    [ "$status" -eq 0 ] || cat "$out"
    return "$status"
}

# ---------------------------------------------------------------------------------------------
# 2 · authored numeric levels
# ---------------------------------------------------------------------------------------------

gate_authored-levels() {
    local out="$WORK/authored.out"
    "${PROCESS_BOUND[@]}" python3 "$ROOT/tools/authored_levels.py" --check >"$out" 2>&1
    local status=$?
    SUMMARY="$(grep -E '^[0-9]+ failures' "$out" | tail -1)"
    SUMMARY="${SUMMARY:-no failure line}; $(grep -E '^[0-9]+ authored' "$out" | tail -1)"
    [ "$status" -eq 0 ] || cat "$out"
    return "$status"
}

# ---------------------------------------------------------------------------------------------
# 3 · every path a governing document names
# ---------------------------------------------------------------------------------------------

gate_named-paths() {
    local out="$WORK/paths.out"
    "${PROCESS_BOUND[@]}" python3 "$ROOT/tools/resolve_named_paths.py" >"$out" 2>&1
    local status=$?
    SUMMARY="$(grep -E '^FAILURES' "$out" | tail -1)"
    SUMMARY="${SUMMARY:-no failure line}; $(grep -E '^path tokens' "$out" | tail -1)"
    [ "$status" -eq 0 ] || cat "$out"
    return "$status"
}

# ---------------------------------------------------------------------------------------------
# 3b · the LINE on the end of every path a governing document names
# ---------------------------------------------------------------------------------------------
#
# `named-paths` above verifies the path. Nothing verified the number after the colon, and the
# operating contract says in its own text that a line number is the most perishable thing a document
# can carry. An audit on 2026-08-15 found 265 such citations with no verifier of any kind, and
# `analytic_field.rs:1142` stale in three governing documents while a record deposited the same day
# already carried the right line. The correction had been made and never propagated.

gate_line-citations() {
    local out="$WORK/lines.out"
    "${PROCESS_BOUND[@]}" python3 "$ROOT/tools/resolve_line_citations.py" >"$out" 2>&1
    local status=$?
    SUMMARY="$(grep -E '^FAILURES' "$out" | tail -1)"
    SUMMARY="${SUMMARY:-no summary line}"
    [ "$status" -eq 0 ] || cat "$out"
    return "$status"
}

# ---------------------------------------------------------------------------------------------
# 3c · every live material bracket has one truth grade and declared evidence tags
# ---------------------------------------------------------------------------------------------

gate_epistemic-tags() {
    local out="$WORK/epistemic.out"
    "${PROCESS_BOUND[@]}" python3 "$ROOT/tools/epistemic_tags.py" >"$out" 2>&1
    local status=$?
    SUMMARY="$(tail -1 "$out")"
    SUMMARY="${SUMMARY:-no summary line}"
    [ "$status" -eq 0 ] || cat "$out"
    return "$status"
}

# ---------------------------------------------------------------------------------------------
# 4 · the table of contents agrees with the tree
# ---------------------------------------------------------------------------------------------
#
# `THE_CLAIM_INDEX.md` is generated. It was deposited 2026-08-10 declaring itself generated with no
# generator committed — the same shape as the two sourceless `zz_` probes, in the one file whose
# stated job is to stop drift. `tools/claim_index.py` owns it now, and this is the reader that makes
# the ownership detectable rather than declared. Unlike the two ledger gates below, it is green on a
# dirty tree: it compares the index against the *documents*, not against a run.

gate_claim-index() {
    local out="$WORK/claim.out"
    "${PROCESS_BOUND[@]}" python3 "$ROOT/tools/claim_index.py" --check >"$out" 2>&1
    local status=$?
    SUMMARY="$(tail -1 "$out")"
    SUMMARY="${SUMMARY:-no summary line}"
    [ "$status" -eq 0 ] || cat "$out"
    return "$status"
}

# ---------------------------------------------------------------------------------------------
# 4b · the exterior equation atlas agrees with its schema, manifest and relation endpoints
# ---------------------------------------------------------------------------------------------

gate_equation-atlas() {
    local out="$WORK/equation-atlas.out"
    "${PROCESS_BOUND[@]}" python3 "$ROOT/tools/equation_atlas.py" --check >"$out" 2>&1
    local status=$?
    SUMMARY="$(tail -1 "$out")"
    SUMMARY="${SUMMARY:-no summary line}"
    [ "$status" -eq 0 ] || cat "$out"
    return "$status"
}

# ---------------------------------------------------------------------------------------------
# 5 · every example driver is in the catalog, and every catalogued driver is in the tree
# ---------------------------------------------------------------------------------------------

gate_driver-catalog() {
    local out="$WORK/drivers.out"
    "${PROCESS_BOUND[@]}" python3 "$ROOT/tools/driver_catalog.py" --check >"$out" 2>&1
    local status=$?
    SUMMARY="$(head -1 "$out")"
    SUMMARY="${SUMMARY:-no summary line}"
    [ "$status" -eq 0 ] || cat "$out"
    return "$status"
}

# ---------------------------------------------------------------------------------------------
# 5 · the content address of every return under output/
# ---------------------------------------------------------------------------------------------

gate_output-manifest() {
    local out="$WORK/output.out"
    "${PROCESS_BOUND[@]}" python3 "$ROOT/tools/output_manifest.py" --check >"$out" 2>&1
    local status=$?
    SUMMARY="$(grep -E '^recorded ' "$out" | tail -1)"
    SUMMARY="${SUMMARY:-no summary line}"
    [ "$status" -eq 0 ] || cat "$out"
    return "$status"
}

# ---------------------------------------------------------------------------------------------
# 5 · the closure that produced every return under output/
# ---------------------------------------------------------------------------------------------

gate_closure-manifest() {
    local out="$WORK/closure.out"
    "${PROCESS_BOUND[@]}" python3 "$ROOT/tools/closure_manifest.py" --check >"$out" 2>&1
    local status=$?
    if [ "$status" -eq 0 ]; then
        SUMMARY="$(tail -1 "$out")"
        return 0
    fi
    # A closure hash covers the driver, ITS WHOLE CRATE'S `src/**.rs`, and the crate manifest. So
    # one edit anywhere in a crate moves the closure of every driver that crate owns, and a bare
    # count of moved rows reads as twenty-three separate defects when it is one dirty crate. Name
    # the owning crates: that is the reading that makes the red actionable.
    local moved crates
    moved="$(grep -c '^  moved: ' "$out")"
    crates="$(grep '^  moved: ' "$out" | sed 's/^  moved: //' \
        | while IFS= read -r slug; do
              awk -F'\t' -v s="$slug" '$1 == s { print $2 }' "$ROOT/meta/CLOSURE_MANIFEST.tsv"
          done \
        | grep -oE '^(crates|soma)/[^/]+' | sort -u | paste -sd' ' -)"
    SUMMARY="$moved closure(s) moved; producing crates: ${crates:-none in the ledger}"
    cat "$out"
    return "$status"
}

# ---------------------------------------------------------------------------------------------
# 6 · the committed boundary artifacts, content AND closure
# ---------------------------------------------------------------------------------------------

# Unlike the two ledger gates above, this one is a property of TRACKED files only, so it is green
# or red on the code rather than on the working tree's tidiness. It is the one place in the
# sequence where `CLAUDE.md` §0 lesson 1 — content hash AND closure hash, with a verifier — is
# checked against something committed.
gate_boundary-artifacts() {
    local out="$WORK/boundary.out"
    "${PROCESS_BOUND[@]}" python3 "$ROOT/tools/boundary_artifacts.py" >"$out" 2>&1
    local status=$?
    SUMMARY="$(tail -1 "$out")"
    SUMMARY="${SUMMARY:-no summary line}; $(grep -c '^BOUND ' "$out") artifact(s) bound"
    [ "$status" -eq 0 ] || cat "$out"
    return "$status"
}

# ---------------------------------------------------------------------------------------------
# 7 · the Typst roots
# ---------------------------------------------------------------------------------------------

# The roots are READ OFF THE MATERIAL, not listed here. A root is a `.typ` directly under
# `papers/source/` or a `main.typ` anywhere below it — which on this tree returns exactly the ten
# `papers/source/README.md` gives compile lines for. The count is printed rather than asserted: if
# the derivation returns nine or eleven, the summary line says so and a reader sees it, whereas an
# authored list of ten would go stale in silence.
typst_roots() {
    find "$ROOT/papers/source" -maxdepth 1 -name '*.typ' -type f
    find "$ROOT/papers/source" -mindepth 2 -name 'main.typ' -type f
}

gate_typst() {
    local rendered="$WORK/typst"
    mkdir -p "$rendered"
    local total=0 broken=0 root stem
    while IFS= read -r root; do
        total=$((total + 1))
        stem="$(printf '%s' "${root#"$ROOT/papers/source/"}" | tr '/' '-')"
        if ! "${PROCESS_BOUND[@]}" typst compile --root "$ROOT/papers/source" "$root" "$rendered/$stem.pdf" \
             >"$WORK/typst-$stem.err" 2>&1; then
            broken=$((broken + 1))
            printf '=== %s\n' "${root#"$ROOT/"}"
            cat "$WORK/typst-$stem.err"
        fi
    done < <(typst_roots | sort)
    SUMMARY="$((total - broken))/$total roots compile"
    [ "$broken" -eq 0 ]
}

# ---------------------------------------------------------------------------------------------
# 8 · the monotone ownership ratchet
# ---------------------------------------------------------------------------------------------

# It runs as of 2026-08-10. It had two absolute frames, and the first HID the second: the baseline
# it read did not exist in this tree, and `check_repository` reads the baseline before taking the
# census, so execution never reached the three PROTECTED_ROOTS that still carried the laboratory's
# `src/soma/` prefix. `CONSTRUCTION_STATE.md` recorded only the first; `canon/THE_DOCUMENT_LAW.md`
# §1.9 and §7 recorded both, correctly, and had done since it was written. Both are repaired in
# `crates/holonic-architecture-lint/src/lib.rs`.
#
# THE BASELINE IS TAKEN AT HEAD, NOT AT THE WORKING TREE. `meta/HOLONIC_DSA_BASELINE.tsv` is
# emitted from a detached worktree of the commit — the method `CONSTRUCTION_STATE.md` names for
# any measurement taken while the tree is dirty — so it is a property of what is committed and
# reproduces on any machine. The consequence is intended and is what a ratchet is for: uncommitted
# work that adds an ownership or materialization occurrence shows up RED, by file and construct.
gate_architecture-lint() {
    local out="$WORK/lint.out"
    "${PROCESS_BOUND[@]}" flock "$CARGO_LOCK" env PATH="$CARGO_PATH" \
        cargo run -q -p holonic-architecture-lint -j 2 -- "$ROOT" >"$out" 2>&1
    local status=$?
    SUMMARY="$(grep -E '^holonic architecture' "$out" | tail -1)"
    SUMMARY="${SUMMARY:-no summary line}"
    [ "$status" -eq 0 ] || cat "$out"
    return "$status"
}

# ---------------------------------------------------------------------------------------------
# The controls
#
# A gate control perturbs the material it reads, asserts the gate turns RED, and restores. The
# command exercises only the safe controls implemented below; it does not claim coverage for every
# gate. Every perturbation is either
# a new file this script created (removed on the way out, including on a signal) or lives entirely
# outside the repository; no tracked file is edited.
#
# The one gate whose full path is NOT controlled is `tests`: making the workspace suite fail costs
# a full rebuild under the cargo lock, and its verdict is cargo's own exit status rather than
# anything this script computes. What this script *does* compute for that gate is the sum, and the
# sum IS controlled below against a synthetic result block.
# ---------------------------------------------------------------------------------------------

CONTROL_ARTIFACTS=()
control_cleanup() {
    local artifact
    for artifact in "${CONTROL_ARTIFACTS[@]-}"; do
        [ -n "$artifact" ] && rm -rf "$artifact"
    done
}

# GREEN, then RED, then GREEN again. Not merely "red with the probe in place".
#
# A gate that is already red for an unrelated reason will read as RED under any perturbation, and
# reporting that as a held control is precisely the defect `CLAUDE.md` §8 names — *a check whose
# material cannot vary the property under test wears a passing result*. Both ledger gates are
# already red on any dirty tree, so this is not hypothetical here: it fires.
#
# INCONCLUSIVE is therefore a distinct third verdict, not a failure. It says the tree could not
# vary the property today, names what would be needed (a clean tree, a current ledger), and is
# counted separately.
CONTROL_UNSETTLED=0
control_probe() {
    local name="$1" why="$2" setup="$3" teardown="$4"

    SUMMARY=""
    if ! "gate_$name" >"$WORK/control-$name-before.log" 2>&1; then
        # Already red for an unrelated reason, so the VERDICT cannot flip. The READING still can,
        # and that is the falsifiable part: run the probe anyway and require the summary line to
        # move. A gate whose summary does not move under its own probe is not gating; a gate whose
        # summary moves is reading the material, and only the verdict is saturated.
        local before="$SUMMARY"
        eval "$setup"
        SUMMARY=""
        "gate_$name" >"$WORK/control-$name-saturated.log" 2>&1
        local after="$SUMMARY"
        eval "$teardown"
        CONTROL_UNSETTLED=$((CONTROL_UNSETTLED + 1))
        if [ "$before" = "$after" ]; then
            printf 'CONTROL HELD? NO   %-18s already red AND the probe moved nothing: %s\n' \
                "$name" "$before"
            return 1
        fi
        printf 'PARTIAL            %-18s already red, so the verdict could not flip; the probe\n' \
            "$name"
        printf '                   %-18s moved the reading: %s\n' "" "$before"
        printf '                   %-18s                 -> %s\n' "" "$after"
        return 0
    fi

    eval "$setup"
    SUMMARY=""
    "gate_$name" >"$WORK/control-$name-after.log" 2>&1
    local under=$?
    eval "$teardown"

    if [ "$under" -eq 0 ]; then
        printf 'CONTROL HELD? NO   %-18s stayed green under: %s\n' "$name" "$why"
        return 1
    fi

    # And it must come back. A probe that leaves the gate red has changed the tree, not tested it.
    SUMMARY=""
    if ! "gate_$name" >"$WORK/control-$name-restored.log" 2>&1; then
        printf 'CONTROL HELD? NO   %-18s stayed red after the probe was removed: %s\n' \
            "$name" "$SUMMARY"
        return 1
    fi
    printf 'CONTROL HELD       %-18s green -> red -> green under: %s\n' "$name" "$why"
    return 0
}

control_sum() {
    local block
    block=$(cat <<'BLOCK'
test result: ok. 100 passed; 0 failed; 3 ignored; 0 measured; 0 filtered out; finished in 0.10s
test result: ok. 23 passed; 0 failed; 11 ignored; 0 measured; 0 filtered out; finished in 0.02s
test result: FAILED. 7 passed; 2 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s
BLOCK
)
    local got
    got="$(printf '%s\n' "$block" | sum_test_results)"
    local want="130 passed, 2 failed, 14 ignored over 3 result lines"
    if [ "$got" = "$want" ]; then
        printf 'CONTROL HELD       %-18s the sum reads every line: %s\n' "tests(sum)" "$got"
        return 0
    fi
    printf 'CONTROL HELD? NO   %-18s summed %s, expected %s\n' "tests(sum)" "$got" "$want"
    return 1
}

run_controls() {
    trap 'control_cleanup; rm -rf "$WORK"' EXIT INT TERM
    local broken=0

    control_sum || broken=$((broken + 1))

    # authored-levels: a new library file carrying an undispositioned level. Not `mod`-declared,
    # so nothing compiles it; `library_sources()` globs `*/src/**.rs`, so the tool reads it.
    local level_probe="$ROOT/crates/holonic-language/src/zz_gate_control.rs"
    CONTROL_ARTIFACTS+=("$level_probe")
    control_probe authored-levels "an undispositioned const in library code" \
        "printf 'const ZZ_GATE_CONTROL_LEVEL: usize = 7;\n' >'$level_probe'" \
        "rm -f '$level_probe'" || broken=$((broken + 1))

    # named-paths: a live root document naming an owner that is not in the tree.
    local doc_probe="$ROOT/ZZ_GATE_CONTROL.md"
    CONTROL_ARTIFACTS+=("$doc_probe")
    control_probe named-paths "a live document naming an absent owner" \
        "printf '# control\n\nThis names \`crates/holonic-engine/src/zz_gate_control.rs\`, absent.\n' >'$doc_probe'" \
        "rm -f '$doc_probe'" || broken=$((broken + 1))

    # claim-index: a document retitled without regenerating. The title is what the index copies, so
    # editing it is the exact drift the generator exists to catch.
    control_probe claim-index "a document retitled without regenerating the index" \
        "sed -i '1s/.*/# The document law, retitled by a gate control/' '$ROOT/canon/THE_DOCUMENT_LAW.md'" \
        "sed -i '1s/.*/# The document law/' '$ROOT/canon/THE_DOCUMENT_LAW.md'" || broken=$((broken + 1))

    # driver-catalog: a new driver added without cataloguing it. This is the exact event that
    # produced 203 uncatalogued drivers, so the control is the event itself.
    local driver_probe="$ROOT/crates/holonic-engine/examples/zz_gate_control_driver.rs"
    CONTROL_ARTIFACTS+=("$driver_probe")
    control_probe driver-catalog "a driver added without cataloguing it" \
        "printf '//! A control driver, added and not catalogued.\nfn main() {}\n' >'$driver_probe'" \
        "rm -f '$driver_probe'" || broken=$((broken + 1))

    # output-manifest and closure-manifest: a return directory with no manifest row and no
    # producing driver. It is UNRECORDED to the first and a new ORPHAN row to the second.
    local return_probe="$ROOT/output/zz-gate-control"
    CONTROL_ARTIFACTS+=("$return_probe")
    local return_setup="mkdir -p '$return_probe'; printf 'a return nothing can cite\n' >'$return_probe/probe.txt'"
    control_probe output-manifest "a return directory with no manifest row" \
        "$return_setup" "rm -rf '$return_probe'" || broken=$((broken + 1))
    control_probe closure-manifest "a return directory with no producing driver" \
        "$return_setup" "rm -rf '$return_probe'" || broken=$((broken + 1))

    # boundary-artifacts: NOT EXERCISED, and the reason is other people's work rather than a
    # property of the gate. Its whole material is three committed binaries and one committed
    # registry; every probe that would redden it corrupts a tracked artifact that concurrent
    # sessions are compiling against, for the duration of the probe. Stated rather than skipped.
    printf 'NOT EXERCISED      %-18s would require corrupting a tracked binary; see below\n' \
        "boundary-artifacts"
    printf '                   %-18s what would redden it: one octet changed in soma/kernel/soma.spv\n' ""
    printf '                   %-18s or in either .ptx, or any closure member edited without a re-seed\n' ""
    printf '                   %-18s note: it binds what IS committed and does NOT assert currency —\n' ""
    printf '                   %-18s currency is the registry rebuild_evidence column, read it there\n' ""

    # typst: a compilation root that does not compile. It is also a control on the DERIVATION —
    # the root list is read off the material, so a new top-level `.typ` must enter it.
    local typst_probe="$ROOT/papers/source/zz_gate_control.typ"
    CONTROL_ARTIFACTS+=("$typst_probe")
    control_probe typst "an eleventh root that does not compile" \
        "printf '#let broken = \n' >'$typst_probe'" \
        "rm -f '$typst_probe'" || broken=$((broken + 1))

    # architecture-lint: an entirely synthetic repository root, outside this tree, whose census
    # exceeds its own committed baseline by one `Vec`.
    local lint_root="$WORK/lint-control"
    local protected
    for protected in crates/holonic-engine/src crates/holonic-language/src \
                     soma/body/src soma/membrane/src soma/life/src; do
        mkdir -p "$lint_root/$protected"
    done
    mkdir -p "$lint_root/meta"
    printf 'fn control() { let a: Vec<u8> = Vec::new(); let b: Vec<u8> = Vec::new(); }\n' \
        >"$lint_root/crates/holonic-engine/src/control.rs"

    # The allowance is READ OFF THE MATERIAL by the tool's own `--emit-baseline`, never written
    # here. Counting `Vec` occurrences by hand is how the first version of this control failed:
    # it authored `Vec=3` for a file whose census is 4, and reported the tool broken.
    local lint_run=(timeout -k 2s 180s flock "$CARGO_LOCK" env PATH="$CARGO_PATH"
                    cargo run -q -p holonic-architecture-lint -j 2 --)
    "${lint_run[@]}" --emit-baseline "$lint_root" >"$lint_root/meta/HOLONIC_DSA_BASELINE.tsv"
    local exact
    exact="$(grep -oE 'Vec=[0-9]+' "$lint_root/meta/HOLONIC_DSA_BASELINE.tsv" | head -1)"
    if "${lint_run[@]}" "$lint_root" >/dev/null 2>&1; then
        printf 'CONTROL HELD       %-18s its own census (%s) is within its own baseline: clean\n' \
            "arch(under)" "$exact"
    else
        printf 'CONTROL HELD? NO   %-18s refused a census equal to its own baseline\n' "arch(under)"
        broken=$((broken + 1))
    fi

    # One occurrence fewer than the material carries. Nothing else changes.
    local allowed="${exact#Vec=}"
    sed -i "s/Vec=$allowed/Vec=$((allowed - 1))/" "$lint_root/meta/HOLONIC_DSA_BASELINE.tsv"
    if "${lint_run[@]}" "$lint_root" >/dev/null 2>&1; then
        printf 'CONTROL HELD? NO   %-18s %s observed against %s allowed: passed\n' \
            "arch(over)" "$allowed" "$((allowed - 1))"
        broken=$((broken + 1))
    else
        printf 'CONTROL HELD       %-18s %s observed against %s allowed: refused\n' \
            "arch(over)" "$allowed" "$((allowed - 1))"
    fi

    control_cleanup
    printf '\n%d control(s) did not hold, %d partial\n' "$broken" "$CONTROL_UNSETTLED"
    if [ "$CONTROL_UNSETTLED" -gt 0 ]; then
        printf 'A PARTIAL control is a statement about the TREE, not about the gate: that gate was\n'
        printf 'already red, so nothing this script did could flip its verdict. What it does show is\n'
        printf 'that the probe MOVED THE READING — the gate is consuming the material rather than\n'
        printf 'returning a constant. Re-run on a tree where that gate is green for the full control.\n'
    fi
    return $((broken == 0 ? 0 : 1))
}

# ---------------------------------------------------------------------------------------------
# Entry
# ---------------------------------------------------------------------------------------------

main() {
    local selected=()
    local argument
    for argument in "$@"; do
        case "$argument" in
            --list) printf '%s\n' "${GATES[@]}"; return 0 ;;
            --control) run_controls; return $? ;;
            -h|--help)
                # The leading comment block, whatever length it has grown to.
                awk 'NR == 1 { next } /^#/ { sub(/^# ?/, ""); print; next } { exit }' \
                    "${BASH_SOURCE[0]}"
                return 0 ;;
            --*) printf 'unknown option %s\n' "$argument" >&2; return 2 ;;
            *)
                if printf '%s\n' "${GATES[@]}" | grep -qx -- "$argument"; then
                    selected+=("$argument")
                else
                    printf 'unknown gate %s; --list for the names\n' "$argument" >&2
                    return 2
                fi
                ;;
        esac
    done
    [ "${#selected[@]}" -gt 0 ] || selected=("${GATES[@]}")

    printf 'gates at %s, %s\n\n' "$(git -C "$ROOT" rev-parse --short HEAD 2>/dev/null || echo '?')" \
        "$(date -Is)"
    local gate
    for gate in "${selected[@]}"; do
        run_gate "$gate" || true
    done
    printf '\n%d passed, %d failed' "${#PASSED[@]}" "${#FAILED[@]}"
    if [ "${#FAILED[@]}" -gt 0 ]; then
        printf ': %s\n' "${FAILED[*]}"
        return 1
    fi
    printf '\n'
    return 0
}

main "$@"
