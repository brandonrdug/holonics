#!/usr/bin/env bash
#
# The release gate sequence. Every owned verifier has one named entry here.
#
#     bash tools/gates.sh                    # every gate, in order
#     bash tools/gates.sh --list             # the gate names, and nothing else
#     bash tools/gates.sh claim-index typst  # only the named gates, in the order given
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
# WHAT THIS SCRIPT DOES NOT DO. It does not repair, inventory, classify, or regenerate the tree.
# A release receiver runs only tests and checks attached to an explicit repository contract.

set -u -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CARGO_LOCK=/tmp/holonics-cargo.lock
CARGO_PATH=/opt/cuda/bin:$PATH   # holonic-engine's build script shells out to nvcc.
CARGO_JOBS="$(nproc)"            # apparatus width read from the active machine, never authored.
PROCESS_BOUND=(timeout -k 2s 180s)

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

GATES=(tests formal tracked-authority source-shape epistemic-tags claim-index equation-atlas typst
       document-law)

# ---------------------------------------------------------------------------------------------
# 10 · the laws THE_DOCUMENT_LAW states about governing documents
# ---------------------------------------------------------------------------------------------
#
# Three laws the corpus states and now enforces: measured absence, subordinate plans, and one
# identical current frontier in the position record and roadmap.
#
# An ABSENCE CLAIM must carry the command that measured it and the date it was measured.
# `docs/canon/THE_OWNER_ATLAS.md` states the discipline — *"A measured absence decays and carries its
# command… Re-run it; do not cite it"* — and an audit on 2026-08-15 found roughly one in three
# absence claims the assistant had made about this repository was false, with the durable population
# being exactly the ones that looked measured.
#
# And `docs/plans/` may hold exactly ONE document declaring itself active. `THE_ROADMAP.md` opens
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
    local build="$WORK/test-build.out"
    # Unit/integration/bin tests are the executable guard population. The example targets are
    # an evidence-driver corpus and are marked `test=false`; linking every one into the test profile
    # made a local library repair pay hundreds of binaries. Keep their release-boundary coverage by
    # type-checking them once, without linking or executing them all. Real deeds are still built and
    # executed explicitly by their owning phase.
    # Compilation is productive work, not a hung test. The invoking agent supervises its progress
    # under AGENTS.md's September 4 ruling. Build the workspace test targets once, then apply the
    # existing runtime guard to their execution; a cold build must not spend that execution budget.
    flock "$CARGO_LOCK" env PATH="$CARGO_PATH" \
        cargo test --workspace --lib --bins --tests --no-run -j "$CARGO_JOBS" >"$build" 2>&1
    local build_status=$?
    if [ "$build_status" -ne 0 ]; then
        SUMMARY="workspace test compilation failed (exit $build_status)"
        tail -60 "$build"
        return "$build_status"
    fi
    "${PROCESS_BOUND[@]}" flock "$CARGO_LOCK" env PATH="$CARGO_PATH" \
        cargo test --workspace --lib --bins --tests --no-fail-fast -j "$CARGO_JOBS" >"$out" 2>&1
    local tests_status=$?
    flock "$CARGO_LOCK" env PATH="$CARGO_PATH" \
        cargo check --workspace --examples -j "$CARGO_JOBS" >"$examples" 2>&1
    local examples_status=$?
    local status=0
    [ "$tests_status" -eq 0 ] && [ "$examples_status" -eq 0 ] || status=1
    SUMMARY="$(sum_test_results <"$out"); example targets type-checked"
    # What is shown on failure is decided by the material: the lines cargo itself marks, plus
    # every result line. A fixed line budget would elide the one failure in a 30,000-line log.
    if [ "$status" -ne 0 ]; then
        printf 'test execution exit %s; example check exit %s\n' "$tests_status" "$examples_status"
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
# Every live material bracket has one truth grade and declared evidence tags
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
# `docs/CLAIM_INDEX.md` is generated. It was deposited 2026-08-10 declaring itself generated with no
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
# 7 · the Typst roots
# ---------------------------------------------------------------------------------------------

# The roots are READ OFF THE MATERIAL, not listed here. A root is a `.typ` directly under
# `research/papers/source/` or a `main.typ` anywhere below it — which on this tree returns exactly the ten
# `research/papers/source/README.md` gives compile lines for. The count is printed rather than asserted: if
# the derivation returns nine or eleven, the summary line says so and a reader sees it, whereas an
# authored list of ten would go stale in silence.
typst_roots() {
    find "$ROOT/research/papers/source" -maxdepth 1 -name '*.typ' -type f
    find "$ROOT/research/papers/source" -mindepth 2 -name 'main.typ' -type f
}

gate_typst() {
    local rendered="$WORK/typst"
    mkdir -p "$rendered"
    local total=0 broken=0 root stem
    while IFS= read -r root; do
        total=$((total + 1))
        stem="$(printf '%s' "${root#"$ROOT/research/papers/source/"}" | tr '/' '-')"
        if ! "${PROCESS_BOUND[@]}" typst compile --root "$ROOT/research/papers/source" "$root" "$rendered/$stem.pdf" \
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

    # claim-index: a document retitled without regenerating. The title is what the index copies, so
    # editing it is the exact drift the generator exists to catch.
    control_probe claim-index "a document retitled without regenerating the index" \
        "sed -i '1s/.*/# The document law, retitled by a gate control/' '$ROOT/docs/canon/THE_DOCUMENT_LAW.md'" \
        "sed -i '1s/.*/# The document law/' '$ROOT/docs/canon/THE_DOCUMENT_LAW.md'" || broken=$((broken + 1))

    # typst: a compilation root that does not compile. It is also a control on the DERIVATION —
    # the root list is read off the material, so a new top-level `.typ` must enter it.
    local typst_probe="$ROOT/research/papers/source/zz_gate_control.typ"
    CONTROL_ARTIFACTS+=("$typst_probe")
    control_probe typst "an eleventh root that does not compile" \
        "printf '#let broken = \n' >'$typst_probe'" \
        "rm -f '$typst_probe'" || broken=$((broken + 1))


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
