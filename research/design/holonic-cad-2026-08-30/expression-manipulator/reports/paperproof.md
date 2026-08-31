# Paperproof: data types and machinery conventions

Source: `https://github.com/Paper-Proof/paperproof`, HEAD `69401f7d9348699e1532194734b5dda0771278b7` ("lean - switch to module system"), cloned to `$S/refs/paperproof`. Lean toolchain `leanprover/lean4:v4.27.0` (library) / `v4.29.0-rc8` (examples). All paths below are relative to the clone root.

## 1. Identity and purpose

Paperproof is a VS Code extension plus a Lean 4 library that renders a tactic proof as a nested-box "history of hypotheses and goals" diagram, in the spirit of Gentzen trees, semantic tableaux, and natural deduction. The Lean side (`lean/`) walks the elaborator's `InfoTree`, diffs metavariable contexts before/after each user-written tactic, and emits a flat list of `ProofStep` records over an RPC method; the TypeScript side (`app/`) rebuilds boxes, arrows, and tables from that list purely by diffing goal and hypothesis identities. It refreshes on every cursor move, is read-only, and models only `by`-block tactic proofs.

## 2. Core data types

### 2.1 Lean-side extraction types (`lean/Services/BetterParser.lean`)

```lean
public structure Hypothesis where
  username : String
  type : String
  value : Option String
  -- unique identifier for the hypothesis, fvarId
  id : String
  isProof : String            -- "proof" | "universe" | "data"
  deriving Inhabited, ToJson, FromJson

public structure GoalInfo where
  username : String
  type : String
  hyps : List Hypothesis
  -- unique identifier for the goal, mvarId
  id : MVarId
  deriving Inhabited, ToJson, FromJson

public instance : BEq GoalInfo where beq g1 g2 := g1.id == g2.id
public instance : Hashable GoalInfo where hash g := hash g.id

public structure ProofStepPosition where
  start: Lsp.Position
  stop: Lsp.Position

public structure ProofStep where
  tacticString    : String
  goalBefore      : GoalInfo
  goalsAfter      : List GoalInfo
  tacticDependsOn : List String        -- fvarId strings
  spawnedGoals    : List GoalInfo      -- orphan mvars (have/by/calc bodies)
  position        : ProofStepPosition
  theorems        : List TheoremSignature

public structure Result where
  steps : List ProofStep
  allGoals : Std.HashSet GoalInfo
```

Goal and hypothesis equality is by id only (`BEq GoalInfo`). `TheoremSignature` lives in `lean/Services/GetTheorems.lean`: `name, instanceArgs, implicitArgs, explicitArgs : List ArgumentInfo`, `type, declarationType : String`, `body : Option String`; `ArgumentInfo = {name, type : String}`.

The RPC envelope (`lean/Paperproof.lean`):

```lean
meta def VERSION := 4
public meta inductive Mode where | single_tactic | tree
public meta structure InputParams where pos : Lsp.Position; mode: Mode
public meta structure OutputParams where steps : List Paperproof.Services.ProofStep; version: Nat
@[server_rpc_method]
public meta def getSnapshotData (params : InputParams) : RequestM (RequestTask OutputParams)
```

### 2.2 Emitted JSON schema (TS mirror, `app/types/LeanProofTree.ts`)

This is the wire format, verbatim:

```ts
export type LeanHypothesis = { value: null | string; username: string; type: string; id: string; isProof: string; };
export type LeanGoal = { username: string; type: string; id: string; hyps: LeanHypothesis[]; };
export type LeanTactic = {
  tacticString: string;
  tacticDependsOn: string[];
  goalBefore: LeanGoal;
  goalsAfter: LeanGoal[];
  spawnedGoals: LeanGoal[];
  position: PositionStartStop;      // {start:{line,character}, stop:{line,character}}
  theorems: AnyTheoremSignature[];
};
export type LeanProofTree = LeanTactic[];
```

The extension wraps it as `ValidProofResponse = { version?: number; proofTree: LeanProofTree; goal: LeanInteractiveGoal | null; theorems? }` (`app/types/index.ts`), where `goal` is `goals[0]` from Lean's own `Lean.Widget.getInteractiveGoals` (`app/types/LeanInteractiveGoal.ts`: `{ mvarId: string; userName; goalPrefix; hyps: {fvarIds: string[]; names: string[]; type}[] }`). The TS side reads `LeanGoal.id` as a plain string and compares it directly with `LeanInteractiveGoal.mvarId`, so the `MVarId` serializes to its `_uniq.N` name.

### 2.3 TS render model (`app/types/ConvertedProofTree.ts`)

```ts
export interface GoalNode { text: string; name: string; id: string; }
export interface HypNode  { text: string | null; name: string | null; id: string; isProof: string; }
export interface HypLayer { tacticId: string, hypNodes: HypNode[] }
export interface Box {
  id: string;
  parentId: string | null | "haveBox" | "byBox";
  goalNodes: GoalNode[];     // [inserted in converter.ts]
  hypLayers: HypLayer[];     // [inserted in converter.ts]
  hypTables: Table[];        // derived, [inserted in hypsToTables.ts]
}
export interface Tactic {
  id: string;
  text: string;
  dependsOnIds: string[];
  goalArrows: { fromId: string; toId: string }[];
  hypArrows: { fromId: string | null; toIds: string[]; shardId: string }[];
  successGoalId?: string;
  haveBoxIds: string[];
  byBoxIds: string[];
  position: PositionStartStop;
  theorems: AnyTheoremSignature[];
}
export interface ConvertedProofTree { boxes: Box[]; tactics: Tactic[]; equivalentIds: { [key: string]: string[] }; }
```

Layout intermediates: `TabledHyp {type:"hypothesis"; hypNode; columnFrom; columnTo; row}`, `TabledTactic {type:"tactic"; tactic; columnFrom; columnTo; row; arrowFrom: string|null; shardId}`, `Table {tabledHyps; tabledTactics; currentRow; row1Hyps?}`. A second, hand-authorable schema, `NaturalProofTree` (`app/types/NaturalProofTree.ts`, zod form in `paperproof.xyz/src/services/proofSchema.ts`), is a box tree carrying only deltas: `NaturalBox {goal; newHyps: NaturalHyp[]; tactics: NaturalStep[]}`, `NaturalHyp {name; type; from?}`, `NaturalStep {tactic; dependsOn?; newHyps?; newGoal?; closed?: true; newSubgoals?: NaturalBox[]; haveBoxes?: NaturalBox[]}`.

## 3. Extraction pipeline

**Entry.** `getSnapshotData` calls `withWaitFindSnapAtPos params.pos fun snap => ...`, i.e. it blocks until the elaboration snapshot covering the cursor exists, then runs `checkIfUserIsStillTyping` (`lean/Services/CheckIfUserIsStillTyping.lean`), which throws `stillTyping` if the hover line precedes `snap.stx.getPos?` or if any `MessageSeverity.error` in `snap.msgLog` at or after the snapshot start is not `"unsolved goals"`. In `.tree` mode it runs `BetterParser_Tree fileMap snap.infoTree` inside `RequestM.runTermElabM snap`.

**Traversal.** `BetterParser_Tree` is a single post-order `infoTree.visitM (postNode := fun ctx info _ results => ...)`. Children's `Result`s are flattened (`steps` concatenated, `allGoals` unioned), then the node is inspected: `let .ofTacticInfo tInfo := info | return { steps, allGoals }` and `let .some tacticSubstring := getTacticSubstring tInfo | return ...`. `getTacticSubstring` (`lean/Services/GetTacticSubstring.lean`) is just `tInfo.stx.getSubstring?`; nodes with no source substring (macro-generated `rotate_right`, etc.) are skipped, which is how user-written tactics are distinguished from expansion noise.

**Goal diffing** (`getGoalsChange ctx tInfo`), the heart of the tool:

```lean
let goalMVars := tInfo.goalsBefore ++ tInfo.goalsAfter
let printCtx := {ctx with mctx := tInfo.mctxAfter}
let mut goalsBefore ← getUnassignedGoals goalMVars tInfo.mctxBefore
let mut goalsAfter ← getUnassignedGoals goalMVars tInfo.mctxAfter
let commonGoals := goalsBefore.filter fun g => goalsAfter.contains g
goalsBefore := goalsBefore.filter (!commonGoals.contains ·)
goalsAfter :=  goalsAfter.filter (!commonGoals.contains ·)
for goalBefore in goalsBefore do
  if let some goalDecl := tInfo.mctxBefore.findDecl? goalBefore then
    let assignedMVars ← ctx.runMetaM goalDecl.lctx (findMVarsAssigned goalBefore tInfo.mctxAfter)
    let tacticDependsOn ← ctx.runMetaM goalDecl.lctx (findHypsUsedByTactic goalBefore goalDecl tInfo.mctxAfter)
    result := (tacticDependsOn, ← printGoalInfo printCtx goalBefore,
               ← goalsAfter.filter assignedMVars.contains |>.mapM (printGoalInfo printCtx)) :: result
```

`getUnassignedGoals` keeps mvars that have a decl and are in neither `eAssignment` nor `dAssignment`. Removing `commonGoals` filters out `focus`/`·`/`case` nodes that assign nothing. Parent-child goal edges are recovered from assignment, not from `goalsAfter` order: `findMVarsAssigned` runs `Meta.collectMVars` on `mctxAfter.eAssignment.find? goalId`. Hypothesis usage is likewise semantic: `findHypsUsedByTactic` instantiates the assignment, `collectFVars`, and keeps those present in `goalDecl.lctx` (comment: "Instead of doing parsing of what user wrote (it wouldn't work for linarith etc)"). Printing always uses `mctxAfter` because a `have h := by calc ...` has type `?m.260` in `mctxBefore`.

**Orphans become `spawnedGoals`.** In `parseTacticBody`, `orphanedGoals := currentGoals.foldl Std.HashSet.erase (noInEdgeGoals allGoals steps) |>.toArray.insertionSort (nameNumLt ·.id.name ·.id.name)` — goals seen anywhere in the subtree that no step lists as `goalsAfter`/`spawnedGoals` and that are not the current edge's goals. These are the mvars for `have ... := by`, `(by positivity)`, and `calc` steps; they are sorted by `_uniq` number so calc steps come out in order. Steps whose `goalBefore` already appears in the subtree are dropped (`if steps.map (·.goalBefore) |>.elem goalBefore then none`), so the innermost user tactic wins over the enclosing `tacticSeq`.

**Hypothesis printing** (`printGoalInfo`): `decl.lctx |>.sanitizeNames.run' {options := {}}` for `✝` tombstones; skips `isAuxDecl || isImplementationDetail`; `id := hypDecl.fvarId.name.toString`; `isProof` from `mayBeProof` (`Meta.isProof` → `"proof"`, `type.isSort` → `"universe"`, else `"data"`).

**Syntax-level prettification** (`prettifySteps`): each `rwRule` inside `rw [a, b]` is its own `TacticInfo`; steps are rewritten to `rw [a]`, `rw [b]`, and the closing `]` node becomes `rw [rfl]`. `intro x y` yields one child `TacticInfo` per name and is merged into a single step.

**Hypothesis identity across tactics** is decided in TS (`app/src/services/converter.ts`, `drawNewHypothesisLayer`), by diffing `goalBefore.hyps` against each `goalAfter.hyps`: match by `id` (fvarId) first, then by `username` (guarded: `!hypsAfter.find((h) => h.id === hypBefore.id && h.id !== hypAfter.id)`, issue #10). Outcomes: same id, unchanged → nothing; same id but name/type changed → `weirdSituation` (mutate the drawn node in place, "let's trust Lean that the change is so miniscule"); same name, new id, same type → `addToEquivalentIds` (alias, no node); same name, new id, new type → new node plus arrow from the old id (this is `rw ... at h`). Unmatched hyps: appeared only → nodes with `fromId: null`; disappeared only → nothing ("indicated by opacities"); both → one branching arrow from `hypsBeforeThatDisappeared[0]` to every appeared hyp (this is `cases h with | inl hp`, `rcases h with ⟨a, b⟩`).

**Tactic shapes** (`handleTacticApp`), with `goalBefore` located via `getBoxByGoalId`:

- `have h : T := by ...`, `have h := calc ...`, `let`: `goalsAfter.length === 1 && goalsAfter[0].type === goalBefore.type` (CASE_1). The new goal id is aliased to the old (`addToEquivalentIds`), and every `spawnedGoals` entry becomes a `Box` with `parentId: "haveBox"`. Test `spawned` in `lean/Tests.lean` shows the shape: `goalsAfter: type 666 = 665 + 1, hyps: easy : 4 = 2 + 2`, `spawnedGoals: type 4 = 2 + 2`. The inner `rfl` step has `goalBefore` equal to the spawned goal, so it lands in the have-box.
- `apply T (by positivity)`: `goalsAfter.length >= 1 && spawnedGoals.length >= 1` with a changed goal (CASE_2) → `byBox`es.
- terminal `calc`: otherwise (CASE_3) `spawnedGoals` are appended to `goalsAfter` as siblings; `prettifyTacticText` collapses the text to `calc`.
- `cases`, `induction`, `rcases`, `constructor`, `apply Iff.intro`, `by_cases`: `goalsAfter.length > 1` → one new child `Box` per goal (`createNewBox(pretty, currentBox.id)`), a `goalArrows` entry from `goalBefore.id` to each, and a per-child `hypLayer` from the hyp diff. The child box label is `prettifyGoalUsername(goalNodes[0].name)` (`inl`, `succ`, `pos`), which strips the `._@` macro-scope suffix.
- `intro`, `rw`, `simp`, `apply` with a single new goal: same box, new `GoalNode` pushed if its text differs from the last one, hyp layer appended.
- closing tactics (`exact`, `rfl`, `linarith`, `sorry`): `goalsAfter.length === 0` → `successGoalId = goalBefore.id`. `sorry` is a normal closing step; the UI marks it by text (`tactic.text.includes('sorry')`).
- unsolved goals: no step has that goal as `goalBefore`; `getTacticByGoalId` returns `undefined`, and `TacticNode` renders the `...` ellipsis when it is the active goal.
- `first | a | b`: backtracking yields several steps with the same `goalBefore.id`; `filterBacktrackingSteps` keeps the last.

Before conversion, `removeParticularHypsFromTactic` drops `isProof === "universe"` hyps (Mathlib `variable` clutter). `drawInitialGoal` creates box `"1"` (`parentId: null`) with an `"init"` pseudo-tactic whose `hypArrows` come from `null`. `postprocess` rewrites every id through `getDisplayedId` and numbers `shardId`s.

**Single-tactic mode** uses `goalsAt?` (`lean/Services/GoalsAt.lean`, a copy of `InfoTree.goalsAt?` with an added `!isClosingBracketInRewriteSequence`), `shouldRenderSingleSequent` (cursor on whitespace or on `by` → one `"fake"` step), `prettifyRwTactic`, and `GetTheorems`, which samples `tree.hoverableInfoAtM?` every 3 bytes across the tactic range, collects `.ofTermInfo` constant heads, and pretty-prints each via `forallTelescope` with `binderInfo` classification.

**Offline path.** `lean/terminal.lean` (`lake exe terminal FILE CONST OUT.json`) runs `Frontend.processCommand` with `infoState.enabled := true` and runs `BetterParser_Tree` on the info trees of the command introducing `CONST`, writing `{steps, allGoals}`. `lean/Tests.lean` defines `#assert_parser in <command>` and golden-tests the textual dump via `#guard_msgs`.

## 4. Rendering conventions

**Colors** (`app/src/index.css`): hypotheses `background: #a4dabc; border: 2px solid rgb(152 214 179)`, hyp names `#d0005b`; with `isGreenHypotheses` off, `data` hyps are yellow `#f9e9b5`; goals `rgb(249, 195, 195)` / `rgb(246, 185, 185)`; tactics are transparent with a dashed SVG border and `#72787c` text; `-success` is cyan `rgb(0 213 255 / 12%)` with 🎉 flanking; `-sorried` is `#f2ded94f`; `-ellipsis` is bold `...`; arrows `#a0ceb0`; canvas `#FFFDF7` with `#EFE8D6` border; root header/footer `#F3F1E8` with uppercase JetBrains Mono titles `hypotheses` / `theorem`.

**Nesting.** Every non-root `Box` has a dashed border; depth is tracked by a CSS counter `.box { --level: 0; & .box { --level: 1; ...}}` to 8, and the case-name strip uses `color-mix(in srgb, rgba(132,147,171), white calc(80% - var(--level) * 7%))` so scopes darken with depth ("variable scopes are shown as darkening backgrounds", README). `BoxEl` (`app/src/components/ProofTree/components/BoxEl/index.tsx`) renders, top to bottom: root-only header with hoisted `row1Hyps`; `Hypotheses` tables; `.child-boxes` (boxes with `parentId === box.id`, flex row, `align-items: flex-end`); then `goalNodes.slice().reverse()`, each as `[byBoxes][TacticNode][GoalNode]`. Reversing the goals is the "read towards the middle" convention: hypotheses descend from the top, goals ascend from the bottom, and the tactic that closes the box sits where they meet. Have-boxes are rendered inside the hypothesis table above the `have` tactic cell (`TacticNodeForHypothesis.tsx`).

**Hypothesis layout** (`app/src/services/hypsToTables.ts`) is a grid, not a graph layout: rows alternate tactic/hyp (`currentRow += 2`); a child's column span is `getChildrenWidth` (leaf = 1, else sum over descendants reached through `hypArrows`), so a hyp sits directly above everything derived from it; a new `Table` starts at `"init"` or when `!doAnyLayersBelowHaveParentsAbove`; `arrowFrom` is set only when the parent is in another table or more than two rows up (`currentTable.currentRow - parentHyp.row > 2`), otherwise adjacency implies the edge. Childless `data` hyps are hoisted to `row1Hyps` in the header.

**Arrows.** Two families, both DOM-measured after layout (`createArrow.ts` divides by the current `transform` scale) and drawn with `perfect-arrows` (`PerfectArrow.tsx`): structural hyp→tactic arrows from `hypsToTables`, and `dependsOnIds` arrows from a hypothesis to the tactic node, drawn only for `isProof === "proof"` hyps (`DependsOnUI.shouldDrawArrowToHypothesis`) and only visible on hover or on the `-success` tactic (`.tactic .perfect-arrow { display: none } .tactic:hover ...`). Goal arrows are implicit in vertical stacking.

**Highlighting and cursor.** `getHighlights` maps the InfoView goal's `mvarId` and each `hyps[].fvarIds` through `equivalentIds` and applies `-highlighted`; the tactic whose `position` contains the cursor gets `-position-matches` (bold). `renderByBoxes` shows `byBox`es only when focused or sorried. `isBoxSorried` marks a box whose closing tactic contains `sorry` and whose children are not themselves sorried.

**Interaction.** Click a box → `zoomToBox` (CSS `transform: scale`, 300 ms rAF animation) and `localStorage.zoomedBoxId`; on each refresh `zoomOnNavigation` zooms to the lowest common ancestor of the box holding the current goal and the last clicked box. Right-click menu (`ContextMenu.tsx`): collapse/expand box (collapsed shows only `goalNodes[0]`), single-tactic mode, LaTeX mode (gpt-4o via a `paperproof.xyz` proxy), zoom, font size, compact modes, "Copy for LLM", snapshot (POSTs `.proof-tree` `outerHTML`). Have-box collapse toggles ⛶/▬. There is no click-to-jump to source: the only webview→extension messages are `from_webview:update_settings` and `from_webview:request_full_proof_tree`.

## 5. Machinery conventions

**Identity.** Hypotheses are keyed by fvarId string (`_uniq.N`), goals by mvarId; both are Lean's, never invented. Boxes and tactics get sequential string ids from module-level counters reset at each `converter()` call (`boxId = 1; tacticId = 1`), so the root is always `"1"` (special-cased in `BoxEl`, `getHeader`, `zoomOnNavigation`). `equivalentIds: { [displayedId]: inferiorId[] }` is a one-level alias table; `getDisplayedId` finds the representative, `addToEquivalentIds` extends the representative's list. DOM ids are `box-${id}`, `hypothesis-${id}`, `tactic-${id}` or `tactic-${id}-${shardId}` (one element per `hypArrows` shard). Theorem identity for UI state is the statement text: `useEffect(..., [converted?.statement])` clears `zoomedBoxId` and `collapsedBoxIds`.

**Update model.** No incremental update. `extension/src/extension.ts` listens to `onDidChangeTextEditorSelection`/`onDidChangeActiveTextEditor`, skips when the panel is closed ("Our parser is expensive"), cancels the previous `CancellationTokenSource`, and `sendPosition` posts `start_loading`, `update_position`, then `sendPosition` with the full body; stale responses are dropped by `token.isCancellationRequested`. `vscodeRequest` opens a new RPC session per call: `$/lean/rpc/connect {uri}` then `$/lean/rpc/call {sessionId, method, ...tdp, params}`, on a client borrowed from `leanprover.lean4`'s exports (`clientProvider.getActiveClient()`). Tree mode issues two calls, `Paperproof.getSnapshotData` and `Lean.Widget.getInteractiveGoals`. The webview rebuilds everything (`converter` + `hypsToTables`, "2ms to 5ms") and re-measures arrows in a `useLayoutEffect` keyed on `[converted, UIVersion]`.

**Caching.** None beyond Lean's own snapshot cache (`withWaitFindSnapAtPos`) and `retainContextWhenHidden` on the panel.

**Error handling.** Lean throws `RequestError ⟨.invalidParams, code⟩` with short codes `zeroProofSteps`, `noGoalsAfter`, `noParsedTree`, `stillTyping`, `couldntFindTacticSubstring`; the extension adds `leanExtensionNotFound`, `wrongLeanExtensionVersion: <html>`, `leanClientNotFound`, `leanNotYetRunning`; Lean's own `File changed.`, `no snapshot found at`, `No RPC method` pass through. `handleExtensionErrors.tsx` maps each to a snackbar or silence. Protocol compatibility is a single integer, `VERSION := 4` in Lean vs `desiredVersion = 4` in `indexBrowser.tsx`, checked before conversion.

**Position mapping.** One-directional. Lean records `ProofStepPosition` from `tacticSubstring.startPos/stopPos` via `FileMap.utf8PosToLspPos`; TS `isCursorWithinTactic` treats a tactic spanning more than one line as ending at `start.line + 1, char 0` because the last tactic's substring swallows trailing blank lines. Which goal is "current" comes from the InfoView RPC, not from positions.

## 6. Abstractions to lift for a Lean-based mathematics CAD

Transferable patterns:

1. **Assignment-driven edges, not syntax-driven.** Parent/child goal edges from `Meta.collectMVars` on `eAssignment`, and dependencies from `collectFVars` on the instantiated assignment. Works for `linarith`, `omega`, `simp` where syntax says nothing.
2. **Before/after mctx diff with `commonGoals` removal.** Identifies no-op structural tactics (`focus`, `·`, `case`) for free and collapses macro expansion to the innermost user tactic.
3. **Orphan detection = `allGoals − in-edges`.** Sub-proof entry points (`have`, `by`, `calc`) fall out of set difference on mvar ids, then sorted by `_uniq` number for creation order.
4. **User-written filter by `stx.getSubstring?`.** A cheap, robust separator between elaboration noise and authored steps.
5. **Print with the final mctx.** `printCtx := {ctx with mctx := tInfo.mctxAfter}` avoids `?m.260` leaks; a CAD should print at the latest known state, but keep the earlier state as data.
6. **Flat step list plus a separate structural converter.** Lean emits an order-preserving `List ProofStep`; all box/scope reconstruction happens in a 500-line pure function that runs in milliseconds and is unit-testable with golden JSON.
7. **Two-key matching with an alias table.** fvarId first, name second, `equivalentIds` for "same object, new id" (CASE_1 goals, `let`-rewritten hyps). A representative/inferior union table is exactly what a CAD needs for object identity across refactors.
8. **Explicit `spawnedGoals` vs `goalsAfter`.** Separating "goals I still owe" from "goals I opened as a side quest" is what makes have/by/calc nest instead of branch.
9. **`successGoalId` as a first-class closing event.** A box is closed by exactly one step; that step is where 🎉/sorry/ellipsis states attach.
10. **Pseudo-step `"init"`.** Treating the initial context as a tactic with `fromId: null` arrows unifies the initial hypotheses with all later layers.
11. **Semantic classification of hyps (`isProof`: proof/data/universe).** Cheap `Meta.isProof` / `isSort` calls drive filtering (drop universes), header hoisting (childless data), and arrow policy (only proof hyps get dependency arrows).
12. **Grid layout from a descendant-width recursion.** Provenance trees render as tables where a node's `columnTo − columnFrom` equals its subtree width; adjacency replaces arrows unless the parent is `> 2` rows away.
13. **Golden-test the extractor with a command elaborator.** `#assert_parser in` + `#guard_msgs` yields deterministic textual snapshots per theorem without an IDE.
14. **Delta-only human schema with an inverse.** `NaturalProofTree` carries only `newHyps`, `from`, `dependsOn`, `newGoal`, `closed`, and `naturalToConverted`/`copyAsNaturalProofTree` form a round trip; a CAD interchange format should likewise be delta-based and invertible.
15. **Backtracking filter by last-writer-wins on `goalBefore.id`.** Simple, and correct as long as steps are emitted in attempt order.

Not modeled (a lower-level tool must add):

1. **Term-mode proofs and term-level structure.** Only `.ofTacticInfo` nodes are read; `TermInfo` is used solely to harvest theorem names. `exact ⟨p, ppos, pp⟩` is one opaque step.
2. **Metavariable assignment history / delayed assignments.** Only `eAssignment` at `mctxBefore`/`mctxAfter` is compared; `dAssignment` is used just as a "solved" flag, and intermediate assignments inside a tactic are invisible.
3. **Elaboration order, unification, and instance resolution.** `synthInstance` traces, postponed problems, and the order in which subgoals were actually solved (vs listed) are dropped.
4. **Universe levels and implicit arguments in goals.** Everything is `ppExprWithInfos ... .fmt.pretty` strings; no `Expr`, no `Level`, no binder info survives except in `TheoremSignature`.
5. **Definitional unfolding / rewriting positions.** `rw` is reduced to per-rule steps with a whole-type string diff; which subterm changed, motive, and `at *` fan-out are not represented, and hypotheses that merely disappear are silently dropped ("indicated by opacities").
