import Lean.Elab.Frontend
import Lean.LibrarySuggestions.SymbolFrequency
import Lean.Server.InfoUtils
import Mathlib.Tactic

/-!
# Derivation Atlas

This executable is an exterior Lean apparatus face.  Lean parses, elaborates and kernel-checks a
source occurrence; the executable exports the resulting typed expression graph, declaration
bodies, source-linked term occurrences, and before/after proof-state events.  A downstream tool may
derive algebraic, arithmetic, or geometric receiver views from this bundle, but no such view is
part of Lean's truth authority.

The exact graph is intentionally richer than a source parser and weaker than a semantic oracle:
syntax, names and elaborator labels are retained as exterior lineage, while `Expr`, `Environment`,
and `InfoTree` provide the typed return.  The bundle preserves occurrences before any analysis
quotient is applied.
-/

open Lean

namespace Holonics.DerivationAtlas

private structure ProcessedFile where
  snapshots : Language.SnapshotTree
  environment : Environment
  moduleName : String

private def processFile (fileName : String) : IO ProcessedFile := do
  let input ← IO.FS.readFile fileName
  let setupOutput ← IO.Process.output {
    cmd := "lake"
    args := #["setup-file", fileName]
  }
  unless setupOutput.exitCode == 0 do
    throw <| IO.userError s!"lake setup-file failed for {fileName}: {setupOutput.stderr}"
  let decoded : Except String ModuleSetup := Json.parse setupOutput.stdout >>= fromJson?
  let setupInfo ←
    match decoded with
    | .ok value => pure value
    | .error message => throw <| IO.userError s!"invalid lake setup for {fileName}: {message}"
  let inputCtx := Parser.mkInputContext input fileName
  let opts := Lean.internal.cmdlineSnapshots.setIfNotSet setupInfo.options.toOptions true
  let opts := Elab.async.set opts false
  let ctx : Language.ProcessingContext := { inputCtx with }
  let setup (stx : Elab.HeaderSyntax) :
      Language.ProcessingT IO
        (Except Language.Lean.HeaderProcessedSnapshot Language.Lean.SetupImportsResult) := do
    liftM <| setupInfo.dynlibs.forM Lean.loadDynlib
    return Except.ok {
      imports := setupInfo.imports?.getD stx.imports
      isModule := strictOr setupInfo.isModule stx.isModule
      mainModuleName := setupInfo.name
      package? := setupInfo.package?
      opts
      trustLevel := 0
      importArts := setupInfo.importArts
      plugins := setupInfo.plugins
    }
  let snap ← Language.Lean.process setup none ctx
  let snapshots := Language.toSnapshotTree snap
  let wait ← snapshots.waitAll
  let _ := wait.get
  let hasErrors ← snapshots.runAndReport opts false
  if hasErrors then
    throw <| IO.userError s!"elaboration failed for {fileName}"
  let some commandState := Language.Lean.waitForFinalCmdState? snap
    | throw <| IO.userError s!"no final environment returned for {fileName}"
  return {
    snapshots
    environment := commandState.env
    moduleName := setupInfo.name.toString
  }

structure ExpressionFace where
  renderedExterior : String
  leanStructuralHashExterior : String
  rootNode : Nat
  deriving Inhabited, ToJson

structure ExpressionNode where
  index : Nat
  kindExterior : String
  faceExterior : String
  children : Array Nat
  deriving Inhabited, ToJson

structure ExpressionUse where
  node : Nat
  parentNode : Option Nat
  childPosition : Option Nat
  count : Nat
  deriving Inhabited, ToJson

structure ExpressionInterner where
  byExpression : ExprMap Nat := {}
  nodes : Array ExpressionNode := #[]
  rootCounts : Array Nat := #[]
  deriving Inhabited

structure LocalStanding where
  index : Nat
  freeOccurrenceExterior : String
  userFaceExterior : String
  binderFaceExterior : String
  kindFaceExterior : String
  type : ExpressionFace
  value : Option ExpressionFace
  deriving ToJson

structure GoalFace where
  goalOccurrenceExterior : String
  userFaceExterior : String
  localStanding : Array LocalStanding
  target : ExpressionFace
  deriving ToJson

structure TermOccurrence where
  sequence : Nat
  parentDeclarationExterior : String
  startByte : Nat
  stopByte : Nat
  elaboratorExterior : String
  syntaxExterior : String
  expression : ExpressionFace
  expectedType : Option ExpressionFace
  deriving ToJson

structure ProofEvent where
  sequence : Nat
  parentDeclarationExterior : String
  startByte : Nat
  stopByte : Nat
  elaboratorExterior : String
  syntaxExterior : String
  before : Array GoalFace
  after : Array GoalFace
  deriving ToJson

structure DeclarationOperation where
  declarationExterior : String
  moduleExterior : String
  kindExterior : String
  type : ExpressionFace
  definingValue : Option ExpressionFace
  bodyReferencesExterior : Array String
  deriving ToJson

structure AtlasBundle where
  schema : String
  sourcePathExterior : String
  moduleExterior : String
  declarationModulePrefixExterior : String
  expressionNodes : Array ExpressionNode
  expressionUses : Array ExpressionUse
  declarationOperations : Array DeclarationOperation
  termOccurrences : Array TermOccurrence
  proofEvents : Array ProofEvent
  syntaxAndNamesAreExterior : Bool
  kernelChecked : Bool
  truthStatus : String
  deriving ToJson

private def binderFace : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict-implicit"
  | .instImplicit => "instance-implicit"

private def expressionChildren : Expr → Array Expr
  | .app function argument => #[function, argument]
  | .lam _ domain body _ => #[domain, body]
  | .forallE _ domain body _ => #[domain, body]
  | .letE _ type value body _ => #[type, value, body]
  | .mdata _ expression => #[expression]
  | .proj _ _ body => #[body]
  | _ => #[]

private def expressionKind : Expr → String
  | .bvar _ => "bound-variable"
  | .fvar _ => "free-variable"
  | .mvar _ => "metavariable"
  | .sort _ => "sort"
  | .const _ _ => "constant"
  | .app _ _ => "application"
  | .lam _ _ _ _ => "lambda"
  | .forallE _ _ _ _ => "forall"
  | .letE _ _ _ _ _ => "let"
  | .lit _ => "literal"
  | .mdata _ _ => "metadata"
  | .proj _ _ _ => "projection"

private def expressionFaceText : Expr → String
  | .bvar index => s!"{index}"
  | .fvar occurrence => occurrence.name.toString
  | .mvar occurrence => occurrence.name.toString
  | .sort level => reprStr level
  | .const name levels => s!"{name}|{reprStr levels}"
  | app@(.app _ _) =>
      let head := app.getAppFn
      match head with
      | .const name _ => name.toString
      | .fvar occurrence => occurrence.name.toString
      | _ => ""
  | .lam name _ _ binder => s!"{name}|{binderFace binder}"
  | .forallE name _ _ binder => s!"{name}|{binderFace binder}"
  | .letE name _ _ _ nondep => s!"{name}|{if nondep then "have" else "let"}"
  | .lit literal => reprStr literal
  | .mdata data _ => reprStr data
  | .proj typeName index _ => s!"{typeName}|{index}"

private partial def internExpressionNode (standing : IO.Ref ExpressionInterner)
    (expression : Expr) : IO Nat := do
  if let some index := (← standing.get).byExpression[expression]? then
    return index
  let children ← (expressionChildren expression).mapM (internExpressionNode standing)
  let held ← standing.get
  if let some index := held.byExpression[expression]? then
    return index
  let index := held.nodes.size
  let node := {
    index
    kindExterior := expressionKind expression
    faceExterior := expressionFaceText expression
    children
  }
  standing.set {
    held with
    byExpression := held.byExpression.insert expression index
    nodes := held.nodes.push node
    rootCounts := held.rootCounts.push 0
  }
  return index

private def recordRootOccurrence (standing : IO.Ref ExpressionInterner)
    (nodeIndex : Nat) : IO Unit := do
  let held ← standing.get
  standing.set {
    held with
    rootCounts := held.rootCounts.set! nodeIndex (held.rootCounts[nodeIndex]! + 1)
  }

private def materializeExpressionUses (standing : IO.Ref ExpressionInterner)
    : IO (Array ExpressionUse) := do
  let held ← standing.get
  let mut counts := held.rootCounts
  let mut returned := #[]
  let mut remaining := held.nodes.size
  while remaining > 0 do
    let nodeIndex := remaining - 1
    let count := counts[nodeIndex]!
    let rootCount := held.rootCounts[nodeIndex]!
    if rootCount > 0 then
      returned := returned.push {
        node := nodeIndex
        parentNode := none
        childPosition := none
        count := rootCount
      }
    if count > 0 then
      let node := held.nodes[nodeIndex]!
      let mut position := 0
      for child in node.children do
        returned := returned.push {
          node := child
          parentNode := some nodeIndex
          childPosition := some position
          count
        }
        counts := counts.set! child (counts[child]! + count)
        position := position + 1
    remaining := nodeIndex
  return returned

private def expressionFace (standing : IO.Ref ExpressionInterner)
    (expression : Expr) : MetaM ExpressionFace := do
  let expression ← instantiateMVars expression
  let rootNode ← internExpressionNode standing expression
  recordRootOccurrence standing rootNode
  return {
    renderedExterior := toString (← Meta.ppExpr expression)
    leanStructuralHashExterior := reprStr expression.hash
    rootNode
  }

private def goalFace (standing : IO.Ref ExpressionInterner)
    (context : Elab.ContextInfo) (mctx : MetavarContext)
    (goal : MVarId) : IO GoalFace := do
  let context := { context with mctx }
  context.runMetaM {} do
    let declaration ← goal.getDecl
    Meta.withLCtx declaration.lctx declaration.localInstances do
      let mut localStanding := #[]
      for entry in declaration.lctx do
        localStanding := localStanding.push {
          index := entry.index
          freeOccurrenceExterior := entry.fvarId.name.toString
          userFaceExterior := entry.userName.eraseMacroScopes.toString
          binderFaceExterior := binderFace entry.binderInfo
          kindFaceExterior := reprStr entry.kind
          type := ← expressionFace standing entry.type
          value := ← entry.value?.mapM (expressionFace standing)
        }
      return {
        goalOccurrenceExterior := goal.name.toString
        userFaceExterior := declaration.userName.eraseMacroScopes.toString
        localStanding
        target := ← expressionFace standing declaration.type
      }

private def sourceRange (stx : Syntax) : Nat × Nat :=
  match stx.getRange? (canonicalOnly := true) with
  | some range => (range.start.byteIdx, range.stop.byteIdx)
  | none => (0, 0)

private def parentFace (context : Elab.ContextInfo) : String :=
  context.parentDecl?.map (·.toString) |>.getD ""

private def collectInfo (standing : IO.Ref ExpressionInterner) (tree : Elab.InfoTree)
    (terms : Array TermOccurrence) (events : Array ProofEvent) :
    IO (Array TermOccurrence × Array ProofEvent) :=
  tree.foldInfoM (init := (terms, events)) fun context info (terms, events) =>
    match info with
    | .ofTermInfo term => do
        let (startByte, stopByte) := sourceRange term.stx
        let returned ← context.runMetaM term.lctx do
          pure {
            sequence := terms.size
            parentDeclarationExterior := parentFace context
            startByte
            stopByte
            elaboratorExterior := term.elaborator.toString
            syntaxExterior := term.stx.reprint.getD (toString term.stx)
            expression := ← expressionFace standing term.expr
            expectedType := ← term.expectedType?.mapM (expressionFace standing)
          }
        return (terms.push returned, events)
    | .ofTacticInfo tactic => do
        let (startByte, stopByte) := sourceRange tactic.stx
        let returned : ProofEvent := {
          sequence := events.size
          parentDeclarationExterior := parentFace context
          startByte
          stopByte
          elaboratorExterior := tactic.elaborator.toString
          syntaxExterior := tactic.stx.reprint.getD (toString tactic.stx)
          before := ← tactic.goalsBefore.toArray.mapM (goalFace standing context tactic.mctxBefore)
          after := ← tactic.goalsAfter.toArray.mapM (goalFace standing context tactic.mctxAfter)
        }
        return (terms, events.push returned)
    | _ => return (terms, events)

private def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def definingValue : ConstantInfo → Option Expr
  | .defnInfo value => some value.value
  | .thmInfo value => some value.value
  | .opaqueInfo value => some value.value
  | _ => none

private def bodyReferencesExterior (info : ConstantInfo) : Array String :=
  let references := match definingValue info with
    | some value => value.getUsedConstants
    | none => {}
  references.map (·.toString) |>.qsort fun left right => left < right

private def declarationOperations (standing : IO.Ref ExpressionInterner)
    (environment : Environment) (modulePrefix : String) : IO (Array DeclarationOperation) := do
    let mut returned := #[]
    for (name, info) in environment.constants do
      let moduleExterior := match environment.getModuleIdxFor? name with
        | some moduleIndex => environment.header.moduleNames[moduleIndex.toNat]!.toString
        | none => "current-module"
      let admittedByPrefix :=
        moduleExterior == modulePrefix || moduleExterior.startsWith (modulePrefix ++ ".")
      unless moduleExterior == "current-module" || admittedByPrefix do continue
      returned := returned.push {
        declarationExterior := name.toString
        moduleExterior
        kindExterior := constantKind info
        type := environment.unsafeRunMetaM (expressionFace standing info.type)
        definingValue := (definingValue info).map fun value =>
          environment.unsafeRunMetaM (expressionFace standing value)
        bodyReferencesExterior := bodyReferencesExterior info
      }
    return returned.qsort (·.declarationExterior < ·.declarationExterior)

private def parseArgs : List String → Except String (String × Option String × Option String)
  | ["--input", input] => .ok (input, none, none)
  | ["--input", input, "--module-prefix", modulePrefix] =>
      .ok (input, some modulePrefix, none)
  | ["--input", input, "--output", outputPath] => .ok (input, none, some outputPath)
  | ["--input", input, "--module-prefix", modulePrefix, "--output", outputPath] =>
      .ok (input, some modulePrefix, some outputPath)
  | _ => .error "usage: derivation_atlas --input FILE [--module-prefix MODULE] [--output FILE]"

def run (args : List String) : IO UInt32 := do
  let (input, requestedPrefix, output) ←
    match parseArgs args with
    | .ok value => pure value
    | .error message => IO.eprintln message; return 2
  initSearchPath "/usr"
  let processed ← processFile input
  let modulePrefix := requestedPrefix.getD processed.moduleName
  let interner ← IO.mkRef ({} : ExpressionInterner)
  let mut terms := #[]
  let mut events := #[]
  for snapshot in processed.snapshots.getAll do
    if let some tree := snapshot.infoTree? then
      let returned ← collectInfo interner tree terms events
      terms := returned.1
      events := returned.2
  let declarations ← declarationOperations interner processed.environment modulePrefix
  let expressionNodes := (← interner.get).nodes
  let expressionUses ← materializeExpressionUses interner
  let bundle : AtlasBundle := {
    schema := "holonics.derivation-atlas.v2"
    sourcePathExterior := input
    moduleExterior := processed.moduleName
    declarationModulePrefixExterior := modulePrefix
    expressionNodes
    expressionUses
    declarationOperations := declarations
    termOccurrences := terms
    proofEvents := events
    syntaxAndNamesAreExterior := true
    kernelChecked := true
    truthStatus := "established-bounded"
  }
  let json := Json.compress <| toJson bundle
  match output with
  | some path => IO.FS.writeFile path json
  | none => IO.println json
  return 0

end Holonics.DerivationAtlas

def main (args : List String) : IO UInt32 :=
  Holonics.DerivationAtlas.run args
