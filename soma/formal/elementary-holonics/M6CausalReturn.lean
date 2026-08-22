import Lean.Elab.Frontend
import Lean.Server.InfoUtils
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
An exterior Lean apparatus face for M6.

This executable elaborates one addressed source file and returns only typed term occurrences and
before/after proof states. Lean remains the exterior elaborator/checker: it does not select a route,
classify a case, schedule Eros, or become the runtime topology.
-/

open Lean

namespace Holonics.M6.CausalReturn

private def processFile (fileName : String) : IO (Language.SnapshotTree × Environment) := do
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
  let snaps := Language.toSnapshotTree snap
  let wait ← snaps.waitAll
  let _ := wait.get
  let hasErrors ← snaps.runAndReport opts false
  if hasErrors then
    throw <| IO.userError s!"elaboration failed for {fileName}"
  let some commandState := Language.Lean.waitForFinalCmdState? snap
    | throw <| IO.userError s!"no final environment returned for {fileName}"
  return (snaps, commandState.env)

structure ExpressionFace where
  renderedExterior : String
  leanStructuralHashExterior : UInt64
  orderedTransportRoot : Nat
  deriving Inhabited, ToJson

structure ExpressionNode where
  index : Nat
  nodeFaceExterior : String
  children : Array Nat
  deriving Inhabited, ToJson

structure ExpressionInterner where
  byExpression : ExprMap Nat := {}
  nodes : Array ExpressionNode := #[]
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
  parentDeclarationExterior : String
  elaboratorExterior : String
  startByte : Nat
  stopByte : Nat
  syntaxExterior : String
  expression : ExpressionFace
  expectedType : Option ExpressionFace
  deriving ToJson

structure TacticTransition where
  parentDeclarationExterior : String
  elaboratorExterior : String
  startByte : Nat
  stopByte : Nat
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

structure CausalReceipt where
  schema : String
  sourcePathExterior : String
  expressionNodes : Array ExpressionNode
  declarationOperations : Array DeclarationOperation
  termOccurrences : Array TermOccurrence
  tacticTransitions : Array TacticTransition
  syntaxAndNamesAreExterior : Bool
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

private def expressionNodeFace : Expr → String
  | expression => match expression with
  | .bvar index => s!"bound|{index}"
  | .fvar occurrence => s!"free|{occurrence.name}"
  | .mvar occurrence => s!"open|{occurrence.name}"
  | .sort level => s!"sort|{reprStr level}"
  | .const name levels => s!"constant|{name}|{reprStr levels}"
  | app@(.app _ _) =>
      let head := app.getAppFn
      let label := match head with
        | .const name _ => name.toString
        | .fvar occurrence => occurrence.name.toString
        | _ => ""
      s!"application|{label}"
  | .lam name _ _ binder => s!"lambda|{name}|{binderFace binder}"
  | .forallE name _ _ binder => s!"forall|{name}|{binderFace binder}"
  | .letE name _ _ _ nondep =>
      let kind := if nondep then "have" else "let"
      s!"{kind}|{name}"
  | .lit literal => s!"literal|{reprStr literal}"
  | .mdata data _ => s!"metadata|{reprStr data}"
  | .proj typeName index _ => s!"projection|{typeName}|{index}"

private partial def internExpressionNode (standing : IO.Ref ExpressionInterner)
    (expression : Expr) : IO Nat := do
  if let some index := (← standing.get).byExpression[expression]? then
    return index
  let children ← (expressionChildren expression).mapM (internExpressionNode standing)
  -- A child insertion may have admitted this exact expression as one of its own descendants only
  -- through sharing, never through a cycle; repeat the lookup before assigning the next address.
  let held ← standing.get
  if let some index := held.byExpression[expression]? then
    return index
  let index := held.nodes.size
  let node := { index, nodeFaceExterior := expressionNodeFace expression, children }
  standing.set {
    byExpression := held.byExpression.insert expression index
    nodes := held.nodes.push node
  }
  return index

private def expressionFace (standing : IO.Ref ExpressionInterner)
    (expression : Expr) : MetaM ExpressionFace := do
  let expression ← instantiateMVars expression
  return {
    renderedExterior := toString (← Meta.ppExpr expression)
    leanStructuralHashExterior := expression.hash
    orderedTransportRoot := ← internExpressionNode standing expression
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

private def termOccurrence (standing : IO.Ref ExpressionInterner)
    (context : Elab.ContextInfo)
    (info : Elab.TermInfo) : IO TermOccurrence := do
  let (startByte, stopByte) := sourceRange info.stx
  context.runMetaM info.lctx do
    return {
      parentDeclarationExterior := parentFace context
      elaboratorExterior := info.elaborator.toString
      startByte
      stopByte
      syntaxExterior := info.stx.reprint.getD (toString info.stx)
      expression := ← expressionFace standing info.expr
      expectedType := ← info.expectedType?.mapM (expressionFace standing)
    }

private def tacticTransition (standing : IO.Ref ExpressionInterner)
    (context : Elab.ContextInfo)
    (info : Elab.TacticInfo) : IO TacticTransition := do
  let (startByte, stopByte) := sourceRange info.stx
  return {
    parentDeclarationExterior := parentFace context
    elaboratorExterior := info.elaborator.toString
    startByte
    stopByte
    syntaxExterior := info.stx.reprint.getD (toString info.stx)
    before := ← info.goalsBefore.toArray.mapM (goalFace standing context info.mctxBefore)
    after := ← info.goalsAfter.toArray.mapM (goalFace standing context info.mctxAfter)
  }

private def collectInfo (standing : IO.Ref ExpressionInterner) (tree : Elab.InfoTree)
    (initial : Array TermOccurrence × Array TacticTransition) :
    IO (Array TermOccurrence × Array TacticTransition) :=
  tree.foldInfoM (init := initial) fun context info (terms, transitions) =>
    match info with
    | .ofTermInfo term => return (terms.push (← termOccurrence standing context term), transitions)
    | .ofTacticInfo tactic => return (terms, transitions.push (← tacticTransition standing context tactic))
    | _ => return (terms, transitions)

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

private def isDirectProposition (expression : Expr) : Bool :=
  expression == mkSort levelZero

private def bodyReferencesExterior (info : ConstantInfo) : Array String :=
  let references := match info with
    | .thmInfo value => value.value.getUsedConstants
    | .defnInfo value => if isDirectProposition value.type then
        value.value.getUsedConstants
      else
        {}
    | .opaqueInfo value => if isDirectProposition value.type then
        value.value.getUsedConstants
      else
        {}
    | _ => {}
  references.map (·.toString) |>.qsort fun left right => left < right

private def declarationOperations (standing : IO.Ref ExpressionInterner)
    (environment : Environment) : Array DeclarationOperation :=
  Id.run do
    let mut returned := #[]
    for (name, info) in environment.constants do
      let moduleExterior := match environment.getModuleIdxFor? name with
        | some moduleIndex => environment.header.moduleNames[moduleIndex.toNat]!.toString
        | none => "current-module"
      unless moduleExterior == "current-module" ||
          moduleExterior.startsWith "ElementaryHolonics" do continue
      returned := returned.push {
        declarationExterior := name.toString
        moduleExterior
        kindExterior := constantKind info
        type := environment.unsafeRunMetaM (expressionFace standing info.type)
        definingValue := match info with
          | .thmInfo _ => none
          | _ => if isDirectProposition info.type then
              (definingValue info).map fun value =>
                environment.unsafeRunMetaM (expressionFace standing value)
            else
              none
        bodyReferencesExterior := bodyReferencesExterior info
      }
    returned.qsort (·.declarationExterior < ·.declarationExterior)

def run (args : List String) : IO UInt32 := do
  initSearchPath "/usr"
  let (returnDeclarations, fileName) ← match args with
    | ["--declarations", fileName] => pure (true, fileName)
    | ["--transitions", fileName] => pure (false, fileName)
    | _ => IO.eprintln "usage: m6_lean_causal_return (--declarations|--transitions) FILE"; return 2
  let (snaps, environment) ← processFile fileName
  let expressionInterner ← IO.mkRef ({} : ExpressionInterner)
  let mut termOccurrences := #[]
  let mut tacticTransitions := #[]
  for snap in snaps.getAll do
    if let some tree := snap.infoTree? then
      let returned ← collectInfo expressionInterner tree (termOccurrences, tacticTransitions)
      termOccurrences := returned.1
      tacticTransitions := returned.2
  let declarationOperations := if returnDeclarations then
    declarationOperations expressionInterner environment
  else
    #[]
  let expressionNodes := (← expressionInterner.get).nodes
  let returned : CausalReceipt := {
    schema := "holonics.m6.lean-causal-return.v1"
    sourcePathExterior := fileName
    expressionNodes
    declarationOperations
    termOccurrences
    tacticTransitions
    syntaxAndNamesAreExterior := true
    truthStatus := "established-bounded"
  }
  IO.println <| Json.compress <| toJson returned
  return 0

end Holonics.M6.CausalReturn

def main (args : List String) : IO UInt32 :=
  Holonics.M6.CausalReturn.run args
