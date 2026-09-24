/-!
# Receiver-caused codec reflection and continuation

[definition] This is the source-neutral law extracted from the current Rust
`holonic-language::ReflectiveRuntime`. A codec is an application chart (`Program` in Rust); a
revision carries the source face that caused it; a receiver owns the reflective request. The
contract does not interpret programs or define a universal syntax.

The owner states the checked structural crossing: a running continuation can be reflected at its
current codec and instruction; a returned child codec must name that codec as a parent; the same
continuation then resumes at the child codec, at the same instruction and with the returned
environment. Unchanged resumption preserves the codec and instruction. This formalizes only the
reflection/revision/resumption branch: executor-specific advance/rest semantics, atlas
capacity/refusal behavior, source-face registration, and remount validation are outside scope.
-/

namespace Holonics.Transport.ReflectiveContinuation

universe u v w

inductive ContinuationState (Reflection : Type u) where
  | running
  | reflected (reflection : Reflection)
  | rested
  | obstructed
  deriving DecidableEq

inductive ReflectionState (Codec : Type v) where
  | pending
  | revised (codec : Codec)
  | resumedUnchanged
  deriving DecidableEq

/-- A live continuation. `environment` is the executor-owned standing returned at this crossing. -/
structure Continuation (Codec : Type v) (Reflection : Type u) (Environment : Type w) where
  id : Nat
  codec : Codec
  instruction : Nat
  state : ContinuationState Reflection
  environment : Environment

/-- A receiver-qualified frame snapshots the codec and instruction at the request. -/
structure Frame (Codec : Type v) (ContinuationId : Type u) (Receiver : Type w) where
  id : Nat
  receiver : Receiver
  continuation : ContinuationId
  codec : Codec
  instruction : Nat
  state : ReflectionState Codec

/-- The codec lineage and causal face attached to one proposed revision. -/
structure CodecRevision (Codec : Type v) (Face : Type w) where
  id : Codec
  parents : List Codec
  causedBy : Face

/-- A reflection request is admitted only from a running continuation; it freezes the source
codec and instruction into the receiver's frame and returns the continuation's environment. -/
def requestReflection {Codec : Type v} {Receiver : Type w} {Environment : Type w}
    (reflectionId : Nat) (receiver : Receiver)
    (c : Continuation Codec Nat Environment) :
    Option (Continuation Codec Nat Environment × Frame Codec Nat Receiver) := by
  cases c with
  | mk id codec instruction state environment =>
    cases state with
    | running =>
      exact some
        (⟨id, codec, instruction, .reflected reflectionId, environment⟩,
          ⟨reflectionId, receiver, id, codec, instruction, .pending⟩)
    | reflected _ => exact none
    | rested => exact none
    | obstructed => exact none

/-- A successful request records the receiving role at the current codec and instruction while
keeping the same continuation identity and returned environment. -/
theorem requestReflection_success {Codec : Type v} {Receiver : Type w} {Environment : Type w}
    (reflectionId : Nat) (receiver : Receiver)
    (c : Continuation Codec Nat Environment)
    (result : Continuation Codec Nat Environment × Frame Codec Nat Receiver)
    (h : requestReflection reflectionId receiver c = some result) :
    result.1.id = c.id ∧ result.1.codec = c.codec ∧
      result.1.instruction = c.instruction ∧ result.1.state = .reflected reflectionId ∧
      result.1.environment = c.environment ∧ result.2.id = reflectionId ∧
      result.2.receiver = receiver ∧ result.2.continuation = c.id ∧
      result.2.codec = c.codec ∧ result.2.instruction = c.instruction := by
  cases c with
  | mk id codec instruction state environment =>
    cases state with
    | running =>
      simp only [requestReflection] at h
      cases h
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | reflected _ => simp [requestReflection] at h
    | rested => simp [requestReflection] at h
    | obstructed => simp [requestReflection] at h

/-- A matching open request may revise the codec and resume the same continuation. -/
def reviseAndResume {Codec : Type v} {Receiver : Type w} {Environment : Type w} {Face : Type w}
    [DecidableEq Codec]
    (frame : Frame Codec Nat Receiver) (c : Continuation Codec Nat Environment)
    (revision : CodecRevision Codec Face) :
    Option (Continuation Codec Nat Environment × Frame Codec Nat Receiver) := by
  if h : frame.state = .pending ∧ frame.continuation = c.id ∧
      c.state = .reflected frame.id ∧ frame.codec ∈ revision.parents then
    exact some
      (⟨c.id, revision.id, c.instruction, .running, c.environment⟩,
        { frame with state := .revised revision.id })
  else exact none

/-- Successful revision adopts the child codec, resumes the same continuation at the same
instruction, and preserves the environment returned by the reflecting executor. -/
theorem reviseAndResume_success {Codec : Type v} {Receiver : Type w} {Environment : Type w} {Face : Type w}
    [DecidableEq Codec] (frame : Frame Codec Nat Receiver)
    (c : Continuation Codec Nat Environment) (revision : CodecRevision Codec Face)
    (result : Continuation Codec Nat Environment × Frame Codec Nat Receiver)
    (h : reviseAndResume frame c revision = some result) :
    result.1.id = c.id ∧ result.1.codec = revision.id ∧
      result.1.instruction = c.instruction ∧ result.1.state = .running ∧
    result.1.environment = c.environment ∧
      result.2.state = .revised revision.id ∧ frame.codec ∈ revision.parents := by
  by_cases hvalid : frame.state = .pending ∧ frame.continuation = c.id ∧
      c.state = .reflected frame.id ∧ frame.codec ∈ revision.parents
  · simp [reviseAndResume, hvalid] at h
    cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hvalid.2.2.2⟩
  · simp [reviseAndResume, hvalid] at h

/-- Successful unchanged resumption reopens the same continuation without changing its codec,
instruction, or returned environment. -/
def resumeUnchanged {Codec : Type v} {Receiver : Type w} {Environment : Type w}
    [DecidableEq Codec]
    (frame : Frame Codec Nat Receiver) (c : Continuation Codec Nat Environment) :
    Option (Continuation Codec Nat Environment × Frame Codec Nat Receiver) := by
  if h : frame.state = .pending ∧ frame.continuation = c.id ∧
      c.state = .reflected frame.id then
    exact some
      (⟨c.id, c.codec, c.instruction, .running, c.environment⟩,
        { frame with state := .resumedUnchanged })
  else exact none

theorem resumeUnchanged_success {Codec : Type v} {Receiver : Type w} {Environment : Type w}
    [DecidableEq Codec]
    (frame : Frame Codec Nat Receiver) (c : Continuation Codec Nat Environment)
    (result : Continuation Codec Nat Environment × Frame Codec Nat Receiver)
    (h : resumeUnchanged frame c = some result) :
    result.1.id = c.id ∧ result.1.codec = c.codec ∧
    result.1.instruction = c.instruction ∧ result.1.state = .running ∧
    result.1.environment = c.environment ∧ result.2.state = .resumedUnchanged := by
  by_cases hvalid : frame.state = .pending ∧ frame.continuation = c.id ∧
      c.state = .reflected frame.id
  · simp [resumeUnchanged, hvalid] at h
    cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [resumeUnchanged, hvalid] at h

/-- Composing a receiver's reflection request with a lineage-qualified revision preserves the
requested boundary and executor-returned environment while adopting the child codec. -/
theorem revision_resumes_the_requested_boundary {Codec : Type v} {Receiver : Type w}
    {Environment : Type w} {Face : Type w} [DecidableEq Codec]
    (reflectionId : Nat) (receiver : Receiver)
    (c : Continuation Codec Nat Environment) (revision : CodecRevision Codec Face)
    (requested : Continuation Codec Nat Environment × Frame Codec Nat Receiver)
    (resumed : Continuation Codec Nat Environment × Frame Codec Nat Receiver)
    (hrequest : requestReflection reflectionId receiver c = some requested)
    (hresume : reviseAndResume requested.2 requested.1 revision = some resumed) :
    resumed.1.id = c.id ∧ resumed.1.codec = revision.id ∧
    resumed.1.instruction = c.instruction ∧ resumed.1.environment = c.environment ∧
      requested.2.receiver = receiver ∧ requested.2.codec = c.codec ∧
      requested.2.instruction = c.instruction ∧
      c.codec ∈ revision.parents ∧ resumed.2.state = .revised revision.id := by
  have hreq := requestReflection_success reflectionId receiver c requested hrequest
  have hrev := reviseAndResume_success requested.2 requested.1 revision resumed hresume
  rcases hreq with ⟨reqId, reqCodec, reqInstr, _, reqEnv, _, reqReceiver, _, reqFrameCodec,
    reqFrameInstr⟩
  rcases hrev with ⟨resId, resCodec, resInstr, resState, resEnv, resFrameState, parent⟩
  rw [reqFrameCodec] at parent
  exact ⟨resId.trans reqId, resCodec, resInstr.trans reqInstr, resEnv.trans reqEnv,
    reqReceiver, reqFrameCodec, reqFrameInstr, parent, resFrameState⟩

#print axioms reviseAndResume_success
#print axioms requestReflection_success
#print axioms resumeUnchanged_success
#print axioms revision_resumes_the_requested_boundary

end Holonics.Transport.ReflectiveContinuation
