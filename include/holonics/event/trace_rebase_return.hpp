#pragma once

#include <holonics/codec/trace_rebase_face.hpp>
#include <holonics/event/checker_return_schema.hpp>
#include <holonics/event/trace_rebase_surface_law.hpp>

namespace holonics::event {

struct trace_rebase_passage_return final {
  body::body_change_receipt formation_commit{};
  codec::trace_rebase_formal_face formal{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{};
  checker_raw_return raw{};
  checker_typed_return typed{};
  checker_morphology_return returned_morphology{};
  acquired_trace_rebase acquired{};
  bool pending_before_process{};
  bool pending_after_return{};
  bool passage_preserved{};
};
struct trace_rebase_discovery_observation final {
  trace_fiber_remount_receipt predecessor_remount{};
  organ::trace_rebase_discovery_receipt inquiry{};
  trace_rebase_passage_return passage{};
  trace_rebase_rest_receipt rest{};
  trace_rebase_remount_receipt remount{};
  trace_rebase_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool final_can_continue{};
};
struct heldout_trace_rebase_observation final {
  trace_rebase_remount_receipt predecessor_remount{};
  organ::heldout_trace_rebase_receipt inquiry{};
  trace_rebase_passage_return passage{};
  codec::trace_rebase_dossier_face dossier{};
  trace_rebase_rest_receipt rest{};
  trace_rebase_remount_receipt remount{};
  trace_rebase_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool final_can_continue{};
};

} // namespace holonics::event
