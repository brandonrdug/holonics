#pragma once

#include <holonics/event/dependent_theorem_production_law.hpp>
#include <holonics/event/absent_fiber_control.hpp>
#include <holonics/event/terminal_theorem_rest.hpp>
#include <holonics/event/theorem_production_return.hpp>

namespace holonics::event {

struct terminal_theorem_observation final {
  absent_fiber_control_receipt absent_fiber{};
  theorem_production_remount_receipt production_remount{};
  theorem_production_remount_receipt ablation_remount{};
  dependent_theorem_generation_receipt generation{};
  dependent_theorem_generation_receipt ablated_generation{};
  body::body_change_receipt generation_commit{};
  codec::formal_math_face formal{};
  codec::conversational_math_face conversational{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{};
  codec::formal_checker_face checker_face{};
  checker_raw_return raw{};
  checker_typed_return typed{};
  checker_morphology_return returned_morphology{};
  organ::acquired_theorem_fiber second_acquired{};
  terminal_theorem_rest_receipt rest{};
  terminal_theorem_remount_receipt remount{};
  terminal_theorem_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  std::uint16_t ablation_source_bytes{};
  bool source_detached{};
  bool setup_integrity_exact{};
  bool ablation_generation_refused{};
  bool dependency_exact{};
  bool pending_before_process{};
  bool pending_after_return{};
  bool passage_preserved{};
  bool handoff_continuation_valid{};
};

}  // namespace holonics::event
