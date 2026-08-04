#pragma once

#include <holonics/codec/theorem_production_renderer.hpp>
#include <holonics/event/checker_return_schema.hpp>
#include <holonics/event/theorem_production_rest.hpp>
#include <holonics/organ/theorem_production_receipt.hpp>

namespace holonics::event {

struct theorem_production_observation final {
  organ::theorem_generation_receipt generation{};
  body::body_change_receipt generation_commit{};
  codec::formal_math_face formal{};
  codec::conversational_math_face conversational{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{};
  codec::formal_checker_face checker_face{};
  checker_raw_return raw{};
  checker_typed_return typed{};
  checker_morphology_return returned_morphology{};
  organ::acquired_theorem_fiber acquired{};
  organ::theorem_probe_receipt before{};
  organ::theorem_probe_receipt after{};
  organ::theorem_ablation_receipt ablation{};
  theorem_production_rest_receipt rest{};
  theorem_production_remount_receipt remount{};
  theorem_production_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool pending_before_process{};
  bool pending_after_return{};
  bool passage_preserved{};
  bool behavior_changed{};
  bool handoff_continuation_valid{};
};

}  // namespace holonics::event
