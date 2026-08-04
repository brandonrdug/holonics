#pragma once

#include <holonics/codec/geometry_theory_face.hpp>
#include <holonics/event/checker_return_schema.hpp>
#include <holonics/event/geometry_inquiry_rest.hpp>
#include <holonics/organ/geometry_inquiry_receipt.hpp>

namespace holonics::event {

struct geometry_inquiry_observation final {
  terminal_theorem_remount_receipt predecessor_remount{};
  organ::geometry_inquiry_receipt inquiry{};
  body::body_change_receipt theory_commit{};
  codec::geometry_theory_face formal{};
  codec::geometry_theory_explanation conversational{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{};
  checker_raw_return raw{};
  checker_typed_return typed{};
  checker_morphology_return returned_morphology{};
  organ::acquired_geometry_theory acquired{};
  geometry_inquiry_rest_receipt rest{};
  geometry_inquiry_remount_receipt remount{};
  geometry_inquiry_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool pending_before_process{};
  bool pending_after_return{};
  bool passage_preserved{};
  bool final_can_continue{};
};

}  // namespace holonics::event
