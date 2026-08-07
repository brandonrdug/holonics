#pragma once

#include <holonics/codec/phase_crystal_face.hpp>
#include <holonics/event/checker_return_schema.hpp>
#include <holonics/event/phase_crystal_rest.hpp>
#include <holonics/organ/phase_crystal_receipt.hpp>

namespace holonics::event {

struct phase_crystal_observation final {
  geometry_inquiry_remount_receipt predecessor_remount{};
  organ::phase_crystal_receipt inquiry{};
  body::body_change_receipt formation_commit{};
  codec::phase_crystal_face formal{};
  codec::phase_crystal_explanation conversational{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{};
  checker_raw_return raw{};
  checker_typed_return typed{};
  checker_morphology_return returned_morphology{};
  organ::acquired_phase_crystal acquired{};
  phase_crystal_rest_receipt rest{};
  phase_crystal_remount_receipt remount{};
  phase_crystal_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool pending_before_process{};
  bool pending_after_return{};
  bool passage_preserved{};
  bool final_can_continue{};
};

}  // namespace holonics::event
