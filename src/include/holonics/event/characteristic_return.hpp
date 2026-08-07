#pragma once

#include <holonics/codec/characteristic_face.hpp>
#include <holonics/event/characteristic_rest.hpp>
#include <holonics/event/checker_return_schema.hpp>
#include <holonics/organ/characteristic_receipt.hpp>

namespace holonics::event {

struct characteristic_observation final {
  phase_crystal_remount_receipt predecessor_remount{};
  organ::characteristic_receipt inquiry{};
  body::body_change_receipt formation_commit{};
  codec::characteristic_face formal{};
  codec::characteristic_explanation conversational{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{};
  checker_raw_return raw{};
  checker_typed_return typed{};
  checker_morphology_return returned_morphology{};
  organ::acquired_characteristic acquired{};
  characteristic_rest_receipt rest{};
  characteristic_remount_receipt remount{};
  characteristic_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool pending_before_process{};
  bool pending_after_return{};
  bool passage_preserved{};
  bool final_can_continue{};
};

}  // namespace holonics::event
