#pragma once

#include <holonics/codec/regular_singular_face.hpp>
#include <holonics/event/checker_return_schema.hpp>
#include <holonics/event/regular_singular_rest.hpp>
#include <holonics/organ/regular_singular_receipt.hpp>

namespace holonics::event {

struct regular_singular_observation final {
  characteristic_remount_receipt predecessor_remount{};
  organ::regular_singular_receipt inquiry{};
  body::body_change_receipt formation_commit{};
  codec::regular_singular_face formal{};
  codec::regular_singular_explanation conversational{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{};
  checker_raw_return raw{};
  checker_typed_return typed{};
  checker_morphology_return returned_morphology{};
  organ::acquired_regular_singular acquired{};
  regular_singular_rest_receipt rest{};
  regular_singular_remount_receipt remount{};
  regular_singular_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool pending_before_process{};
  bool pending_after_return{};
  bool passage_preserved{};
  bool final_can_continue{};
};

}  // namespace holonics::event
