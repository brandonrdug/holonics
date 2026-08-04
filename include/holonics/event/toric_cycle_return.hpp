#pragma once

#include <holonics/codec/toric_cycle_face.hpp>
#include <holonics/event/checker_return_schema.hpp>
#include <holonics/event/toric_cycle_rest.hpp>
#include <holonics/organ/toric_cycle_receipt.hpp>

namespace holonics::event {

struct toric_passage_return final {
  body::body_change_receipt formation_commit{};
  codec::toric_formal_face formal{};
  codec::toric_explanation conversational{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{};
  checker_raw_return raw{};
  checker_typed_return typed{};
  checker_morphology_return returned_morphology{};
  organ::acquired_toric_cycle acquired{};
  bool pending_before_process{};
  bool pending_after_return{};
  bool passage_preserved{};
};

struct toric_cycle_observation final {
  cm_incidence_remount_receipt predecessor_remount{};
  organ::toric_cycle_receipt inquiry{};
  toric_passage_return passage{};
  toric_cycle_rest_receipt rest{};
  toric_cycle_remount_receipt remount{};
  toric_cycle_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool final_can_continue{};
};

}  // namespace holonics::event
