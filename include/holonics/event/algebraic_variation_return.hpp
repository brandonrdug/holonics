#pragma once

#include <holonics/codec/algebraic_variation_face.hpp>
#include <holonics/event/algebraic_variation_rest.hpp>
#include <holonics/event/checker_return_schema.hpp>
#include <holonics/organ/algebraic_variation_receipt.hpp>

namespace holonics::event {

struct algebraic_variation_passage_return final {
  body::body_change_receipt formation_commit{};
  codec::variation_formal_face formal{};
  codec::variation_explanation conversational{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{};
  checker_raw_return raw{};
  checker_typed_return typed{};
  checker_morphology_return returned_morphology{};
  organ::acquired_algebraic_variation acquired{};
  bool pending_before_process{};
  bool pending_after_return{};
  bool passage_preserved{};
};

struct algebraic_variation_observation final {
  toric_cycle_remount_receipt predecessor_remount{};
  organ::algebraic_variation_receipt inquiry{};
  algebraic_variation_passage_return passage{};
  algebraic_variation_rest_receipt rest{};
  algebraic_variation_remount_receipt remount{};
  algebraic_variation_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool final_can_continue{};
};

}  // namespace holonics::event
