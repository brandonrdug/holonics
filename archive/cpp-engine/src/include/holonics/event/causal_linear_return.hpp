#pragma once

#include <holonics/codec/causal_linear_face.hpp>
#include <holonics/event/causal_linear_rest.hpp>
#include <holonics/event/checker_return_schema.hpp>
#include <holonics/organ/causal_linear_receipt.hpp>

namespace holonics::event {

struct causal_linear_passage_return final {
  body::body_change_receipt formation_commit{};
  codec::causal_linear_formal_face formal{};
  codec::causal_linear_explanation conversational{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{};
  checker_raw_return raw{};
  checker_typed_return typed{};
  checker_morphology_return returned_morphology{};
  organ::acquired_causal_linear acquired{};
  bool pending_before_process{};
  bool pending_after_return{};
  bool passage_preserved{};
};

struct causal_linear_observation final {
  algebraic_variation_remount_receipt predecessor_remount{};
  organ::causal_linear_receipt inquiry{};
  causal_linear_passage_return passage{};
  causal_linear_rest_receipt rest{};
  causal_linear_remount_receipt remount{};
  causal_linear_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool final_can_continue{};
};

}  // namespace holonics::event
