#pragma once

#include <holonics/codec/hodge_realization_face.hpp>
#include <holonics/event/checker_return_schema.hpp>
#include <holonics/event/hodge_realization_rest.hpp>
#include <holonics/organ/hodge_realization_receipt.hpp>

namespace holonics::event {

struct hodge_realization_passage_return final {
  body::body_change_receipt formation_commit{};
  codec::hodge_formal_face formal{}; codec::hodge_explanation conversational{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{}; checker_raw_return raw{};
  checker_typed_return typed{}; checker_morphology_return returned_morphology{};
  organ::acquired_hodge_realization acquired{};
  bool pending_before_process{}; bool pending_after_return{}; bool passage_preserved{};
};

struct hodge_realization_observation final {
  expression_geometry_remount_receipt predecessor_remount{};
  organ::hodge_realization_receipt inquiry{};
  organ::hodge_blowup_receipt changed{};
  hodge_realization_passage_return passage{};
  hodge_realization_rest_receipt rest{}; hodge_realization_remount_receipt remount{};
  hodge_realization_rest_receipt handoff{};
  exact::word final_head{}; exact::word final_continuation{};
  bool changed_sensitive{}; bool final_can_continue{};
};

}  // namespace holonics::event
