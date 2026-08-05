#pragma once

#include <holonics/codec/expression_geometry_face.hpp>
#include <holonics/event/checker_return_schema.hpp>
#include <holonics/event/expression_geometry_rest.hpp>
#include <holonics/organ/expression_geometry_receipt.hpp>

namespace holonics::event {

struct expression_geometry_passage_return final {
  body::body_change_receipt formation_commit{};
  codec::expression_geometry_formal_face formal{};
  codec::expression_geometry_explanation conversational{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{}; checker_raw_return raw{};
  checker_typed_return typed{}; checker_morphology_return returned_morphology{};
  organ::acquired_expression_geometry acquired{};
  bool pending_before_process{}; bool pending_after_return{}; bool passage_preserved{};
};

struct expression_geometry_observation final {
  intrinsic_hypergeometry_remount_receipt predecessor_remount{};
  organ::expression_geometry_receipt inquiry{};
  organ::expression_changed_receipt changed{};
  expression_geometry_passage_return passage{};
  expression_geometry_rest_receipt rest{};
  expression_geometry_remount_receipt remount{};
  expression_geometry_rest_receipt handoff{};
  exact::word final_head{}; exact::word final_continuation{};
  bool changed_sensitive{}; bool final_can_continue{};
};

}  // namespace holonics::event
