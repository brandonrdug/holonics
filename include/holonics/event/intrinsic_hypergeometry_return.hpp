#pragma once

#include <holonics/codec/intrinsic_hypergeometry_face.hpp>
#include <holonics/event/checker_return_schema.hpp>
#include <holonics/event/intrinsic_hypergeometry_rest.hpp>
#include <holonics/organ/intrinsic_hypergeometry_receipt.hpp>

namespace holonics::event {

struct intrinsic_hypergeometry_passage_return final {
  body::body_change_receipt formation_commit{};
  codec::intrinsic_hypergeometry_formal_face formal{};
  codec::intrinsic_hypergeometry_explanation conversational{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{};
  checker_raw_return raw{};
  checker_typed_return typed{};
  checker_morphology_return returned_morphology{};
  organ::acquired_intrinsic_hypergeometry acquired{};
  bool pending_before_process{};
  bool pending_after_return{};
  bool passage_preserved{};
};

struct intrinsic_hypergeometry_observation final {
  causal_linear_remount_receipt predecessor_remount{};
  organ::intrinsic_hypergeometry_receipt inquiry{};
  organ::intrinsic_phase_case_receipt changed_case{};
  intrinsic_hypergeometry_passage_return passage{};
  intrinsic_hypergeometry_rest_receipt rest{};
  intrinsic_hypergeometry_remount_receipt remount{};
  intrinsic_hypergeometry_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool changed_sensitive{};
  bool final_can_continue{};
};

}  // namespace holonics::event
