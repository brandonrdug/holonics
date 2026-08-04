#pragma once

#include <holonics/codec/cm_incidence_face.hpp>
#include <holonics/event/cm_incidence_rest.hpp>
#include <holonics/event/checker_return_schema.hpp>
#include <holonics/organ/cm_incidence_receipt.hpp>

namespace holonics::event {

struct cm_passage_return final {
  body::body_change_receipt formation_commit{};
  codec::cm_formal_face formal{};
  codec::cm_explanation conversational{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{};
  checker_raw_return raw{};
  checker_typed_return typed{};
  checker_morphology_return returned_morphology{};
  organ::acquired_cm_incidence acquired{};
  bool pending_before_process{};
  bool pending_after_return{};
  bool passage_preserved{};
};

struct cm_incidence_observation final {
  blind_reconstruction_remount_receipt predecessor_remount{};
  organ::cm_incidence_receipt inquiry{};
  cm_passage_return passage{};
  cm_incidence_rest_receipt rest{};
  cm_incidence_remount_receipt remount{};
  cm_incidence_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool final_can_continue{};
};

}  // namespace holonics::event
