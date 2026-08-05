#pragma once

#include <holonics/codec/cultivated_organ_face.hpp>
#include <holonics/event/checker_return_schema.hpp>
#include <holonics/event/cultivated_organ_rest.hpp>

namespace holonics::event {

struct cultivated_passage_return final {
  body::body_change_receipt formation_commit{};
  codec::cultivated_formal_face formal{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{};
  checker_raw_return raw{};
  checker_typed_return typed{};
  checker_morphology_return returned_morphology{};
  organ::cultivated_shift_organ acquired[organ::cultivation_family_count]{};
  bool pending_before_process{};
  bool pending_after_return{};
  bool passage_preserved{};
};

struct cultivation_observation final {
  rederivation_remount_receipt predecessor_remount{};
  organ::cultivation_receipt inquiry{};
  cultivated_passage_return passage{};
  cultivated_organ_rest_receipt rest{};
  cultivated_organ_remount_receipt remount{};
  cultivated_organ_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool final_can_continue{};
};

struct cultivated_application_observation final {
  cultivated_organ_remount_receipt predecessor_remount{};
  organ::heldout_application_receipt inquiry{};
  cultivated_passage_return passage{};
  codec::cultivated_dossier_face dossier{};
  cultivated_organ_rest_receipt rest{};
  cultivated_organ_remount_receipt remount{};
  cultivated_organ_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool final_can_continue{};
};

}  // namespace holonics::event
