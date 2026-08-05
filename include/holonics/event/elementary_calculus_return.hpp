#pragma once

#include <holonics/codec/elementary_calculus_face.hpp>
#include <holonics/event/checker_return_schema.hpp>
#include <holonics/event/elementary_calculus_rest.hpp>

namespace holonics::event {

struct elementary_passage_return final {
  body::body_change_receipt formation_commit{};
  codec::elementary_formal_face formal{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{};
  checker_raw_return raw{};
  checker_typed_return typed{};
  checker_morphology_return returned_morphology{};
  acquired_elementary_fiber acquired[6]{};
  bool pending_before_process{};
  bool pending_after_return{};
  bool passage_preserved{};
};

struct elementary_calculus_observation final {
  cultivated_organ_remount_receipt predecessor_remount{};
  organ::elementary_calculus_receipt inquiry{};
  elementary_passage_return passage{};
  elementary_calculus_rest_receipt rest{};
  elementary_calculus_remount_receipt remount{};
  elementary_calculus_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool final_can_continue{};
};

struct heldout_holonomy_observation final {
  elementary_calculus_remount_receipt predecessor_remount{};
  organ::heldout_holonomy_receipt inquiry{};
  elementary_passage_return passage{};
  codec::elementary_dossier_face dossier{};
  elementary_calculus_rest_receipt rest{};
  elementary_calculus_remount_receipt remount{};
  elementary_calculus_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool final_can_continue{};
};

}  // namespace holonics::event
