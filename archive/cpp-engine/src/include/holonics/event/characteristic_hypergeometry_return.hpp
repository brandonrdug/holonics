#pragma once

#include <holonics/codec/characteristic_hypergeometry_face.hpp>
#include <holonics/event/characteristic_hypergeometry_rest.hpp>
#include <holonics/event/checker_return_schema.hpp>

namespace holonics::event {

struct characteristic_passage_return final {
  body::body_change_receipt formation_commit{};
  codec::characteristic_formal_face formal{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{};
  checker_raw_return raw{};
  checker_typed_return typed{};
  checker_morphology_return returned_morphology{};
  acquired_characteristic_fiber acquired{};
  bool pending_before_process{};
  bool pending_after_return{};
  bool passage_preserved{};
};
struct characteristic_discovery_observation final {
  elementary_calculus_remount_receipt predecessor_remount{};
  organ::characteristic_hypergeometry_receipt inquiry{};
  characteristic_passage_return passage{};
  hypergeometry_rest_receipt rest{};
  hypergeometry_remount_receipt remount{};
  hypergeometry_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool final_can_continue{};
};
struct heldout_characteristic_observation final {
  hypergeometry_remount_receipt predecessor_remount{};
  organ::heldout_characteristic_receipt inquiry{};
  characteristic_passage_return passage{};
  codec::characteristic_dossier_face dossier{};
  hypergeometry_rest_receipt rest{};
  hypergeometry_remount_receipt remount{};
  hypergeometry_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool final_can_continue{};
};

} // namespace holonics::event
