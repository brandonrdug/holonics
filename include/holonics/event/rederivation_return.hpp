#pragma once

#include <holonics/codec/rederivation_face.hpp>
#include <holonics/event/checker_return_schema.hpp>
#include <holonics/event/rederivation_rest.hpp>

namespace holonics::event {

struct rederivation_passage_return final {
  body::body_change_receipt formation_commit{};
  codec::rederivation_surface surface{};
  codec::rederivation_formal_face formal{};
  codec::rederivation_dossier_face conversational{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{};
  checker_raw_return raw{};
  checker_typed_return typed{};
  checker_morphology_return returned_morphology{};
  organ::acquired_rederivation_fiber acquired[4]{};
  bool pending_before_process{};
  bool pending_after_return{};
  bool passage_preserved{};
};

struct rederivation_foil_return final {
  body::body_change_receipt formation_commit{};
  codec::rederivation_foil_face formal{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{};
  checker_raw_return raw{};
  checker_typed_return typed{};
  checker_morphology_return returned_morphology{};
  bool pending_before_process{};
  bool pending_after_return{};
  bool passage_preserved{};
  bool expected_rejection{};
};

struct rederivation_observation final {
  arithmetic_spectral_remount_receipt predecessor_remount{};
  organ::rederivation_receipt inquiry{};
  rederivation_foil_return foil{};
  rederivation_passage_return passage{};
  rederivation_rest_receipt rest{};
  rederivation_remount_receipt remount{};
  rederivation_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool final_can_continue{};
};

} // namespace holonics::event
