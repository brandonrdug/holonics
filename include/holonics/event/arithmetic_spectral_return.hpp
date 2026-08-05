#pragma once

#include <holonics/codec/arithmetic_spectral_face.hpp>
#include <holonics/event/arithmetic_spectral_rest.hpp>
#include <holonics/event/checker_return_schema.hpp>

namespace holonics::event {

struct arithmetic_spectral_passage_return final {
  body::body_change_receipt formation_commit{};
  codec::arithmetic_formal_face formal{}; codec::arithmetic_explanation conversational{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{}; checker_raw_return raw{};
  checker_typed_return typed{}; checker_morphology_return returned_morphology{};
  organ::acquired_arithmetic_spectral acquired{};
  bool pending_before_process{}; bool pending_after_return{}; bool passage_preserved{};
};

struct arithmetic_spectral_observation final {
  hodge_realization_remount_receipt predecessor_remount{};
  organ::arithmetic_spectral_receipt inquiry{};
  arithmetic_spectral_passage_return passage{};
  arithmetic_spectral_rest_receipt rest{}; arithmetic_spectral_remount_receipt remount{};
  arithmetic_spectral_rest_receipt handoff{};
  exact::word final_head{}; exact::word final_continuation{};
  bool final_can_continue{};
};

}  // namespace holonics::event
