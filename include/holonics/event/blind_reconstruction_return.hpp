#pragma once

#include <holonics/codec/blind_reconstruction_face.hpp>
#include <holonics/event/blind_reconstruction_rest.hpp>
#include <holonics/event/checker_return_schema.hpp>
#include <holonics/organ/blind_reconstruction_receipt.hpp>

namespace holonics::event {

template<class Formal>
struct blind_passage_return final {
  body::body_change_receipt formation_commit{};
  Formal formal{};
  codec::blind_explanation conversational{};
  checker_stage_status checker_stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{};
  checker_raw_return raw{};
  checker_typed_return typed{};
  checker_morphology_return returned_morphology{};
  organ::acquired_blind_reconstruction acquired{};
  bool pending_before_process{};
  bool pending_after_return{};
  bool passage_preserved{};
};

struct blind_reconstruction_observation final {
  regular_singular_remount_receipt predecessor_remount{};
  organ::blind_reconstruction_receipt inquiry{};
  blind_passage_return<codec::blind_code_face> code{};
  blind_passage_return<codec::blind_moment_face> moment{};
  blind_reconstruction_rest_receipt rest{};
  blind_reconstruction_remount_receipt remount{};
  blind_reconstruction_rest_receipt handoff{};
  exact::word final_head{};
  exact::word final_continuation{};
  bool final_can_continue{};
};

}  // namespace holonics::event
