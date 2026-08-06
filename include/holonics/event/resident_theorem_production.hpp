#pragma once

#include <new>
#include <type_traits>

#include <holonics/event/checker_normalization_law.hpp>
#include <holonics/event/checker_pending_deed.hpp>
#include <holonics/event/theorem_production_return.hpp>
#include <holonics/organ/theorem_production_law.hpp>
#include <holonics/receiver/theorem_production_question.hpp>

namespace holonics::event {

class resident_theorem_production final {
 public:
  resident_theorem_production() = delete;
  resident_theorem_production(const resident_theorem_production&) = delete;
  resident_theorem_production& operator=(const resident_theorem_production&) = delete;
  resident_theorem_production(resident_theorem_production&&) = delete;
  resident_theorem_production& operator=(resident_theorem_production&&) = delete;

  HOLONICS_CALLABLE resident_theorem_production(
      const organ::theorem_production_foundation& foundation, std::uint64_t body_seed,
      const body::rest_region* regions, std::uint64_t mathematical_admitted_tally,
      std::uint64_t codec_admitted_tally) noexcept
      : foundation_(foundation), body_(body_seed, regions),
        mathematical_admitted_tally_(mathematical_admitted_tally),
        codec_admitted_tally_(codec_admitted_tally), source_detached_(true) {}

  HOLONICS_CALLABLE resident_theorem_production(
      const organ::theorem_production_foundation& foundation,
      const theorem_production_rest_record& record,
      theorem_production_remount_receipt& receipt) noexcept
      : foundation_(foundation), body_(body::continuing_body::remount(record.body, receipt.body)),
        acquired_(record.acquired), mathematical_admitted_tally_(record.mathematical_admitted_tally),
        codec_admitted_tally_(record.codec_admitted_tally), source_detached_(true) {
    const bool integrity_exact = record.integrity == theorem_production_rest_integrity(record);
    receipt.acquired_fiber = acquired_.identity;
    receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
    receipt.acquired_return_preserved = integrity_exact && acquired_.accepted;
    receipt.source_replayed = receipt.body.source_replay_count != 0;
  }

  [[nodiscard]] HOLONICS_CALLABLE exact::word head() const noexcept { return body_.head(); }
  [[nodiscard]] HOLONICS_CALLABLE bool can_continue() const noexcept { return body_.can_open(); }
  [[nodiscard]] HOLONICS_CALLABLE const organ::acquired_theorem_fiber& acquired() const noexcept {
    return acquired_;
  }

  [[nodiscard]] HOLONICS_CALLABLE organ::theorem_probe_receipt probe(
      const receiver::dependent_theorem_question& question, bool exclude_returned_fiber) const noexcept {
    organ::theorem_probe_receipt receipt{};
    receipt.goal = {question.identity, question.receiver, question.required_returned_fiber,
        question.target_type, question.maximum_dependencies};
    receipt.body_head = body_.head();
    const bool usable = acquired_.accepted && !exclude_returned_fiber &&
        question.required_returned_fiber == acquired_.identity &&
        question.maximum_dependencies >= acquired_.dependency_count;
    if (!usable) { return receipt; }
    receipt.used_returned_fiber = acquired_.identity;
    receipt.consequence = exact::word{question.identity.value() + 50'000U};
    receipt.obstruction = organ::theorem_production_obstruction::none;
    receipt.dependency_count = acquired_.dependency_count;
    receipt.available = true;
    return receipt;
  }

  [[nodiscard]] HOLONICS_CALLABLE bool generate_and_stage(
      const receiver::theorem_production_question& question,
      theorem_production_observation& observation) noexcept {
    auto& generation = observation.generation;
    const organ::theorem_production_goal goal{question.identity, question.receiver,
        question.target_type, question.metavariable, question.maximum_dependencies};
    generation.expansion = organ::expand_theorem_fibers(foundation_, goal);
    if (generation.expansion.obstruction !=
        organ::theorem_production_obstruction::receiver_underdetermined) {
      generation.obstruction = generation.expansion.obstruction;
      return false;
    }
    organ::theorem_proof_fiber selected{};
    if (!organ::restrict_theorem_fibers(generation.expansion, selected)) {
      generation.obstruction = organ::theorem_production_obstruction::no_consequence;
      return false;
    }
    generation.passage = {exact::word{question.identity.value() + 30'000U},
        exact::word{question.identity.value() + 10'000U},
        exact::word{question.identity.value() + 20'000U}, question.target_type,
        selected.rule, selected.lineage, selected.formation, true, true};
    auto continuation = body_.take_continuation();
    observation.generation_commit = body_.commit(body_.head(), 0, 7,
        generation.passage.identity.value(), static_cast<body::linear_continuation&&>(continuation));
    if (observation.generation_commit.state != body::body_change_status::committed) {
      generation.obstruction = organ::theorem_production_obstruction::continuation_refused;
      return false;
    }
    generation.exclusion.generated_statement = generation.passage.statement;
    generation.exclusion.generated_proof = generation.passage.proof;
    generation.exclusion.target_absent_at_mount = true;
    generation.exact_local_expansion = true;
    generation.exact_receiver_restriction = true;
    generation.proof_current_lineaged = true;
    const codec::theorem_production_surface surface{generation.passage.identity,
        generation.passage.statement, generation.passage.proof,
        codec::theorem_surface_form::composed_trace_rebase, true, true};
    if (!codec::render_composed_trace_theorem(surface, observation.formal) ||
        !codec::render_composed_trace_explanation(surface, observation.conversational) ||
        !codec::render_formal_checker_face(observation.formal,
            codec::formal_declaration_form::composed_trace_rebase,
            observation.checker_face)) {
      generation.obstruction = organ::theorem_production_obstruction::render_refused;
      return false;
    }
    checker_outbound_occurrence outbound{body_.head(), exact::word{160'200},
        exact::word{160'201}, exact::word{160'202}, exact::word{160'203},
        exact::word{160'204}, generation.passage.identity, observation.formal.identity};
    ::new (static_cast<void*>(pending_storage_)) checker_pending_deed{
        body_.take_continuation(), outbound};
    pending_live_ = true;
    observation.outbound = outbound;
    observation.checker_stage = checker_stage_status::exact;
    observation.pending_before_process = true;
    generation.obstruction = organ::theorem_production_obstruction::none;
    return true;
  }

  [[nodiscard]] HOLONICS_CALLABLE bool resume(
      const checker_raw_return& raw, theorem_production_observation& observation) noexcept {
    observation.raw = raw;
    auto* pending = live_pending();
    if (pending == nullptr || !pending->resumable()) { return false; }
    const auto expected = pending->outbound();
    auto& typed = observation.typed;
    typed.passage = raw.passage;
    typed.source = raw.source;
    const bool lineage_exact = raw.predecessor == expected.predecessor &&
        raw.event == expected.event && raw.port == expected.expected_return_port &&
        raw.lineage.value() == expected.lineage.value() + 1U &&
        raw.passage == expected.passage && raw.source == expected.source;
    if (!lineage_exact) { typed.state = checker_return_status::passage_mismatch; return false; }
    normalize_checker_return(raw, observation.checker_face, typed);
    const bool accepted = typed.state == checker_return_status::accepted;
    observation.returned_morphology.mathematical_before = mathematical_admitted_tally_;
    observation.returned_morphology.codec_before = codec_admitted_tally_;
    mathematical_admitted_tally_ += accepted ? 3U : 1U;
    codec_admitted_tally_ += accepted ? 2U : 3U;
    const std::uint64_t delta = accepted ? 5U : 4U;
    observation.returned_morphology.commit = body_.commit(expected.predecessor, 0, delta,
        expected.passage.value(), pending->take_continuation());
    pending_live_ = false;
    observation.returned_morphology.mathematical_after = mathematical_admitted_tally_;
    observation.returned_morphology.codec_after = codec_admitted_tally_;
    observation.returned_morphology.returned_difference_applied =
        observation.returned_morphology.commit.state == body::body_change_status::committed;
    observation.pending_after_return = pending_live_;
    observation.passage_preserved = typed.passage == expected.passage &&
        observation.checker_face.passage == expected.passage;
    if (accepted && observation.returned_morphology.returned_difference_applied) {
      const auto& passage = observation.generation.passage;
      acquired_ = {exact::word{passage.identity.value() + 10'000U}, passage.identity,
          passage.statement, passage.proof, raw.event, passage.selected_rule, exact::word{delta},
          observation.generation.expansion.fibers[0].dependency_count, true};
      observation.acquired = acquired_;
    }
    return observation.returned_morphology.returned_difference_applied;
  }

  [[nodiscard]] HOLONICS_CALLABLE theorem_production_rest_receipt rest(
      theorem_production_rest_record& record) noexcept {
    theorem_production_rest_receipt receipt{};
    if (!source_detached_ || !acquired_.accepted || pending_live_) { return receipt; }
    receipt.body = body_.rest(record.body);
    if (!receipt.body.returned) { return receipt; }
    record.acquired = acquired_;
    record.mathematical_admitted_tally = mathematical_admitted_tally_;
    record.codec_admitted_tally = codec_admitted_tally_;
    record.integrity = theorem_production_rest_integrity(record);
    receipt.acquired_fiber = acquired_.identity;
    receipt.integrity = exact::word{record.integrity};
    receipt.source_detached = true;
    receipt.returned = true;
    return receipt;
  }

 private:
  [[nodiscard]] HOLONICS_CALLABLE checker_pending_deed* live_pending() noexcept {
    return pending_live_ ? reinterpret_cast<checker_pending_deed*>(pending_storage_) : nullptr;
  }

  organ::theorem_production_foundation foundation_{};
  body::continuing_body body_;
  organ::acquired_theorem_fiber acquired_{};
  alignas(checker_pending_deed) unsigned char pending_storage_[sizeof(checker_pending_deed)]{};
  std::uint64_t mathematical_admitted_tally_{};
  std::uint64_t codec_admitted_tally_{};
  bool source_detached_{};
  bool pending_live_{};
};

static_assert(std::is_trivially_destructible_v<resident_theorem_production>);

}  // namespace holonics::event
