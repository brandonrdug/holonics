#pragma once

#include <new>
#include <type_traits>

#include <holonics/event/checker_normalization_law.hpp>
#include <holonics/event/checker_pending_deed.hpp>
#include <holonics/event/terminal_theorem_return.hpp>

namespace holonics::event {

class resident_dependent_theorem_production final {
 public:
  resident_dependent_theorem_production() = delete;
  resident_dependent_theorem_production(const resident_dependent_theorem_production&) = delete;
  resident_dependent_theorem_production& operator=(
      const resident_dependent_theorem_production&) = delete;
  resident_dependent_theorem_production(resident_dependent_theorem_production&&) = delete;
  resident_dependent_theorem_production& operator=(
      resident_dependent_theorem_production&&) = delete;

  HOLONICS_CALLABLE resident_dependent_theorem_production(
      const organ::theorem_production_foundation& foundation,
      const theorem_production_rest_record& record,
      theorem_production_remount_receipt& receipt) noexcept
      : foundation_(foundation), body_(body::continuing_body::remount(record.body, receipt.body)),
        first_(record.acquired), mathematical_admitted_tally_(record.mathematical_admitted_tally),
        codec_admitted_tally_(record.codec_admitted_tally), source_detached_(true) {
    const bool exact = record.integrity == theorem_production_rest_integrity(record);
    receipt.acquired_fiber = first_.identity;
    receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
    receipt.acquired_return_preserved = exact && first_.accepted;
    receipt.source_replayed = receipt.body.source_replay_count != 0;
  }

  HOLONICS_CALLABLE resident_dependent_theorem_production(
      const organ::theorem_production_foundation& foundation,
      const terminal_theorem_rest_record& record,
      terminal_theorem_remount_receipt& receipt) noexcept
      : foundation_(foundation), body_(body::continuing_body::remount(record.body, receipt.body)),
        first_(record.first), second_(record.second),
        mathematical_admitted_tally_(record.mathematical_admitted_tally),
        codec_admitted_tally_(record.codec_admitted_tally), source_detached_(true) {
    const bool exact = record.integrity == terminal_theorem_rest_integrity(record);
    receipt.first_fiber = first_.identity;
    receipt.second_fiber = second_.identity;
    receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
    receipt.both_returns_preserved = exact && first_.accepted && second_.accepted;
    receipt.source_replayed = receipt.body.source_replay_count != 0;
  }

  [[nodiscard]] HOLONICS_CALLABLE exact::word head() const noexcept { return body_.head(); }
  [[nodiscard]] HOLONICS_CALLABLE bool can_continue() const noexcept { return body_.can_open(); }

  [[nodiscard]] HOLONICS_CALLABLE bool attempt(
      const dependent_theorem_setup& setup,
      dependent_theorem_generation_receipt& generation) const noexcept {
    return form_dependent_theorem(foundation_, first_, setup, generation);
  }

  [[nodiscard]] HOLONICS_CALLABLE bool generate_and_stage(
      const dependent_theorem_setup& setup,
      terminal_theorem_observation& observation) noexcept {
    auto& generation = observation.generation;
    if (!attempt(setup, generation)) { return false; }
    const codec::theorem_production_surface surface{generation.passage.identity,
        generation.passage.statement, generation.passage.proof,
        codec::theorem_surface_form::returned_fiber_extension, true, true};
    if (!codec::render_returned_fiber_theorem(surface, observation.formal) ||
        !codec::render_returned_fiber_explanation(surface, observation.conversational) ||
        !codec::render_formal_checker_face(observation.formal,
            codec::formal_declaration_form::returned_fiber_extension,
            observation.checker_face)) {
      generation.obstruction = organ::theorem_production_obstruction::render_refused;
      return false;
    }
    auto continuation = body_.take_continuation();
    observation.generation_commit = body_.commit(body_.head(), 0, 7,
        generation.passage.identity.value(),
        static_cast<body::linear_continuation&&>(continuation));
    if (observation.generation_commit.state != body::body_change_status::committed) {
      generation.obstruction = organ::theorem_production_obstruction::continuation_refused;
      return false;
    }
    checker_outbound_occurrence outbound{body_.head(), exact::word{160'300},
        exact::word{160'301}, exact::word{160'302}, exact::word{160'303},
        exact::word{160'304}, generation.passage.identity, observation.formal.identity};
    ::new (static_cast<void*>(pending_storage_)) checker_pending_deed{
        body_.take_continuation(), outbound};
    pending_live_ = true;
    observation.outbound = outbound;
    observation.checker_stage = checker_stage_status::exact;
    observation.pending_before_process = true;
    return true;
  }

  [[nodiscard]] HOLONICS_CALLABLE bool resume(
      const checker_raw_return& raw,
      terminal_theorem_observation& observation) noexcept {
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
    auto& morphology = observation.returned_morphology;
    morphology.mathematical_before = mathematical_admitted_tally_;
    morphology.codec_before = codec_admitted_tally_;
    mathematical_admitted_tally_ += accepted ? 3U : 1U;
    codec_admitted_tally_ += accepted ? 2U : 3U;
    const std::uint64_t delta = accepted ? 5U : 4U;
    morphology.commit = body_.commit(expected.predecessor, 0, delta,
        expected.passage.value(), pending->take_continuation());
    pending_live_ = false;
    morphology.mathematical_after = mathematical_admitted_tally_;
    morphology.codec_after = codec_admitted_tally_;
    morphology.returned_difference_applied =
        morphology.commit.state == body::body_change_status::committed;
    observation.pending_after_return = pending_live_;
    observation.passage_preserved = typed.passage == expected.passage &&
        observation.checker_face.passage == expected.passage;
    if (accepted && morphology.returned_difference_applied) {
      const auto& passage = observation.generation.passage;
      second_ = {observation.generation.selected_witness, passage.identity,
          passage.statement, passage.proof, raw.event, passage.selected_rule,
          exact::word{delta}, observation.generation.selected.dependency_count, true};
      observation.second_acquired = second_;
    }
    return morphology.returned_difference_applied;
  }

  [[nodiscard]] HOLONICS_CALLABLE terminal_theorem_rest_receipt rest(
      terminal_theorem_rest_record& record) noexcept {
    terminal_theorem_rest_receipt receipt{};
    if (!source_detached_ || !first_.accepted || !second_.accepted || pending_live_) {
      return receipt;
    }
    receipt.body = body_.rest(record.body);
    if (!receipt.body.returned) { return receipt; }
    record.first = first_;
    record.second = second_;
    record.mathematical_admitted_tally = mathematical_admitted_tally_;
    record.codec_admitted_tally = codec_admitted_tally_;
    record.integrity = terminal_theorem_rest_integrity(record);
    receipt.first_fiber = first_.identity;
    receipt.second_fiber = second_.identity;
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
  organ::acquired_theorem_fiber first_{};
  organ::acquired_theorem_fiber second_{};
  alignas(checker_pending_deed) unsigned char pending_storage_[sizeof(checker_pending_deed)]{};
  std::uint64_t mathematical_admitted_tally_{};
  std::uint64_t codec_admitted_tally_{};
  bool source_detached_{};
  bool pending_live_{};
};

static_assert(std::is_trivially_destructible_v<resident_dependent_theorem_production>);

}  // namespace holonics::event
