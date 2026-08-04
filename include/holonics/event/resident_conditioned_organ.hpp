#pragma once

#include <cstddef>
#include <cstdint>
#include <type_traits>

#include <holonics/body/continuing_body.hpp>
#include <holonics/event/conditioned_organ_rest.hpp>
#include <holonics/organ/conditioning_law.hpp>
#include <holonics/receiver/conditioning_probe.hpp>

namespace holonics::event {

class resident_conditioned_organ final {
 public:
  resident_conditioned_organ() = delete;
  resident_conditioned_organ(const resident_conditioned_organ&) = delete;
  resident_conditioned_organ& operator=(const resident_conditioned_organ&) = delete;
  resident_conditioned_organ(resident_conditioned_organ&&) = delete;
  resident_conditioned_organ& operator=(resident_conditioned_organ&&) = delete;

  HOLONICS_CALLABLE resident_conditioned_organ(
      const organ::navigation_morphology& morphology,
      std::uint64_t body_seed,
      const body::rest_region* regions,
      bool source_detached) noexcept
      : morphology_(morphology), body_(body_seed, regions), source_detached_(source_detached),
        obstruction_(organ::valid_morphology(morphology)
            ? organ::conditioning_obstruction::none
            : organ::conditioning_obstruction::invalid_morphology) {}

  HOLONICS_CALLABLE resident_conditioned_organ(
      const conditioned_organ_rest_record& record,
      conditioned_organ_remount_receipt& receipt) noexcept
      : morphology_(record.morphology),
        body_(body::continuing_body::remount(record.body, receipt.body)), source_detached_(true),
        obstruction_(organ::valid_morphology(record.morphology) && receipt.body.returned
            ? organ::conditioning_obstruction::none
            : organ::conditioning_obstruction::rest_refused) {
    receipt.obstruction = obstruction_;
    receipt.organ = morphology_.identity;
    receipt.response_weight = morphology_.response_weight;
    receipt.same_body = receipt.body.head == body_.head();
    receipt.source_replayed = receipt.body.source_replay_count != 0;
  }

  [[nodiscard]] HOLONICS_CALLABLE organ::conditioning_obstruction obstruction() const noexcept {
    return obstruction_;
  }
  [[nodiscard]] HOLONICS_CALLABLE exact::word head() const noexcept { return body_.head(); }
  [[nodiscard]] HOLONICS_CALLABLE bool can_continue() const noexcept { return body_.can_open(); }
  [[nodiscard]] HOLONICS_CALLABLE const body::rest_region& region(std::size_t slot) const noexcept {
    return body_.region(slot);
  }
  [[nodiscard]] HOLONICS_CALLABLE const organ::navigation_morphology& morphology() const noexcept {
    return morphology_;
  }

  [[nodiscard]] HOLONICS_CALLABLE organ::mounting_receipt mounting() const noexcept {
    organ::mounting_receipt result{};
    result.organ = morphology_.identity;
    result.provenance = morphology_.provenance;
    result.before = morphology_;
    result.after = morphology_;
    result.inherited = true;
    return result;
  }

  [[nodiscard]] HOLONICS_CALLABLE receiver::conditioning_probe_receipt probe(
      const receiver::conditioning_question& question) const noexcept {
    receiver::conditioning_probe_receipt result{};
    result.question = question;
    result.body_head = body_.head();
    result.organ = morphology_.identity;
    result.morphology_response_weight = morphology_.response_weight;
    organ::navigation_consequence local{};
    static_cast<void>(organ::respond(morphology_, question.support.value(),
        question.path_length.value(), question.unknown_count.value(), local));
    result.consequence.response = local.response;
    result.consequence.incidence = local.incidence;
    result.consequence.transport = local.transport;
    result.consequence.codec = local.codec;
    result.consequence.obstruction = local.obstruction;
    return result;
  }

  [[nodiscard]] HOLONICS_CALLABLE organ::exposure_receipt expose(
      const organ::exposure_occurrence& occurrence) const noexcept {
    organ::exposure_receipt result{};
    result.occurrence = occurrence;
    result.before = morphology_;
    result.after = morphology_;
    result.crossing_material = true;
    static_cast<void>(organ::respond(morphology_, occurrence.support.value(),
        occurrence.path_length.value(), occurrence.unknown_count.value(), result.received));
    return result;
  }

  [[nodiscard]] HOLONICS_CALLABLE organ::reference_receipt consult(
      const organ::reference_occurrence& occurrence) const noexcept {
    organ::reference_receipt result{};
    result.occurrence = occurrence;
    result.consulted.response = occurrence.testimony;
    result.separately_retained_testimony = true;
    return result;
  }

  [[nodiscard]] HOLONICS_CALLABLE organ::training_receipt train(
      const organ::training_return& returned) noexcept {
    organ::training_receipt receipt{};
    receipt.returned = returned;
    receipt.predecessor = body_.head();
    receipt.before = morphology_;
    organ::navigation_morphology after{};
    if (obstruction_ != organ::conditioning_obstruction::none ||
        !organ::returned_delta(morphology_, returned, receipt.delta, after)) {
      receipt.obstruction = organ::conditioning_obstruction::stale_return;
      return receipt;
    }
    std::uint64_t morphology_delta = 0;
    if (!organ::exact_add(morphology_delta, receipt.delta.response_weight.value(), morphology_delta) ||
        !organ::exact_add(morphology_delta, receipt.delta.transport_weight.value(), morphology_delta) ||
        !organ::exact_add(morphology_delta, receipt.delta.incidence_gate.value(), morphology_delta) ||
        !organ::exact_add(morphology_delta, receipt.delta.codec_bias.value(), morphology_delta) ||
        !organ::exact_add(morphology_delta, receipt.delta.obstruction_threshold.value(),
            morphology_delta)) {
      receipt.obstruction = organ::conditioning_obstruction::arithmetic_refused;
      return receipt;
    }
    auto continuation = body_.take_continuation();
    const auto commit = body_.commit(body_.head(), 0, morphology_delta,
        after.response_weight.value(), static_cast<body::linear_continuation&&>(continuation));
    if (commit.state != body::body_change_status::committed) {
      receipt.obstruction = organ::conditioning_obstruction::continuation_refused;
      return receipt;
    }
    receipt.continuation = commit.continuation_before;
    receipt.successor = commit.successor;
    receipt.after = after;
    receipt.founded_by_return = true;
    receipt.committed = true;
    morphology_ = after;
    return receipt;
  }

  [[nodiscard]] HOLONICS_CALLABLE conditioned_organ_rest_receipt rest(
      conditioned_organ_rest_record& record) noexcept {
    conditioned_organ_rest_receipt receipt{};
    if (obstruction_ != organ::conditioning_obstruction::none || !source_detached_) {
      receipt.obstruction = organ::conditioning_obstruction::rest_refused;
      return receipt;
    }
    receipt.body = body_.rest(record.body);
    if (!receipt.body.returned) {
      receipt.obstruction = organ::conditioning_obstruction::rest_refused;
      return receipt;
    }
    record.morphology = morphology_;
    receipt.organ = morphology_.identity;
    receipt.response_weight = morphology_.response_weight;
    receipt.source_detached = true;
    return receipt;
  }

 private:
  organ::navigation_morphology morphology_{};
  body::continuing_body body_;
  bool source_detached_{};
  organ::conditioning_obstruction obstruction_{organ::conditioning_obstruction::invalid_morphology};
};

static_assert(std::is_trivially_destructible_v<resident_conditioned_organ>);

}  // namespace holonics::event
