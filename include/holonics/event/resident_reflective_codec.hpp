#pragma once

#include <cstdint>
#include <type_traits>

#include <holonics/body/continuing_body.hpp>
#include <holonics/codec/reflection_law.hpp>
#include <holonics/event/reflective_codec_rest.hpp>

namespace holonics::event {

class resident_reflective_codec final {
 public:
  resident_reflective_codec() = delete;
  resident_reflective_codec(const resident_reflective_codec&) = delete;
  resident_reflective_codec& operator=(const resident_reflective_codec&) = delete;
  resident_reflective_codec(resident_reflective_codec&&) = delete;
  resident_reflective_codec& operator=(resident_reflective_codec&&) = delete;

  HOLONICS_CALLABLE resident_reflective_codec(
      const codec::codec_environment& environment,
      std::uint64_t body_seed,
      const body::rest_region* regions,
      bool source_detached) noexcept
      : environment_(environment), body_(body_seed, regions), source_detached_(source_detached),
        obstruction_(codec::valid_environment(environment)
            ? codec::codec_obstruction::none
            : codec::codec_obstruction::invalid_environment) {}

  HOLONICS_CALLABLE resident_reflective_codec(
      const reflective_codec_rest_record& record,
      reflective_codec_remount_receipt& receipt) noexcept
      : environment_(record.environment), body_(body::continuing_body::remount(record.body, receipt.body)),
        source_detached_(true), obstruction_(codec::valid_environment(record.environment) &&
            receipt.body.returned ? codec::codec_obstruction::none
                                  : codec::codec_obstruction::rest_refused) {
    receipt.obstruction = obstruction_;
    receipt.environment = environment_.identity;
    receipt.program = environment_.operative.identity;
    receipt.version = environment_.operative.version;
    receipt.same_body = receipt.body.head == body_.head();
    receipt.source_replayed = receipt.body.source_replay_count != 0;
  }

  [[nodiscard]] HOLONICS_CALLABLE codec::codec_obstruction obstruction() const noexcept {
    return obstruction_;
  }
  [[nodiscard]] HOLONICS_CALLABLE exact::word head() const noexcept { return body_.head(); }
  [[nodiscard]] HOLONICS_CALLABLE const codec::codec_environment& environment() const noexcept {
    return environment_;
  }
  [[nodiscard]] HOLONICS_CALLABLE bool source_detached() const noexcept { return source_detached_; }
  [[nodiscard]] HOLONICS_CALLABLE const body::rest_region& region(std::size_t slot) const noexcept {
    return body_.region(slot);
  }

  [[nodiscard]] HOLONICS_CALLABLE codec::codec_behavior behavior(
      codec::surface_packet probe,
      exact::word render_core,
      std::uint64_t occurrence_seed,
      std::uint64_t lineage_seed) const noexcept {
    codec::codec_behavior result{};
    result.parsed = codec::parse_crossing(environment_, environment_.operative, probe,
        body_.head(), exact::word{occurrence_seed}, exact::word{lineage_seed});
    result.rendered = codec::render_crossing(environment_, environment_.operative, render_core,
        body_.head(), exact::word{occurrence_seed + 1U}, exact::word{lineage_seed + 1U});
    result.transduced = codec::transduce_crossing(environment_, environment_.operative,
        environment_.unrelated, probe, body_.head(), exact::word{occurrence_seed + 2U},
        exact::word{lineage_seed + 2U});
    result.unrelated_parsed = codec::parse_crossing(environment_, environment_.unrelated,
        result.transduced.output, body_.head(), exact::word{occurrence_seed + 3U},
        exact::word{lineage_seed + 3U});
    return result;
  }

  [[nodiscard]] HOLONICS_CALLABLE codec::codec_reflection reflect(
      exact::word occurrence,
      exact::word lineage) const noexcept {
    codec::codec_reflection result{};
    result.obstruction = obstruction_;
    result.occurrence = occurrence;
    result.lineage = lineage;
    result.operative = environment_.operative;
    result.environment = environment_.identity;
    result.inherited_provenance = environment_.inherited_provenance;
    result.continuation.body_head = body_.head();
    result.continuation.pending_serial = body_.continuation_serial();
    result.continuation.pending = body_.can_open();
    result.continuation.reified_view_only = true;
    return result;
  }

  [[nodiscard]] HOLONICS_CALLABLE codec::codec_revision_return apply_revision(
      const codec::codec_revision_request& request,
      const codec::codec_reflection& reflection,
      codec::surface_packet probe) noexcept {
    codec::codec_revision_return result{};
    result.occurrence = request.occurrence;
    result.return_port = request.return_port;
    result.lineage = request.lineage;
    result.predecessor = body_.head();
    result.reflected_program = reflection.operative.identity;
    result.old_version = environment_.operative.version;
    result.new_version = request.next_version;
    result.old_bias = environment_.operative.bias;
    result.new_bias = request.next_bias;
    result.reflected_continuation = reflection.continuation;
    if (obstruction_ != codec::codec_obstruction::none ||
        reflection.obstruction != codec::codec_obstruction::none ||
        reflection.environment != environment_.identity ||
        !codec::equal_program(reflection.operative, environment_.operative) ||
        reflection.continuation.body_head != body_.head() ||
        reflection.continuation.pending_serial != body_.continuation_serial() ||
        !reflection.continuation.pending || !reflection.continuation.reified_view_only) {
      result.obstruction = codec::codec_obstruction::stale_reflection;
      return result;
    }
    if (request.occurrence.value() == 0 || request.return_port.value() == 0 ||
        request.lineage.value() == 0 || request.next_version.value() <= result.old_version.value() ||
        request.next_bias.value() <= result.old_bias.value()) {
      result.obstruction = codec::codec_obstruction::foreign_revision;
      return result;
    }
    auto revised = environment_.operative;
    revised.version = request.next_version;
    revised.bias = request.next_bias;
    exact::word revised_probe{};
    if (codec::parse_surface(revised, probe, revised_probe) != codec::codec_obstruction::none) {
      result.obstruction = codec::codec_obstruction::arithmetic_refused;
      return result;
    }
    const std::uint64_t admitted_tally_delta = request.next_bias.value() - result.old_bias.value();
    auto continuation = body_.take_continuation();
    const auto commit = body_.commit(body_.head(), 0, admitted_tally_delta,
        revised_probe.value(), static_cast<body::linear_continuation&&>(continuation));
    if (commit.state != body::body_change_status::committed) {
      result.obstruction = codec::codec_obstruction::continuation_refused;
      return result;
    }
    result.same_continuation = commit.continuation_before ==
        reflection.continuation.pending_serial;
    result.successor = commit.successor;
    result.law_changed = revised.bias != environment_.operative.bias;
    result.committed = result.same_continuation && result.law_changed;
    environment_.operative = revised;
    return result;
  }

  [[nodiscard]] HOLONICS_CALLABLE reflective_codec_rest_receipt rest(
      reflective_codec_rest_record& record) noexcept {
    reflective_codec_rest_receipt receipt{};
    if (obstruction_ != codec::codec_obstruction::none || !source_detached_) {
      receipt.obstruction = codec::codec_obstruction::rest_refused;
      return receipt;
    }
    receipt.body = body_.rest(record.body);
    if (!receipt.body.returned) {
      receipt.obstruction = codec::codec_obstruction::rest_refused;
      return receipt;
    }
    record.environment = environment_;
    receipt.environment = environment_.identity;
    receipt.program = environment_.operative.identity;
    receipt.version = environment_.operative.version;
    receipt.source_detached = true;
    return receipt;
  }

 private:
  codec::codec_environment environment_{};
  body::continuing_body body_;
  bool source_detached_{};
  codec::codec_obstruction obstruction_{codec::codec_obstruction::invalid_environment};
};

static_assert(std::is_trivially_destructible_v<resident_reflective_codec>);

}  // namespace holonics::event
