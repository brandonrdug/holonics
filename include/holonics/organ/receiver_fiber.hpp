#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/structure/local_population.hpp>

namespace holonics::organ {

inline constexpr std::size_t fiber_word_capacity = 8;

/// The universal exact identity carrier for germs, sources, roles, and paths.
///
/// A fiber identity is a declared schema plus an exact word sequence. **It is not
/// a hash.** Two identities are equal exactly when their schema and their
/// complete words agree, so an identity can never collide by digest, and the
/// words it carries remain readable rather than folded away.
struct receiver_fiber_identity final {
  std::uint64_t schema{};
  std::uint32_t words[fiber_word_capacity]{};
  std::uint8_t used{};
};

/// Declared schemas. Each names the kind of thing an identity identifies; two
/// identities with equal words but different schemas are different fibers.
inline constexpr std::uint64_t role_schema = 0x5245'534F'524F'4C45ULL;
inline constexpr std::uint64_t continuation_target_schema = 0x5245'534F'4E45'5854ULL;
inline constexpr std::uint64_t emanated_path_schema = 0x5245'534F'454D'414EULL;
inline constexpr std::uint64_t germ_receiver_chart = 0x5245'534F'4745'524DULL;
inline constexpr std::uint64_t capacitive_receiver_chart = 0x5245'534F'4341'5041ULL;

/// Role words. The first three name what a fiber is doing in an occurrence; the
/// last three carry **causal provenance**, which is retained permanently so that
/// inherited material, a receiver's question, and the body's own generated
/// successor never become one lineage merely because their germ paths agree.
inline constexpr std::uint32_t germ_role_word = 1;
inline constexpr std::uint32_t informant_role_word = 2;
inline constexpr std::uint32_t continuation_source_role_word = 3;
inline constexpr std::uint32_t inherited_origin_role_word = 4;
inline constexpr std::uint32_t question_origin_role_word = 5;
inline constexpr std::uint32_t emanated_origin_role_word = 6;

enum class occurrence_origin : std::uint8_t {
  inherited,
  receiver_question,
  self_emanated
};

namespace fiber_law {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool admitted(
    const receiver_fiber_identity& value) noexcept {
  return value.schema != 0 && value.used > 0 && value.used <= fiber_word_capacity;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal(
    const receiver_fiber_identity& left,
    const receiver_fiber_identity& right) noexcept {
  if (left.schema != right.schema || left.used != right.used) {
    return false;
  }
  for (std::uint8_t slot = 0; slot < left.used; ++slot) {
    if (left.words[slot] != right.words[slot]) {
      return false;
    }
  }
  return true;
}

/// Total order for registry keying. Lexicographic over schema, length, words.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool precedes(
    const receiver_fiber_identity& left,
    const receiver_fiber_identity& right) noexcept {
  if (left.schema != right.schema) {
    return left.schema < right.schema;
  }
  if (left.used != right.used) {
    return left.used < right.used;
  }
  for (std::uint8_t slot = 0; slot < left.used; ++slot) {
    if (left.words[slot] != right.words[slot]) {
      return left.words[slot] < right.words[slot];
    }
  }
  return false;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr receiver_fiber_identity role_fiber(
    std::uint32_t role) noexcept {
  receiver_fiber_identity value{};
  value.schema = role_schema;
  value.words[0] = role;
  value.used = 1;
  return value;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t origin_role_word(
    occurrence_origin origin) noexcept {
  switch (origin) {
    case occurrence_origin::inherited: return inherited_origin_role_word;
    case occurrence_origin::receiver_question: return question_origin_role_word;
    case occurrence_origin::self_emanated: return emanated_origin_role_word;
  }
  return inherited_origin_role_word;
}

/// The continuation target role carries the SOURCE germ's identity inside it, so
/// a continuation boundary names which germ it continues from. Two continuations
/// into the same target from different sources are different fibers.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool try_continuation_target_role(
    const receiver_fiber_identity& source,
    receiver_fiber_identity& target) noexcept {
  if (!admitted(source) || source.used + 1U > fiber_word_capacity) {
    return false;
  }
  target = receiver_fiber_identity{};
  target.schema = continuation_target_schema;
  target.words[0] = continuation_source_role_word;
  for (std::uint8_t slot = 0; slot < source.used; ++slot) {
    target.words[slot + 1U] = source.words[slot];
  }
  target.used = static_cast<std::uint8_t>(source.used + 1U);
  return true;
}

/// **The emanated path fiber.** A generated branch re-enters carrying the
/// complete exact word sequence of the path that produced it — never a digest.
/// This changes provenance, not morphology: an inherited path and a generated
/// path may recur through equal germ boundaries without becoming one occurrence.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool try_emanated_path_fiber(
    const std::uint32_t* path_words,
    std::uint8_t count,
    receiver_fiber_identity& emanated) noexcept {
  if (count == 0 || count > fiber_word_capacity) {
    return false;
  }
  emanated = receiver_fiber_identity{};
  emanated.schema = emanated_path_schema;
  for (std::uint8_t slot = 0; slot < count; ++slot) {
    emanated.words[slot] = path_words[slot];
  }
  emanated.used = count;
  return true;
}

}  // namespace fiber_law
}  // namespace holonics::organ
