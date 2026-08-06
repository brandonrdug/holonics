#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/integer_arithmetic.hpp>
#include <holonics/event/resonance_ecology.hpp>
#include <holonics/organ/morphological_surface.hpp>

namespace holonics::event {

/// A factorized population, carried exactly. A parse or transport fiber
/// routinely exceeds a machine word, and collapsing it would destroy the
/// plurality it exists to record.
inline constexpr std::size_t relational_reach_limbs = 8;
using relational_reach = exact::unsigned_integer<relational_reach_limbs>;

/// How a relational channel conducts.
///
/// Co-presence is not contact. A separated coincident face conducts **only after
/// the same complete junction phase has returned through two distinct source
/// pairs** — one return is a coincidence, and the channel stays open until a
/// second, independently lineaged return closes it.
enum class channel_conduct : std::uint8_t {
  copresent,
  source_continuous,
  caused,
  ride,
  open
};

struct relational_channel final {
  std::uint64_t junction_phase{};
  std::uint64_t first_source_pair{};
  std::uint64_t second_source_pair{};
  std::uint64_t recurrence_population{};
  channel_conduct conduct{channel_conduct::open};
};

/// One step of an ordered transport word. The word is **noncommuting and is
/// never collapsed to a scalar**: reversing two steps is a different transport,
/// and no product of them is formed.
struct transport_step final {
  std::uint64_t passage{};
  bool reverse_hand{};
};

inline constexpr std::size_t transport_word_capacity = 16;

/// A thought current. Its populations are carried as **wide integers** because a
/// factorized parse or transport population routinely exceeds a machine word,
/// and collapsing it would destroy the very plurality it records.
struct thought_current final {
  transport_step word[transport_word_capacity]{};
  std::uint8_t word_length{};
  relational_reach factorized_transport{};
  relational_reach factorized_parse{};
  std::uint64_t receiver_horizon{};
  bool closed{};
};

namespace relational_law {

/// Admit a returned junction. The first return records a source pair and leaves
/// the channel OPEN. A second return through a **distinct** source pair closes
/// it as caused. A repeat through the same pair advances recurrence but does not
/// close: repetition through one lineage is not independent testimony.
[[nodiscard]] HOLONICS_CALLABLE constexpr channel_conduct admit_return(
    relational_channel& channel,
    std::uint64_t junction_phase,
    std::uint64_t source_pair) noexcept {
  if (channel.conduct == channel_conduct::open && channel.first_source_pair == 0) {
    channel.junction_phase = junction_phase;
    channel.first_source_pair = source_pair;
    channel.recurrence_population = 1;
    channel.conduct = channel_conduct::copresent;
    return channel.conduct;
  }
  if (channel.junction_phase != junction_phase) {
    channel.conduct = channel_conduct::open;
    return channel.conduct;
  }
  channel.recurrence_population = channel.recurrence_population + 1U;
  if (source_pair == channel.first_source_pair) {
    return channel.conduct;
  }
  channel.second_source_pair = source_pair;
  channel.conduct = channel_conduct::caused;
  return channel.conduct;
}

/// Extend a transport word. Order is retained; a reversed hand is a different
/// step, not the inverse of the same one.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool try_extend(
    thought_current& current,
    std::uint64_t passage,
    bool reverse_hand) noexcept {
  if (current.word_length >= transport_word_capacity) {
    return false;
  }
  current.word[current.word_length] = transport_step{passage, reverse_hand};
  current.word_length = static_cast<std::uint8_t>(current.word_length + 1U);
  return true;
}

/// Two transport words are equal only as ordered sequences. This is exposed so a
/// caller cannot compare them by any commutative summary.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool same_word(
    const thought_current& left,
    const thought_current& right) noexcept {
  if (left.word_length != right.word_length) {
    return false;
  }
  for (std::uint8_t slot = 0; slot < left.word_length; ++slot) {
    if (left.word[slot].passage != right.word[slot].passage ||
        left.word[slot].reverse_hand != right.word[slot].reverse_hand) {
      return false;
    }
  }
  return true;
}

/// Does the word return to its origin with a nontrivial transport? A closed
/// route that returns a changed frame carries **holonomy**, which is retained
/// symbolically. No numeric connection coefficient is invented for it.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool carries_holonomy(
    const thought_current& current) noexcept {
  if (current.word_length < 2) {
    return false;
  }
  const transport_step first = current.word[0];
  const transport_step last = current.word[current.word_length - 1U];
  return first.passage == last.passage && first.reverse_hand != last.reverse_hand;
}

/// Join two factorized populations without enumerating either. The product of
/// two plural fibers is formed exactly in the wide carrier; nothing is sampled
/// and nothing saturates.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool try_join(
    const relational_reach& left,
    const relational_reach& right,
    relational_reach& joined) noexcept {
  const auto sum = exact::add(left, right);
  if (!sum.accepted()) {
    return false;
  }
  joined = sum.value;
  return true;
}

}  // namespace relational_law
}  // namespace holonics::event
