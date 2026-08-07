#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <fcntl.h>
#include <sys/wait.h>
#include <unistd.h>

#include <holonics/apparatus/lean_checker_process.hpp>

namespace holonics::apparatus {
namespace {

constexpr std::uint64_t fold_offset = 14'695'981'039'346'656'037ULL;
constexpr std::uint64_t fold_prime = 1'099'511'628'211ULL;

struct file_testimony final {
  std::uint64_t fold{fold_offset};
  std::uint32_t bytes{};
};

[[nodiscard]] bool write_all(int descriptor, const char* bytes, std::size_t count) noexcept {
  std::size_t written = 0;
  while (written < count) {
    const auto result = ::write(descriptor, bytes + written, count - written);
    if (result < 0 && errno == EINTR) { continue; }
    if (result <= 0) { return false; }
    written += static_cast<std::size_t>(result);
  }
  return true;
}

[[nodiscard]] bool read_file(const char* path, char* capture, std::size_t capacity,
    file_testimony& testimony) noexcept {
  const int descriptor = ::open(path, O_RDONLY);
  if (descriptor < 0) { return false; }
  char buffer[4096]{};
  std::size_t captured = 0;
  for (;;) {
    const auto result = ::read(descriptor, buffer, sizeof(buffer));
    if (result < 0 && errno == EINTR) { continue; }
    if (result < 0) { static_cast<void>(::close(descriptor)); return false; }
    if (result == 0) { break; }
    const auto count = static_cast<std::size_t>(result);
    if (testimony.bytes > UINT32_MAX - count ||
        (capture != nullptr && captured + count > capacity)) {
      static_cast<void>(::close(descriptor)); return false;
    }
    for (std::size_t slot = 0; slot < count; ++slot) {
      testimony.fold ^= static_cast<unsigned char>(buffer[slot]);
      testimony.fold *= fold_prime;
      if (capture != nullptr) { capture[captured++] = buffer[slot]; }
    }
    testimony.bytes += static_cast<std::uint32_t>(count);
  }
  return ::close(descriptor) == 0;
}

template<std::size_t Capacity, std::size_t Pattern>
[[nodiscard]] bool contains(const char (&bytes)[Capacity], std::uint32_t used,
    const char (&pattern)[Pattern]) noexcept {
  constexpr std::size_t payload = Pattern - 1U;
  if (payload == 0 || used < payload) { return false; }
  for (std::size_t start = 0; start + payload <= used; ++start) {
    bool same = true;
    for (std::size_t slot = 0; slot < payload; ++slot) {
      same = same && bytes[start + slot] == pattern[slot];
    }
    if (same) { return true; }
  }
  return false;
}

[[nodiscard]] bool capture_environment(const lean_process_configuration& configuration,
    lean_environment_manifest& manifest) noexcept {
  char toolchain[128]{};
  char lake_manifest[4096]{};
  file_testimony toolchain_file{};
  file_testimony manifest_file{};
  file_testimony lake_file{};
  file_testimony lean_file{};
  if (!read_file(configuration.toolchain_path, toolchain, sizeof(toolchain), toolchain_file) ||
      !read_file(configuration.lake_manifest_path, lake_manifest, sizeof(lake_manifest), manifest_file) ||
      !read_file("/usr/bin/lake", nullptr, 0, lake_file) ||
      !read_file("/usr/bin/lean", nullptr, 0, lean_file)) {
    return false;
  }
  manifest = {toolchain_file.fold, manifest_file.fold, lake_file.fold, lean_file.fold,
      toolchain_file.bytes, manifest_file.bytes, lake_file.bytes, lean_file.bytes,
      contains(toolchain, toolchain_file.bytes, "leanprover/lean4:v4.27") &&
          contains(toolchain, toolchain_file.bytes, ".0\n"),
      contains(lake_manifest, manifest_file.bytes,
          "a3a10db0e9d66acbebf76c5e6a135066525ac900")};
  return manifest.pinned_lean_4_27 && manifest.pinned_mathlib_revision;
}

[[nodiscard]] bool write_source(
    const char* path, const char* bytes, std::size_t byte_count) noexcept {
  const int descriptor = ::open(path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
  if (descriptor < 0) { return false; }
  const bool wrote = write_all(descriptor, bytes, byte_count);
  return ::close(descriptor) == 0 && wrote;
}

[[nodiscard]] bool invoke(const lean_process_configuration& configuration,
    std::int32_t& exit_status) noexcept {
  const int standard_output = ::open(
      configuration.stdout_path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
  const int standard_error = ::open(
      configuration.stderr_path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
  if (standard_output < 0 || standard_error < 0) {
    if (standard_output >= 0) { static_cast<void>(::close(standard_output)); }
    if (standard_error >= 0) { static_cast<void>(::close(standard_error)); }
    return false;
  }
  const pid_t child = ::fork();
  if (child == 0) {
    if (::chdir(configuration.working_directory) != 0 ||
        ::dup2(standard_output, STDOUT_FILENO) < 0 ||
        ::dup2(standard_error, STDERR_FILENO) < 0) {
      ::_exit(126);
    }
    static_cast<void>(::close(standard_output));
    static_cast<void>(::close(standard_error));
    ::execl("/usr/bin/lake", "lake", "env", "lean", "-R", configuration.source_root, "-o",
        configuration.produced_artifact_path, configuration.source_path,
        static_cast<char*>(nullptr));
    ::_exit(127);
  }
  static_cast<void>(::close(standard_output));
  static_cast<void>(::close(standard_error));
  if (child < 0) { return false; }
  int status = 0;
  pid_t waited = 0;
  do { waited = ::waitpid(child, &status, 0); } while (waited < 0 && errno == EINTR);
  if (waited != child || !WIFEXITED(status)) { return false; }
  exit_status = static_cast<std::int32_t>(WEXITSTATUS(status));
  return true;
}

}  // namespace

lean_process_receipt run_lean_checker_source(const lean_source_view& source,
    const event::checker_outbound_occurrence& outbound,
    const lean_process_configuration& configuration,
    event::checker_raw_return& returned) noexcept {
  lean_process_receipt receipt{};
  if (source.bytes == nullptr || source.byte_count == 0 ||
      source.passage != outbound.passage || source.generated_source != outbound.source ||
      configuration.working_directory == nullptr || configuration.toolchain_path == nullptr ||
      configuration.lake_manifest_path == nullptr || configuration.source_path == nullptr ||
      configuration.produced_artifact_path == nullptr || configuration.stdout_path == nullptr ||
      configuration.stderr_path == nullptr || configuration.source_root == nullptr) {
    return receipt;
  }
  if (!capture_environment(configuration, receipt.environment)) {
    receipt.state = lean_process_status::environment_refused; return receipt;
  }
  if (!write_source(configuration.source_path, source.bytes, source.byte_count)) {
    receipt.state = lean_process_status::source_refused; return receipt;
  }
  returned = {outbound.predecessor, outbound.event, outbound.expected_return_port,
      exact::word{outbound.lineage.value() + 1U}, outbound.passage, outbound.source};
  returned.launched = true;
  if (!invoke(configuration, returned.exit_status)) {
    receipt.state = lean_process_status::process_refused; return receipt;
  }
  returned.exited = true;
  file_testimony source_file{};
  file_testimony standard_output{};
  file_testimony standard_error{};
  file_testimony produced{};
  if (!read_file(configuration.source_path, nullptr, 0, source_file) ||
      !read_file(configuration.stdout_path, returned.standard_output,
          event::checker_message_capacity, standard_output) ||
      !read_file(configuration.stderr_path, returned.standard_error,
          event::checker_message_capacity, standard_error)) {
    receipt.state = lean_process_status::capture_refused; return receipt;
  }
  if (returned.exit_status == 0 &&
      !read_file(configuration.produced_artifact_path, nullptr, 0, produced)) {
    receipt.state = lean_process_status::capture_refused; return receipt;
  }
  if (standard_output.bytes > UINT16_MAX || standard_error.bytes > UINT16_MAX) {
    receipt.state = lean_process_status::capacity_refused; return receipt;
  }
  returned.stdout_bytes = static_cast<std::uint16_t>(standard_output.bytes);
  returned.stderr_bytes = static_cast<std::uint16_t>(standard_error.bytes);
  returned.produced_artifact_bytes = produced.bytes;
  returned.source_fold = source_file.fold;
  returned.produced_artifact_fold = produced.fold;
  receipt.state = lean_process_status::returned;
  receipt.invocation = exact::word{160'105};
  receipt.source_bytes = exact::word{source_file.bytes};
  receipt.stdout_bytes = exact::word{standard_output.bytes};
  receipt.stderr_bytes = exact::word{standard_error.bytes};
  receipt.produced_artifact_bytes = exact::word{produced.bytes};
  receipt.exterior_process_calls = exact::word{1};
  receipt.host_semantic_events = exact::word{0};
  receipt.named_lake_env_lean = true;
  receipt.raw_bytes_returned = true;
  return receipt;
}

lean_process_receipt run_lean_checker_process(const codec::formal_checker_face& face,
    const event::checker_outbound_occurrence& outbound,
    const lean_process_configuration& configuration,
    event::checker_raw_return& returned) noexcept {
  if (face.byte_count > codec::formal_checker_face_capacity) { return {}; }
  const lean_source_view source{face.passage, face.generated_source, face.bytes, face.byte_count};
  return run_lean_checker_source(source, outbound, configuration, returned);
}

}  // namespace holonics::apparatus
