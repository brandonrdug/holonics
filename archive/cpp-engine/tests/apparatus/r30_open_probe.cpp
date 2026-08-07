#include <cstdarg>
#include <cstdlib>
#include <cstring>
#include <fcntl.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <unistd.h>

namespace {

void record(const char *path) noexcept {
  const char *log = std::getenv("HOLONICS_R30_OPEN_LOG");
  if (log == nullptr || path == nullptr)
    return;
  const int descriptor = static_cast<int>(
      ::syscall(SYS_openat, AT_FDCWD, log, O_WRONLY | O_CREAT | O_APPEND, 0600));
  if (descriptor < 0)
    return;
  constexpr char newline[] = "\n";
  iovec parts[2]{{const_cast<char *>(path), std::strlen(path)},
                 {const_cast<char *>(newline), 1}};
  static_cast<void>(::syscall(SYS_writev, descriptor, parts, 2));
  static_cast<void>(::syscall(SYS_close, descriptor));
}

mode_t creation_mode(int flags, va_list arguments) noexcept {
  return (flags & O_CREAT) != 0 ? static_cast<mode_t>(va_arg(arguments, int))
                                : mode_t{};
}

int open_from(int directory, const char *path, int flags,
              mode_t mode) noexcept {
  record(path);
  return static_cast<int>(::syscall(SYS_openat, directory, path, flags, mode));
}

} // namespace

extern "C" int open(const char *path, int flags, ...) {
  va_list arguments;
  va_start(arguments, flags);
  const auto mode = creation_mode(flags, arguments);
  va_end(arguments);
  return open_from(AT_FDCWD, path, flags, mode);
}
extern "C" int open64(const char *path, int flags, ...) {
  va_list arguments;
  va_start(arguments, flags);
  const auto mode = creation_mode(flags, arguments);
  va_end(arguments);
  return open_from(AT_FDCWD, path, flags, mode);
}
extern "C" int openat(int directory, const char *path, int flags, ...) {
  va_list arguments;
  va_start(arguments, flags);
  const auto mode = creation_mode(flags, arguments);
  va_end(arguments);
  return open_from(directory, path, flags, mode);
}
extern "C" int openat64(int directory, const char *path, int flags, ...) {
  va_list arguments;
  va_start(arguments, flags);
  const auto mode = creation_mode(flags, arguments);
  va_end(arguments);
  return open_from(directory, path, flags, mode);
}
