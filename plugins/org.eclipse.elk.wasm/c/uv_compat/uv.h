/*
 * Minimal libuv compatibility header for the emscripten build of the Lean runtime.
 *
 * Lean 4.35's `src/runtime/io.cpp` includes <uv.h> unconditionally (error-code translation, file
 * metadata, temporary files), while every other libuv use of the runtime is disabled under
 * LEAN_EMSCRIPTEN. Instead of building libuv for wasm32 (Lean's own CMake does, with pthreads),
 * this header declares exactly the subset io.cpp uses, with the libuv Unix ABI: error codes are
 * negated errno values (`UV_EXXX == -EXXX`), the struct fields io.cpp reads keep their libuv names
 * and types. The synchronous functions are implemented with POSIX calls in ../uv_compat.c.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
#ifndef ELK_WASM_UV_COMPAT_H
#define ELK_WASM_UV_COMPAT_H

#include <errno.h>
#include <stddef.h>
#include <stdint.h>
#include <sys/types.h>

#ifdef __cplusplus
extern "C" {
#endif

/* libuv 1.48.0 (the version Lean's CMake builds for emscripten): ENODATA is mapped (>= 1.45),
 * ENOEXEC is not (< 1.50). */
#define UV_VERSION_MAJOR 1
#define UV_VERSION_MINOR 48
#define UV_VERSION_PATCH 0
#define UV_VERSION_HEX ((UV_VERSION_MAJOR << 16) | (UV_VERSION_MINOR << 8) | UV_VERSION_PATCH)

#define UV_E2BIG (-E2BIG)
#define UV_EACCES (-EACCES)
#define UV_EADDRINUSE (-EADDRINUSE)
#define UV_EADDRNOTAVAIL (-EADDRNOTAVAIL)
#define UV_EAFNOSUPPORT (-EAFNOSUPPORT)
#define UV_EAGAIN (-EAGAIN)
#define UV_EBADF (-EBADF)
#define UV_EBUSY (-EBUSY)
#define UV_ECONNABORTED (-ECONNABORTED)
#define UV_ECONNREFUSED (-ECONNREFUSED)
#define UV_ECONNRESET (-ECONNRESET)
#define UV_EDESTADDRREQ (-EDESTADDRREQ)
#define UV_EEXIST (-EEXIST)
#define UV_EFAULT (-EFAULT)
#define UV_EFBIG (-EFBIG)
#define UV_EHOSTUNREACH (-EHOSTUNREACH)
#define UV_EILSEQ (-EILSEQ)
#define UV_EINTR (-EINTR)
#define UV_EINVAL (-EINVAL)
#define UV_EIO (-EIO)
#define UV_EISCONN (-EISCONN)
#define UV_EISDIR (-EISDIR)
#define UV_ELOOP (-ELOOP)
#define UV_EMFILE (-EMFILE)
#define UV_EMLINK (-EMLINK)
#define UV_EMSGSIZE (-EMSGSIZE)
#define UV_ENAMETOOLONG (-ENAMETOOLONG)
#define UV_ENETDOWN (-ENETDOWN)
#define UV_ENETUNREACH (-ENETUNREACH)
#define UV_ENFILE (-ENFILE)
#define UV_ENOBUFS (-ENOBUFS)
#define UV_ENODATA (-ENODATA)
#define UV_ENODEV (-ENODEV)
#define UV_ENOENT (-ENOENT)
#define UV_ENOEXEC (-ENOEXEC)
#define UV_ENOMEM (-ENOMEM)
#define UV_ENOPROTOOPT (-ENOPROTOOPT)
#define UV_ENOSPC (-ENOSPC)
#define UV_ENOSYS (-ENOSYS)
#define UV_ENOTCONN (-ENOTCONN)
#define UV_ENOTDIR (-ENOTDIR)
#define UV_ENOTEMPTY (-ENOTEMPTY)
#define UV_ENOTSOCK (-ENOTSOCK)
#define UV_ENOTSUP (-ENOTSUP)
#define UV_ENOTTY (-ENOTTY)
#define UV_ENXIO (-ENXIO)
#define UV_EPERM (-EPERM)
#define UV_EPIPE (-EPIPE)
#define UV_EPROTO (-EPROTO)
#define UV_EPROTONOSUPPORT (-EPROTONOSUPPORT)
#define UV_EPROTOTYPE (-EPROTOTYPE)
#define UV_ERANGE (-ERANGE)
#define UV_EROFS (-EROFS)
#define UV_ESPIPE (-ESPIPE)
#define UV_ESRCH (-ESRCH)
#define UV_ETIMEDOUT (-ETIMEDOUT)
#define UV_ETXTBSY (-ETXTBSY)
#define UV_EXDEV (-EXDEV)

typedef struct uv_loop_s uv_loop_t;

typedef struct {
    long tv_sec;
    long tv_nsec;
} uv_timespec_t;

typedef struct {
    uint64_t st_dev;
    uint64_t st_mode;
    uint64_t st_nlink;
    uint64_t st_uid;
    uint64_t st_gid;
    uint64_t st_rdev;
    uint64_t st_ino;
    uint64_t st_size;
    uint64_t st_blksize;
    uint64_t st_blocks;
    uint64_t st_flags;
    uint64_t st_gen;
    uv_timespec_t st_atim;
    uv_timespec_t st_mtim;
    uv_timespec_t st_ctim;
    uv_timespec_t st_birthtim;
} uv_stat_t;

typedef struct uv_fs_s uv_fs_t;
typedef void (*uv_fs_cb)(uv_fs_t *req);

struct uv_fs_s {
    ssize_t result;
    const char *path;
    uv_stat_t statbuf;
    char *owned_path; /* compat-only: malloc'd copy owned by the request (mkstemp/mkdtemp) */
};

const char *uv_strerror(int err);
int uv_os_tmpdir(char *buffer, size_t *size);
int uv_fs_stat(uv_loop_t *loop, uv_fs_t *req, const char *path, uv_fs_cb cb);
int uv_fs_lstat(uv_loop_t *loop, uv_fs_t *req, const char *path, uv_fs_cb cb);
int uv_fs_link(uv_loop_t *loop, uv_fs_t *req, const char *path, const char *new_path, uv_fs_cb cb);
int uv_fs_mkstemp(uv_loop_t *loop, uv_fs_t *req, const char *tpl, uv_fs_cb cb);
int uv_fs_mkdtemp(uv_loop_t *loop, uv_fs_t *req, const char *tpl, uv_fs_cb cb);
int uv_fs_unlink(uv_loop_t *loop, uv_fs_t *req, const char *path, uv_fs_cb cb);
void uv_fs_req_cleanup(uv_fs_t *req);

#ifdef __cplusplus
}
#endif

#endif /* ELK_WASM_UV_COMPAT_H */
