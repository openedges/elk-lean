/*
 * Platform pieces the Lean 4.35 runtime expects from its native environment, for emscripten:
 * the synchronous libuv subset declared in uv_compat/uv.h (used by src/runtime/io.cpp for file
 * metadata, hard links, temporary files and error messages), on top of emscripten's POSIX layer.
 *
 * elk-lean itself never touches the file system through the WASM API; these only have to be
 * correct, not fast.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
#define _POSIX_C_SOURCE 200809L /* strdup, mkdtemp, mkstemp, lstat, link under -std=c11 */
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#include "uv.h"

const char *uv_strerror(int err) { return strerror(-err); }

int uv_os_tmpdir(char *buffer, size_t *size) {
    static const char *const vars[] = {"TMPDIR", "TMP", "TEMP", "TEMPDIR"};
    const char *dir = NULL;
    for (size_t i = 0; i < sizeof vars / sizeof vars[0] && dir == NULL; i++) {
        dir = getenv(vars[i]);
        if (dir != NULL && dir[0] == 0) {
            dir = NULL;
        }
    }
    if (dir == NULL) {
        dir = "/tmp";
    }
    size_t len = strlen(dir);
    if (len > 1 && dir[len - 1] == '/') {
        len--; /* libuv strips one trailing slash */
    }
    if (len >= *size) {
        *size = len + 1;
        return UV_ENOBUFS;
    }
    memcpy(buffer, dir, len);
    buffer[len] = 0;
    *size = len;
    return 0;
}

static void fill_stat(uv_stat_t *out, const struct stat *st) {
    memset(out, 0, sizeof *out);
    out->st_dev = (uint64_t)st->st_dev;
    out->st_mode = (uint64_t)st->st_mode;
    out->st_nlink = (uint64_t)st->st_nlink;
    out->st_uid = (uint64_t)st->st_uid;
    out->st_gid = (uint64_t)st->st_gid;
    out->st_rdev = (uint64_t)st->st_rdev;
    out->st_ino = (uint64_t)st->st_ino;
    out->st_size = (uint64_t)st->st_size;
    out->st_blksize = (uint64_t)st->st_blksize;
    out->st_blocks = (uint64_t)st->st_blocks;
    out->st_atim.tv_sec = (long)st->st_atim.tv_sec;
    out->st_atim.tv_nsec = (long)st->st_atim.tv_nsec;
    out->st_mtim.tv_sec = (long)st->st_mtim.tv_sec;
    out->st_mtim.tv_nsec = (long)st->st_mtim.tv_nsec;
    out->st_ctim.tv_sec = (long)st->st_ctim.tv_sec;
    out->st_ctim.tv_nsec = (long)st->st_ctim.tv_nsec;
    out->st_birthtim = out->st_ctim;
}

static int finish(uv_fs_t *req, int ret) {
    req->result = ret < 0 ? -errno : ret;
    return (int)req->result;
}

static void init_req(uv_fs_t *req, const char *path) {
    memset(req, 0, sizeof *req);
    req->path = path;
}

int uv_fs_stat(uv_loop_t *loop, uv_fs_t *req, const char *path, uv_fs_cb cb) {
    (void)loop;
    (void)cb;
    struct stat st;
    init_req(req, path);
    int ret = stat(path, &st);
    if (ret == 0) {
        fill_stat(&req->statbuf, &st);
    }
    return finish(req, ret);
}

int uv_fs_lstat(uv_loop_t *loop, uv_fs_t *req, const char *path, uv_fs_cb cb) {
    (void)loop;
    (void)cb;
    struct stat st;
    init_req(req, path);
    int ret = lstat(path, &st);
    if (ret == 0) {
        fill_stat(&req->statbuf, &st);
    }
    return finish(req, ret);
}

int uv_fs_link(uv_loop_t *loop, uv_fs_t *req, const char *path, const char *new_path, uv_fs_cb cb) {
    (void)loop;
    (void)cb;
    init_req(req, path);
    return finish(req, link(path, new_path));
}

int uv_fs_unlink(uv_loop_t *loop, uv_fs_t *req, const char *path, uv_fs_cb cb) {
    (void)loop;
    (void)cb;
    init_req(req, path);
    return finish(req, unlink(path));
}

/* As in libuv, `req->path` is a malloc'd copy of the template that receives the generated
 * name; uv_fs_req_cleanup releases it. */
static char *dup_template(uv_fs_t *req, const char *tpl) {
    char *path = strdup(tpl);
    init_req(req, path);
    req->owned_path = path;
    return path;
}

int uv_fs_mkstemp(uv_loop_t *loop, uv_fs_t *req, const char *tpl, uv_fs_cb cb) {
    (void)loop;
    (void)cb;
    char *path = dup_template(req, tpl);
    if (path == NULL) {
        req->result = UV_ENOMEM;
        return UV_ENOMEM;
    }
    return finish(req, mkstemp(path));
}

int uv_fs_mkdtemp(uv_loop_t *loop, uv_fs_t *req, const char *tpl, uv_fs_cb cb) {
    (void)loop;
    (void)cb;
    char *path = dup_template(req, tpl);
    if (path == NULL) {
        req->result = UV_ENOMEM;
        return UV_ENOMEM;
    }
    return finish(req, mkdtemp(path) == NULL ? -1 : 0);
}

void uv_fs_req_cleanup(uv_fs_t *req) {
    if (req == NULL) {
        return;
    }
    /* only the temporary-file requests own their path (see dup_template) */
    free(req->owned_path);
    req->owned_path = NULL;
    req->path = NULL;
}
