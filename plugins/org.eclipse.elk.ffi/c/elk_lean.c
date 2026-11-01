/*
 * elk-lean plain C API, see include/elk_lean.h.
 *
 * Wraps the `@[export]` functions of `Elk.Ffi` (plugins/org.eclipse.elk.ffi/Elk/Ffi.lean):
 * each returns an `Except String String` object (`Except.error` = constructor tag 0,
 * `Except.ok` = tag 1, string in field 0) that is copied into a malloc'd C string.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>

#include "elk_lean.h"

/* Lean runtime (libleanrt) and the module initialiser of `Elk.Ffi` (package `elk-lean`). */
extern void lean_initialize_runtime_module(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);
extern void lean_init_task_manager(void);
extern lean_object *initialize_elk_x2dlean_Elk_Ffi(uint8_t builtin);

/* `Elk.Ffi` exports. */
extern lean_object *elk_ffi_layout_json(lean_obj_arg graph, lean_obj_arg options);
extern lean_object *elk_ffi_known_layout_algorithms(lean_obj_arg unit);
extern lean_object *elk_ffi_known_layout_options(lean_obj_arg unit);
extern lean_object *elk_ffi_known_layout_categories(lean_obj_arg unit);
extern lean_object *elk_ffi_convert_elkt(lean_obj_arg elkt, uint32_t flags);
extern lean_object *elk_ffi_set_threads(uint32_t threads);
extern lean_object *elk_ffi_layout_json_threads(lean_obj_arg graph, lean_obj_arg options, uint32_t threads);

static int g_state = 0; /* 0: not initialised, 1: ready, -1: initialisation failed */
static int g_threads_state = 0; /* 1 once elk_lean_init_threads has run (the task manager is started) */

int elk_lean_init(void) {
    if (g_state != 0) {
        return g_state == 1 ? 0 : -1;
    }
    lean_initialize_runtime_module();
    /* like the Lake-generated main: no panic messages while module initialisers run */
    lean_set_panic_messages(false);
    lean_object *res = initialize_elk_x2dlean_Elk_Ffi(1 /* builtin */);
    lean_set_panic_messages(true);
    lean_io_mark_end_initialization();
    if (lean_io_result_is_ok(res)) {
        lean_dec_ref(res);
        g_state = 1;
        return 0;
    }
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    g_state = -1;
    return -1;
}

/* elk_lean_init + the Lean task manager (once per process; LEAN_NUM_THREADS or the hardware
 * threads, workers are created on first use) + the thread cap of the parallel sibling layout
 * (Elk.Core.Parallel: 0 = ELK_LEAN_THREADS or min(hardware threads, 8), 1 = sequential). Later
 * calls change nothing. Without a multi-threaded Lean runtime (the WASM build) the task manager is
 * not created and the engine stays sequential (its probe sees tasks run on the calling thread). */
int elk_lean_init_threads(int threads) {
    int rc = elk_lean_init();
    if (rc != 0 || g_threads_state != 0) {
        return rc;
    }
    g_threads_state = 1;
    lean_init_task_manager();
    lean_object *r = elk_ffi_set_threads(threads > 0 ? (uint32_t)threads : 0u);
    lean_dec(r);
    return 0;
}

void elk_lean_thread_init(void) { lean_initialize_thread(); }

void elk_lean_thread_finalize(void) { lean_finalize_thread(); }

static char *copy_lean_string(b_lean_obj_arg s) {
    size_t n = lean_string_size(s) - 1; /* byte size includes the terminating NUL */
    char *out = (char *)malloc(n + 1);
    if (out == NULL) {
        return NULL;
    }
    memcpy(out, lean_string_cstr(s), n);
    out[n] = 0;
    return out;
}

/* Consumes an `Except String String` result. */
static char *take_result(lean_obj_arg r, int *is_error) {
    int err = lean_obj_tag(r) == 0;
    char *out = copy_lean_string(lean_ctor_get(r, 0));
    lean_dec_ref(r);
    if (is_error != NULL) {
        *is_error = err;
    }
    return out;
}

static char *not_initialised(int *is_error) {
    static const char msg[] = "elk-lean: elk_lean_init() failed or was not called";
    char *out = (char *)malloc(sizeof msg);
    if (out != NULL) {
        memcpy(out, msg, sizeof msg);
    }
    if (is_error != NULL) {
        *is_error = 1;
    }
    return out;
}

char *elk_lean_layout_json(const char *graph_json, const char *options_json, int *is_error) {
    if (g_state != 1) {
        return not_initialised(is_error);
    }
    if (options_json == NULL) {
        options_json = "";
    }
    /* lean_mk_string_from_bytes replaces invalid UTF-8 instead of trusting the host */
    lean_object *g = lean_mk_string_from_bytes(graph_json, strlen(graph_json));
    lean_object *o = lean_mk_string_from_bytes(options_json, strlen(options_json));
    lean_object *r = elk_ffi_layout_json(g, o); /* consumes g and o (exports take owned arguments) */
    return take_result(r, is_error);
}

char *elk_lean_layout_json_threads(const char *graph_json, const char *options_json, int threads,
                                   int *is_error) {
    if (g_state != 1) {
        return not_initialised(is_error);
    }
    if (options_json == NULL) {
        options_json = "";
    }
    lean_object *g = lean_mk_string_from_bytes(graph_json, strlen(graph_json));
    lean_object *o = lean_mk_string_from_bytes(options_json, strlen(options_json));
    lean_object *r = elk_ffi_layout_json_threads(g, o, threads > 0 ? (uint32_t)threads : 0u);
    return take_result(r, is_error);
}

char *elk_lean_known_layout_algorithms(int *is_error) {
    if (g_state != 1) {
        return not_initialised(is_error);
    }
    return take_result(elk_ffi_known_layout_algorithms(lean_box(0)), is_error);
}

char *elk_lean_known_layout_options(int *is_error) {
    if (g_state != 1) {
        return not_initialised(is_error);
    }
    return take_result(elk_ffi_known_layout_options(lean_box(0)), is_error);
}

char *elk_lean_known_layout_categories(int *is_error) {
    if (g_state != 1) {
        return not_initialised(is_error);
    }
    return take_result(elk_ffi_known_layout_categories(lean_box(0)), is_error);
}

char *elk_lean_convert_elkt_flags(const char *elkt, int flags, int *is_error) {
    if (g_state != 1) {
        return not_initialised(is_error);
    }
    lean_object *t = lean_mk_string_from_bytes(elkt, strlen(elkt));
    lean_object *r = elk_ffi_convert_elkt(t, (uint32_t)flags); /* consumes t */
    return take_result(r, is_error);
}

char *elk_lean_convert_elkt(const char *elkt, int *is_error) {
    return elk_lean_convert_elkt_flags(elkt, 0, is_error);
}

const char *elk_lean_version(void) { return "0.12.0"; }

void elk_lean_free(char *s) { free(s); }
