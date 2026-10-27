/*
 * elk-lean Node.js native addon (org.eclipse.elk.napi), port of elk-rs
 * plugins/org.eclipse.elk.napi/src/lib.rs over the plain C API of org.eclipse.elk.ffi
 * (include/elk_lean.h). Written against the Node-API C interface only (no C++ wrapper).
 *
 * Exports (all synchronous, elk-rs names and semantics):
 *   layout_json(graphJson: string, optionsJson: string) -> string
 *   known_layout_algorithms() -> string
 *   known_layout_options() -> string
 *   known_layout_categories() -> string
 * An engine error is thrown as a JavaScript `Error(message)` (napi::Error::from_reason).
 *
 * Threading: the module is context aware, so worker_threads may load it. elk_lean_init runs
 * once per process, on the thread that loads the addon first. Any other thread registers
 * itself with the Lean runtime (elk_lean_thread_init) before its first call and unregisters
 * when its Node environment is torn down. Every engine call holds one process-wide mutex
 * because the layout engine keeps process-global registries.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
#define NAPI_VERSION 8
#include <node_api.h>

#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "elk_lean.h"

/* Serialises elk_lean_init and every engine call across all threads. */
static pthread_mutex_t g_lock = PTHREAD_MUTEX_INITIALIZER;
static int g_init_state = 0; /* 0: not attempted, 1: ready, -1: failed (guarded by g_lock) */
static pthread_t g_init_thread;
/* 1 when the calling thread is registered with the Lean runtime (init thread or after
 * elk_lean_thread_init). */
static _Thread_local int t_registered = 0;

/* The Lean runtime installs its own SIGSEGV/SIGBUS handlers (stack overflow detection) while
 * initialising; Node.js/V8 rely on theirs (WebAssembly trap handling), so they are restored. */
static const int k_saved_signals[] = {SIGSEGV, SIGBUS};
#define K_SAVED_SIGNALS (sizeof k_saved_signals / sizeof k_saved_signals[0])

typedef struct {
    struct sigaction actions[K_SAVED_SIGNALS];
} saved_signals;

static void save_signals(saved_signals *s) {
    for (size_t i = 0; i < K_SAVED_SIGNALS; i++) {
        sigaction(k_saved_signals[i], NULL, &s->actions[i]);
    }
}

static void restore_signals(const saved_signals *s) {
    for (size_t i = 0; i < K_SAVED_SIGNALS; i++) {
        sigaction(k_saved_signals[i], &s->actions[i], NULL);
    }
}

/* Runs elk_lean_init once per process; must hold g_lock. */
static int ensure_engine_locked(void) {
    if (g_init_state == 0) {
        saved_signals saved;
        save_signals(&saved);
        int rc = elk_lean_init();
        restore_signals(&saved);
        g_init_state = rc == 0 ? 1 : -1;
        if (rc == 0) {
            g_init_thread = pthread_self();
            t_registered = 1;
        }
    }
    return g_init_state == 1 ? 0 : -1;
}

/* Registers the calling thread with the Lean runtime on first use; must hold g_lock. */
static void ensure_thread_locked(void) {
    if (!t_registered) {
        saved_signals saved;
        save_signals(&saved);
        elk_lean_thread_init();
        restore_signals(&saved);
        t_registered = 1;
    }
}

/* Environment teardown of a worker thread: unregister it from the Lean runtime. */
static void env_cleanup(void *arg) {
    (void)arg;
    pthread_mutex_lock(&g_lock);
    if (t_registered && g_init_state == 1 && !pthread_equal(pthread_self(), g_init_thread)) {
        elk_lean_thread_finalize();
        t_registered = 0;
    }
    pthread_mutex_unlock(&g_lock);
}

/* Converts a C string result into a JS string, or throws it as an Error; frees `out`. */
static napi_value finish(napi_env env, char *out, int is_error) {
    napi_value result = NULL;
    if (out == NULL) {
        napi_throw_error(env, NULL, "elk-lean: out of memory");
        return NULL;
    }
    if (is_error) {
        napi_throw_error(env, NULL, out);
    } else if (napi_create_string_utf8(env, out, NAPI_AUTO_LENGTH, &result) != napi_ok) {
        napi_throw_error(env, NULL, "elk-lean: cannot create the result string");
        result = NULL;
    }
    elk_lean_free(out);
    return result;
}

/* Copies a JS string argument into a malloc'd UTF-8 buffer; throws a TypeError otherwise.
 * When `optional` is set, undefined/null become "". */
static char *get_string_arg(napi_env env, napi_value value, const char *name, int optional) {
    napi_valuetype type;
    if (napi_typeof(env, value, &type) != napi_ok) {
        napi_throw_error(env, NULL, "elk-lean: cannot inspect argument");
        return NULL;
    }
    if (optional && (type == napi_undefined || type == napi_null)) {
        char *empty = (char *)malloc(1);
        if (empty != NULL) {
            empty[0] = 0;
        }
        return empty;
    }
    if (type != napi_string) {
        char msg[128];
        snprintf(msg, sizeof msg, "elk-lean: argument '%s' must be a string", name);
        napi_throw_type_error(env, NULL, msg);
        return NULL;
    }
    size_t len = 0;
    if (napi_get_value_string_utf8(env, value, NULL, 0, &len) != napi_ok) {
        napi_throw_error(env, NULL, "elk-lean: cannot read string argument");
        return NULL;
    }
    char *buf = (char *)malloc(len + 1);
    if (buf == NULL) {
        napi_throw_error(env, NULL, "elk-lean: out of memory");
        return NULL;
    }
    if (napi_get_value_string_utf8(env, value, buf, len + 1, &len) != napi_ok) {
        free(buf);
        napi_throw_error(env, NULL, "elk-lean: cannot read string argument");
        return NULL;
    }
    return buf;
}

typedef char *(*metadata_fn)(int *is_error);

/* Runs one metadata query under the engine lock. */
static napi_value call_metadata(napi_env env, metadata_fn fn) {
    int is_error = 1;
    char *out;
    pthread_mutex_lock(&g_lock);
    if (ensure_engine_locked() != 0) {
        pthread_mutex_unlock(&g_lock);
        napi_throw_error(env, NULL, "elk-lean: engine initialisation failed");
        return NULL;
    }
    ensure_thread_locked();
    out = fn(&is_error);
    pthread_mutex_unlock(&g_lock);
    return finish(env, out, is_error);
}

/* layout_json(graphJson, optionsJson): elk-rs layout_api::layout_json. */
static napi_value js_layout_json(napi_env env, napi_callback_info info) {
    size_t argc = 2;
    napi_value argv[2];
    if (napi_get_cb_info(env, info, &argc, argv, NULL, NULL) != napi_ok) {
        napi_throw_error(env, NULL, "elk-lean: cannot read arguments");
        return NULL;
    }
    napi_value undef;
    napi_get_undefined(env, &undef);
    char *graph = get_string_arg(env, argc > 0 ? argv[0] : undef, "graphJson", 0);
    if (graph == NULL) {
        return NULL;
    }
    char *options = get_string_arg(env, argc > 1 ? argv[1] : undef, "optionsJson", 1);
    if (options == NULL) {
        free(graph);
        return NULL;
    }
    int is_error = 1;
    char *out;
    pthread_mutex_lock(&g_lock);
    if (ensure_engine_locked() != 0) {
        pthread_mutex_unlock(&g_lock);
        free(graph);
        free(options);
        napi_throw_error(env, NULL, "elk-lean: engine initialisation failed");
        return NULL;
    }
    ensure_thread_locked();
    out = elk_lean_layout_json(graph, options, &is_error);
    pthread_mutex_unlock(&g_lock);
    free(graph);
    free(options);
    return finish(env, out, is_error);
}

static napi_value js_known_layout_algorithms(napi_env env, napi_callback_info info) {
    (void)info;
    return call_metadata(env, elk_lean_known_layout_algorithms);
}

static napi_value js_known_layout_options(napi_env env, napi_callback_info info) {
    (void)info;
    return call_metadata(env, elk_lean_known_layout_options);
}

static napi_value js_known_layout_categories(napi_env env, napi_callback_info info) {
    (void)info;
    return call_metadata(env, elk_lean_known_layout_categories);
}

NAPI_MODULE_INIT(/* napi_env env, napi_value exports */) {
    pthread_mutex_lock(&g_lock);
    int rc = ensure_engine_locked();
    int is_init_thread = rc == 0 && pthread_equal(pthread_self(), g_init_thread);
    pthread_mutex_unlock(&g_lock);
    if (rc != 0) {
        napi_throw_error(env, NULL,
                         "elk-lean: elk_lean_init() failed (see stderr for the module error)");
        return NULL;
    }
    if (!is_init_thread) {
        napi_add_env_cleanup_hook(env, env_cleanup, NULL);
    }
    napi_property_descriptor props[] = {
        {"layout_json", NULL, js_layout_json, NULL, NULL, NULL, napi_enumerable, NULL},
        {"known_layout_algorithms", NULL, js_known_layout_algorithms, NULL, NULL, NULL,
         napi_enumerable, NULL},
        {"known_layout_options", NULL, js_known_layout_options, NULL, NULL, NULL,
         napi_enumerable, NULL},
        {"known_layout_categories", NULL, js_known_layout_categories, NULL, NULL, NULL,
         napi_enumerable, NULL},
    };
    napi_value version;
    if (napi_define_properties(env, exports, sizeof props / sizeof props[0], props) != napi_ok ||
        napi_create_string_utf8(env, elk_lean_version(), NAPI_AUTO_LENGTH, &version) != napi_ok ||
        napi_set_named_property(env, exports, "version", version) != napi_ok) {
        napi_throw_error(env, NULL, "elk-lean: cannot define the module exports");
        return NULL;
    }
    return exports;
}
