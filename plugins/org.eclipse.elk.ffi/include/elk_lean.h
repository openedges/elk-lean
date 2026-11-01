/*
 * elk-lean plain C API (org.eclipse.elk.ffi).
 *
 * The four functions of the elk-rs NAPI/WASM bindings (`layout_json`,
 * `known_layout_algorithms`, `known_layout_options`, `known_layout_categories`) over the
 * Lean entry points of `Elk.Ffi`. Results are NUL-terminated UTF-8 strings allocated with
 * malloc (release them with elk_lean_free). `*is_error` is set to 1 when the result is an
 * error message (the JavaScript layers throw it) and to 0 when it is JSON: compact, object
 * keys sorted, exactly like elk-rs `serde_json::to_string`. elk_lean_convert_elkt (an elk-lean
 * addition) converts ELK Text (.elkt) to ELK JSON like the CLI `elk convert`.
 *
 * Threads: elk_lean_init (or elk_lean_init_threads) must run once before anything else. Every
 * other thread that calls the API must call elk_lean_thread_init first (and
 * elk_lean_thread_finalize before it exits). Calls must not overlap: the layout engine keeps
 * process-wide registries, so hosts serialise calls (Node.js does on its main thread; a
 * worker_threads pool needs a lock).
 *
 * Parallel layout (elk-lean addition): after elk_lean_init_threads the engine may lay out
 * independent sibling sub-graphs on Lean worker threads inside one call; results are
 * byte-identical to the sequential layout (docs/parallel-layout.md). With elk_lean_init alone the
 * engine is sequential.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
#ifndef ELK_LEAN_H
#define ELK_LEAN_H

#ifdef __cplusplus
extern "C" {
#endif

/* Initialises the Lean runtime and all elk-lean modules (idempotent). 0 on success, -1 when
 * a module initialiser failed (the error is printed to stderr). */
int elk_lean_init(void);

/* elk_lean_init, then (first call only; later calls change nothing) starts the Lean task
 * manager and sets the thread cap of the parallel sibling layout: 0 = ELK_LEAN_THREADS or
 * min(hardware threads, 8), 1 = sequential, n = at most n threads per call (the calling thread
 * plus n - 1 Lean workers). Lean workers have the Lean runtime's thread stack (1 GB reserved; only
 * Lean executables apply LEAN_STACK_SIZE_KB), not the stack of the calling thread. 0 on success, -1 as
 * elk_lean_init. */
int elk_lean_init_threads(int threads);

/* Registers / unregisters the calling thread with the Lean runtime. */
void elk_lean_thread_init(void);
void elk_lean_thread_finalize(void);

/* elk-rs layout_api::layout_json(graph_json, options_json). options_json may be "" or "{}". */
char *elk_lean_layout_json(const char *graph_json, const char *options_json, int *is_error);

/* elk_lean_layout_json with the thread cap `threads` for this call (<= 0: the cap set by
 * elk_lean_init_threads; 1: sequential). The result does not depend on it. Without
 * elk_lean_init_threads there is no task manager and the call is sequential. */
char *elk_lean_layout_json_threads(const char *graph_json, const char *options_json, int threads,
                                   int *is_error);

/* elk-rs layout_api::known_layout_algorithms/options/categories (JSON arrays). */
char *elk_lean_known_layout_algorithms(int *is_error);
char *elk_lean_known_layout_options(int *is_error);
char *elk_lean_known_layout_categories(int *is_error);

/* Flag bits of elk_lean_convert_elkt_flags (the `elk convert` options). */
#define ELK_LEAN_CONVERT_DEFAULTS 1  /* --defaults: elk-live sizes (nodes 30, ports 5, labels) */
#define ELK_LEAN_CONVERT_PRETTY 2    /* --pretty: indented output */
#define ELK_LEAN_CONVERT_SORT_KEYS 4 /* --sort-keys: object keys sorted */

/* elk-lean addition: ELK Text (.elkt) -> ELK JSON, byte-identical to `elk convert INPUT.elkt`
 * (compact, keys in exporter order, no default sizes). A parse error is returned with
 * *is_error = 1 as the CLI's message "ELK Text parse error: <line>:<col>: <message>". */
char *elk_lean_convert_elkt(const char *elkt, int *is_error);

/* Same with ELK_LEAN_CONVERT_* flags, e.g. ELK_LEAN_CONVERT_DEFAULTS for `elk convert --defaults`. */
char *elk_lean_convert_elkt_flags(const char *elkt, int flags, int *is_error);

/* elk-lean version ("0.12.0"); static storage, do not free. */
const char *elk_lean_version(void);

/* Releases a string returned by the functions above (free()). */
void elk_lean_free(char *s);

#ifdef __cplusplus
}
#endif

#endif /* ELK_LEAN_H */
