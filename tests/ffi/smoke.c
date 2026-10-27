/*
 * Native smoke test of the plain C API (include/elk_lean.h): initialises elk-lean, lays out
 * the graph given as argv[1] (a JSON file) with the options argv[2] (JSON text, optional) and
 * prints the result; `--algorithms`, `--options`, `--categories` print the metadata.
 * Exit code 0 on success, 1 when the API reported an error, 2 on usage/init errors.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "elk_lean.h"

static char *read_file(const char *path) {
    FILE *f = fopen(path, "rb");
    if (f == NULL) {
        return NULL;
    }
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *buf = (char *)malloc((size_t)n + 1);
    if (buf == NULL || fread(buf, 1, (size_t)n, f) != (size_t)n) {
        fclose(f);
        free(buf);
        return NULL;
    }
    buf[n] = 0;
    fclose(f);
    return buf;
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: smoke GRAPH.json [OPTIONS_JSON] | --algorithms | --options | --categories\n");
        return 2;
    }
    if (elk_lean_init() != 0) {
        return 2;
    }
    int is_error = 0;
    char *out = NULL;
    if (strcmp(argv[1], "--algorithms") == 0) {
        out = elk_lean_known_layout_algorithms(&is_error);
    } else if (strcmp(argv[1], "--options") == 0) {
        out = elk_lean_known_layout_options(&is_error);
    } else if (strcmp(argv[1], "--categories") == 0) {
        out = elk_lean_known_layout_categories(&is_error);
    } else if (strcmp(argv[1], "--version") == 0) {
        printf("%s\n", elk_lean_version());
        return 0;
    } else {
        char *graph = read_file(argv[1]);
        if (graph == NULL) {
            fprintf(stderr, "cannot read %s\n", argv[1]);
            return 2;
        }
        out = elk_lean_layout_json(graph, argc > 2 ? argv[2] : "{}", &is_error);
        free(graph);
    }
    if (out == NULL) {
        return 2;
    }
    fputs(out, is_error ? stderr : stdout);
    fputc('\n', is_error ? stderr : stdout);
    elk_lean_free(out);
    return is_error ? 1 : 0;
}
