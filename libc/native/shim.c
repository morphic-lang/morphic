#include "shim.h"
#include <stdarg.h>
#include <stdio.h>

void print(const char *str, ...) {
    va_list arg;
    va_start(arg, str);

    vfprintf(stdout, str, arg);

    va_end(arg);
}

void print_error(const char *str, ...) {
    va_list arg;
    va_start(arg, str);

    vfprintf(stderr, str, arg);

    va_end(arg);
}

void write(const void *ptr, size_t size, size_t count) {
    fwrite(ptr, size, count, stdout);
}

int flush(void) {
    return fflush(stdout);
}
