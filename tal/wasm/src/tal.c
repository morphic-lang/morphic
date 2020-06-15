#include "tal.h"
#include "js_ffi.h"

/* Provided by the opt-proto program we will be linked against. */
extern int main(int argc, char **argv);

void _start(void) {
  char *argv = NULL;
  main(0, &argv);
}

void *memset(void *ptr, int value, size_t num) {
  char *p = (char *) ptr;
  while (num-- != 0) {
    *p++ = value;
  }
  return ptr;
}

void *memcpy(void *restrict dst, const void *restrict src, size_t num) {
  char *restrict d = (char *) dst;
  const char *restrict s = (const char *) src;
  while (num-- != 0) {
    *d++ = *s++;
  }
  return dst;
}

size_t strlen(const char *str) {
  const char *s = str;
  while (*s) {
    ++s;
  }
  return s - str;
}

_Noreturn void exit(int code) {
  morphic_js_exit(code);
}

_Noreturn void abort(void) {
  exit(1);
}

int getchar(void) {
  /* Implemented entirely on the Javascript side because dealing with variable
     length console input is annoying. */
  return morphic_js_get_char();
}

void print(const char *str, ...) {
  morphic_js_print(str, strlen(str));
}

void print_error(const char *str, ...) {
  morphic_js_print_error(str, strlen(str));
}

void write(const void *ptr, size_t size, size_t count) {
  morphic_js_print((const char *) ptr, size * count);
}

int flush(void) {
  /* There is no analogous function to flush for Javascript. */
  return 0;
}

static _Noreturn void prof_not_supported_error(void) {
  print_error("Profiling on the webassembly target is not yet supported");
  morphic_js_exit(1);
}

uint64_t prof_clock_res_nanos(void) {
  prof_not_supported_error();
}

uint64_t prof_clock_nanos(void) {
  prof_not_supported_error();
}

void prof_report_init(void) {
  prof_not_supported_error();
}

void prof_report_write_string(const char *str) {
  prof_not_supported_error();
}

void prof_report_write_u64(uint64_t val) {
  prof_not_supported_error();
}

void prof_report_done(void) {
  prof_not_supported_error();
}
