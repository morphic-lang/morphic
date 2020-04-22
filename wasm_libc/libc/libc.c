#include "libc.h"
#include "js_ffi.h"

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
  opt_proto_js_exit(code);
}

_Noreturn void abort(void) {
  exit(1);
}

int get_char(void) {
  /* Implemented entirely on the Javascript side because dealing with variable
     length console input is annoying. */
  return opt_proto_js_get_char();
}

void print(const char *str) {
  opt_proto_js_print(str, strlen(str));
}

void print_error(const char *str) {
  opt_proto_js_print_error(str, strlen(str));
}

void write(const void *ptr, size_t size, size_t count) {
  opt_proto_js_print((const char *) ptr, size * count);
}
