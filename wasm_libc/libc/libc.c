#include "libc.h"
#include "js_ffi.h"

void _start(void) {
  // TODO: write this function
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

void exit(int code) {
  opt_proto_js_exit(code);
}

void abort(void) {
  exit(1);
}

void print(const char *str) {
  opt_proto_js_print(str, strlen(str));
}

void print_error(const char *str) {
  opt_proto_js_print_error(str, strlen(str));
}
