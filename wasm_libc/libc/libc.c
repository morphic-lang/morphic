#include "libc.h"

void* memset(void* ptr, int value, size_t num) {
  char* p = (char*)ptr;
  while (num-- != 0) {
    *p++ = value;
  }
  return ptr;
}

void* memcpy(void* dst, const void* src, size_t num) {
  char* d = (char*)dst;
  const char* s = (const char*)src;
  while (num-- != 0) {
    *d++ = *s++;
  }
  return dst;
}
