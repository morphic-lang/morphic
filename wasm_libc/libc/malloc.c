#include "libc.h"
#include "js_ffi.h"

/* The following configuration of dlmalloc for WebAssembly is adapted from
   wasi-libc and emscripten-core. */

#define PAGESIZE 65536

/* The MORECORE macro in dlmalloc will use sbrk to allocate memory. */
static void *sbrk(ptrdiff_t increment) {
  if (increment < 0 || increment % PAGESIZE != 0) {
    abort();
  }
  
  if (increment == 0) {
    return (void *) (opt_proto_js_memory_size() * PAGESIZE);
  }

  return (void *) opt_proto_js_memory_grow(increment / PAGESIZE);
}

/* We define the error codes to be the same values as on unix. */
#define ENOMEM 12 /* Out of memory. */
#define EINVAL 22 /* Invalid argument. */

/* WebAssembly doesn't have mmap style allocation. */
#define HAVE_MMAP 0

/* WebAssembly supports memory.grow but has no intrinsic to shrink memory. */
#define MORECORE_CANNOT_TRIM 1

/* Removing sanity checks reduces code size. */
#ifndef DEBUG
#define ABORT __builtin_unreachable()
#endif

/* We don't have any of part of stdlib or unix available. */
#define LACKS_UNISTD_H
#define LACKS_FCNTL_H
#define LACKS_SYS_PARAM_H
#define LACKS_SYS_MMAN_H
#define LACKS_STRINGS_H
#define LACKS_STRING_H
#define LACKS_SYS_TYPES_H
#define LACKS_ERRNO_H
#define LACKS_STDLIB_H
#define LACKS_SCHED_H
#define LACKS_TIME_H

/* Avoid pulling in fprintf and stdio dependencies. */
#define NO_MALLOC_STATS 1

/* Disabling malloc statistics generation reduces code size. */
#define NO_MALLINFO 1

/* Avoids unaligned SIMD accesses. */
#define MALLOC_ALIGNMENT 16

/* This serves two purposes. First, it makes it easy to control which functions
   are exported. Second, if a function has a special name, like "malloc", the
   compiler might assume certain things about its behavior. This could interact
   poorly with the assumptions of code in the "dlmalloc" implementation.
   By using the identifier "dlmalloc" in the implementation, we avoid needing
   to define -fno-builtin as a mitigation. */
#define USE_DL_PREFIX
#define DLMALLOC_EXPORT static inline

/* This isn't declared DLMALLOC_EXPORT, so it must be made static explicitly. */
static size_t dlmalloc_usable_size(void *);

/* By default this is a no-op on Windows and sets errno on other platforms. We
   also set it to a no-op since we don't provide errno to the implementation. */
#define MALLOC_FAILURE_ACTION

/* INCLUDE THE MALLOC IMPLEMENTATION C FILE! */
#include "dlmalloc.c"

/* Expose the correct functions */

void *malloc(size_t size) {
  return dlmalloc(size);
}

void *calloc(size_t num, size_t size) {
  return dlcalloc(num, size);
}

void *realloc(void *ptr, size_t new_size) {
  return dlrealloc(ptr, new_size);
}

void free(void *ptr) {
  dlfree(ptr);
}
