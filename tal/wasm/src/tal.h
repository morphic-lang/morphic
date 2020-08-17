#ifndef _264b892f_09af_4c8c_85c3_102a473fbe29
#define _264b892f_09af_4c8c_85c3_102a473fbe29

#include "int.h"

#define NULL 0

#define EOF -1

/* Javascript needs an entry point to the wasm program. This wrapper will
   provide the necessary arguments to the opt-proto main function and allow
   Javascript to easily start execution. */
void _start(void);

void *memset(void *ptr, int value, size_t num); /* Used by dlmalloc implementation. */
void *memcpy(void *restrict dst, const void *restrict src, size_t num); /* Used by dlmalloc implementation. */
size_t strlen(const char *str);
_Noreturn void exit(int code); /* Currently, does not call destructors or atexit functions. */
_Noreturn void abort(void); /* Currently, just shells out to exit(1). */
int getchar(void);

/* Implemented via dlmalloc. */
void *malloc(size_t size);
void *calloc(size_t num, size_t size);
void *realloc(void *ptr, size_t new_size);
void free(void *ptr);

/* Modified versions of libc functions for wasm portability: */
void print(const char *str, ...); /* Currently, does not do proper string formatting. */
void print_error(const char *str, ...); /* Currently, does not do proper string formatting. */
void write(const void *ptr, size_t size, size_t count);
void write_error(const void *ptr, size_t size, size_t count);
int flush(void);
int64_t rand_int64(void);

/* Profiling primitives: */
uint64_t prof_clock_res_nanos(void);
uint64_t prof_clock_nanos(void);
void prof_report_init(void);
void prof_report_write_string(const char *str);
void prof_report_write_u64(uint64_t val);
void prof_report_done(void);

#endif
