#ifndef _264b892f_09af_4c8c_85c3_102a473fbe29
#define _264b892f_09af_4c8c_85c3_102a473fbe29

#define NULL 0

#define EOF -1

typedef unsigned long size_t;
typedef long ptrdiff_t;

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
int flush(void);

#endif