#ifndef _264b892f_09af_4c8c_85c3_102a473fbe29
#define _264b892f_09af_4c8c_85c3_102a473fbe29

typedef unsigned long size_t;
typedef long ptrdiff_t;

void _start(void);

void *memset(void *ptr, int value, size_t num); /* Used by dlmalloc implementation */
void *memcpy(void *restrict dst, const void *restrict src, size_t num); /* Used by dlmalloc implementation */
size_t strlen(const char *str);
void exit(int code); /* Currently, does not call destructors or atexit functions */
void abort(void); /* Currently, just shells out to exit(1) */
void print(const char *str); /* Not actually a libc function */
void print_error(const char *str); /* Not actually a libc function */

void *malloc(size_t size);
void *calloc(size_t num, size_t size);
void *realloc(void *ptr, size_t new_size);
void free(void *ptr);

#endif