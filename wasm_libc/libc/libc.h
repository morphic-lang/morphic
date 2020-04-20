#ifndef _0ddc0190_8081_11ea_bc55_0242ac130003
#define _0ddc0190_8081_11ea_bc55_0242ac130003

typedef unsigned long size_t;
typedef long ptrdiff_t;

void _start(void);

void* memset(void* ptr, int value, size_t num); /* Used by dlmalloc implementation */
void* memcpy(void* dst, const void* src, size_t num); /* Used by dlmalloc implementation */
void* malloc(size_t size);
void* calloc(size_t num, size_t size);
void* realloc(void* ptr, size_t new_size);
void free(void* ptr);

#endif