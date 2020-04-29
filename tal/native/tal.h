#ifndef _ade9ea77_e1cc_4ec8_8db3_0117569ac863
#define _ade9ea77_e1cc_4ec8_8db3_0117569ac863

#include <stddef.h>

/* Because of various constraints when compiling for WebAssembly (for instance,
   the lack of a filesystem), some of the opt-proto builtins rely on what
   amount to lightweight wrappers over libc functions. */

void print(const char *str, ...);
void print_error(const char *str, ...);
void write(const void *ptr, size_t size, size_t count);
int flush(void);

#endif