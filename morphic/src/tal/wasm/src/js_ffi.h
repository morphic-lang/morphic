#ifndef _638e62ef_8d8e_414d_bbb5_13ca336e2466
#define _638e62ef_8d8e_414d_bbb5_13ca336e2466

#include "int.h"

extern _Noreturn void     morphic_js_exit       (int );
extern           int      morphic_js_get_char   (void);
extern           int64_t  morphic_js_rand_int64 (void);
extern           void     morphic_js_print      (const char *, unsigned long);
extern           void     morphic_js_print_error(const char *, unsigned long);
extern           int      morphic_js_memory_size(void);
extern           int      morphic_js_memory_grow(int );

#endif
