#ifndef _ade9ea77_e1cc_4ec8_8db3_0117569ac863
#define _ade9ea77_e1cc_4ec8_8db3_0117569ac863

#include <stddef.h>
#include <stdint.h>

/* Because of various constraints when compiling for WebAssembly (for instance,
   the lack of a filesystem), some of the morphic builtins rely on what amount
   to lightweight wrappers over libc functions. */

void morphic_print(const char *str, ...);
void morphic_print_error(const char *str, ...);
void morphic_write(const void *ptr, size_t size, size_t count);
void morphic_write_error(const void *ptr, size_t size, size_t count);
int morphic_flush(void);

/* Profiling primitives: */
uint64_t morphic_prof_clock_res_nanos(void);
uint64_t morphic_prof_clock_nanos(void);
void morphic_prof_report_init(void);
void morphic_prof_report_write_string(const char *str);
void morphic_prof_report_write_u64(uint64_t val);
void morphic_prof_report_done(void);

void morphic_prof_rc_record_retain(void);
void morphic_prof_rc_record_release(void);
void morphic_prof_rc_record_rc1(void);
uint64_t morphic_prof_rc_get_retain_count(void);
uint64_t morphic_prof_rc_get_release_count(void);
uint64_t morphic_prof_rc_get_rc1_count(void);

/* bdwgc provides function `GC_init`, but instructs us to call the `GC_INIT`
   macro, which does additional work dependent on the flags used to compile
   bdwgc. We wrap this macro to call it from morphic programs. */
void morphic_GC_init(void);

/* bdwgc does not provide a calloc. */
void *morphic_GC_calloc(size_t num, size_t size);

#endif
