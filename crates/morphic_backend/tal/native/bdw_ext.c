#include <string.h>
#include <gc.h>

/* bdwgc provides function `GC_init`, but instructs us to call the `GC_INIT`
   macro, which does additional work dependent on the flags used to compile
   bdwgc. We wrap this macro to call it from morphic programs. */
void morphic_GC_init(void) {
    GC_INIT();
}

/* bdwgc does not provide a calloc. */
void *morphic_GC_calloc(size_t num, size_t size) {
    size_t total_size = num * size;
    void *ptr = GC_malloc(total_size);
    if (ptr == NULL) {
        return NULL;
    }
    return memset(ptr, 0, total_size);
}