#include "tal.h"
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <sys/syscall.h>
#include <linux/random.h>

void print(const char *str, ...) {
    va_list arg;

    va_start(arg, str);
    vfprintf(stdout, str, arg);
    va_end(arg);
}

void print_error(const char *str, ...) {
    va_list arg;

    va_start(arg, str);
    vfprintf(stderr, str, arg);
    va_end(arg);
}

void write(const void *ptr, size_t size, size_t count) {
    fwrite(ptr, size, count, stdout);
}

void write_error(const void *ptr, size_t size, size_t count) {
    fwrite(ptr, size, count, stderr);
}

int flush(void) {
    return fflush(stdout);
}

int64_t rand_int64(void) {
    int64_t i;
    syscall(SYS_getrandom, &i, sizeof(i), 0);
    return i;
}

#define PROF_CLOCK_ID (CLOCK_MONOTONIC)

/* TODO: Is this advisable?  Is there some reason the POSIX clock API doesn't natively work entirely
   with nanoseconds? */
#define TIMESPEC_TO_NANOS(spec) (((uint64_t)(spec).tv_sec)*1000000000 + ((uint64_t)(spec).tv_nsec))

uint64_t prof_clock_res_nanos(void) {
    struct timespec res;
    if (clock_getres(PROF_CLOCK_ID, &res)) {
        perror("Could not get clock resolution");
        exit(1);
    }
    return TIMESPEC_TO_NANOS(res);
}

uint64_t prof_clock_nanos(void) {
    struct timespec tp;
    if (clock_gettime(PROF_CLOCK_ID, &tp)) {
        perror("Could not get clock");
        exit(1);
    }
    return TIMESPEC_TO_NANOS(tp);
}

static FILE *prof_report_file = NULL;

void prof_report_init(void) {
    const char *report_path = getenv("MORPHIC_PROFILE_PATH");
    if (report_path == NULL) {
        return;
    }

    prof_report_file = fopen(report_path, "w");
    if (prof_report_file == NULL) {
        perror("Could not open profile report file");
        exit(1);
    }
}

void prof_report_write_string(const char *str) {
    if (prof_report_file == NULL) {
        return;
    }

    fputs(str, prof_report_file);
    if (ferror(prof_report_file)) {
        perror("Could not write to profile report file");
        exit(1);
    }
}

void prof_report_write_u64(uint64_t val) {
    if (prof_report_file == NULL) {
        return;
    }

    if (fprintf(prof_report_file, "%llu", (unsigned long long)val) < 0) {
        // TODO: Does fprintf set errno?
        fputs("Could not write integer to profile report file\n", stderr);
        exit(1);
    }
}

void prof_report_done(void) {
    if (prof_report_file == NULL) {
        return;
    }

    if (fclose(prof_report_file)) {
        perror("Error while closing profile report file");
        exit(1);
    }
}
