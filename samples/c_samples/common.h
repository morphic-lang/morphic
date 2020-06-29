#ifndef _7bb56885_4a3f_4b76_9ae7_bde28b8cc52e
#define _7bb56885_4a3f_4b76_9ae7_bde28b8cc52e

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>

struct profile_info {
  uint64_t total_calls;
  uint64_t total_clock_nanos;
};

static uint64_t clock_nanos(void) {
    struct timespec tp;
    if (clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &tp)) {
        perror("Could not get clock");
        exit(1);
    }
    return ((uint64_t)tp.tv_sec)*1000000000 + (uint64_t)tp.tv_nsec;
}

static void record_call(struct profile_info *info, uint64_t start_nanos, uint64_t end_nanos) {
  if (start_nanos > end_nanos) {
    fprintf(stderr, "Error: start_nanos > end_nanos");
    exit(1);
  }

  info->total_calls += 1;
  info->total_clock_nanos += end_nanos - start_nanos;
}

static void write_report(struct profile_info info) {
  char const *report_path = getenv("MORPHIC_PROFILE_PATH");
  if (report_path == NULL) {
    fputs("Warning: no MORPHIC_PROFILE_PATH provided\n", stderr);
    return;
  }

  FILE *report_file = fopen(report_path, "w");
  if (report_file == NULL) {
    perror("Could not open profile report file");
    exit(1);
  }

  if (
    fprintf(
      report_file,
      "{\"total_calls\": %llu, \"total_clock_nanos\": %llu}",
      (unsigned long long)info.total_calls,
      (unsigned long long)info.total_clock_nanos
    ) < 0
  ) {
    // TODO: Does fprintf set errno?
    fputs("Could not write profiling information to report file\n", stderr);
    exit(1);
  }

  if (fclose(report_file)) {
    perror("Error while closing profile report file");
    exit(1);
  }
}

#endif
