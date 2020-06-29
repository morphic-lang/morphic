#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

#include "common.h"

static struct profile_info count_primes_info;

uint64_t count_primes(uint64_t limit) {
  uint64_t clock_start = clock_nanos();

  uint64_t accum = 0;
  for (uint64_t n = limit; n > 1; n--) {
    bool composite = false;
    for (uint64_t i = 2; i * i <= n; i++) {
      if (n % i == 0) {
        composite = true;
        break;
      }
    }
    if (!composite) {
      accum++;
    }
  }

  uint64_t clock_end = clock_nanos();
  record_call(&count_primes_info, clock_start, clock_end);

  return accum;
}

int main(int argc, char **argv) {
  unsigned int iters;
  unsigned int limit;
  if (scanf("%u\n%u", &iters, &limit) == EOF) {
    fprintf(stderr, "Expected two positive integers (an iteration count and a limit)\n");
    return 1;
  }

  if (iters == 0) {
    return 0;
  }

  uint64_t result;
  for (unsigned int i = 0; i < iters; i++) {
    result = count_primes(limit);
  }

  printf("There are %llu primes <= %u\n", (unsigned long long)result, limit);

  write_report(count_primes_info);
}
