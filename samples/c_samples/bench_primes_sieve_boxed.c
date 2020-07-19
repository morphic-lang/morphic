#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>

#include "common.h"

typedef bool Primality;
const Primality PRIME = 0;
const Primality COMPOSITE = 1;

static struct profile_info sieve_info;

Primality **sieve(uint64_t limit) {
  uint64_t clock_start = clock_nanos();

  Primality **arr = calloc(1, sizeof(Primality *));
  if (arr == NULL) {
    perror("calloc");
    exit(1);
  }

  *arr = calloc(limit, sizeof(Primality *));
  if (*arr == NULL) {
    perror("calloc");
    exit(1);
  }

  (*arr)[0] = COMPOSITE;
  (*arr)[1] = COMPOSITE;

  for (uint64_t n = 2; n < limit; n++) {
    if ((*arr)[n] == PRIME) {
      for (uint64_t i = 2 * n; i < limit; i += n) {
        (*arr)[i] = COMPOSITE;
      }
    }
  }

  uint64_t clock_end = clock_nanos();
  record_call(&sieve_info, clock_start, clock_end);

  return arr;
}

int main(int argc, char **argv) {
  unsigned int iters;
  unsigned int limit;
  if (scanf("%u\n%u", &iters, &limit) == EOF) {
    fprintf(stderr, "Expected two positive intetgers (an iteration count and a limit)\n");
    return 1;
  }

  if (iters == 0) {
    return 0;
  }

  Primality **primes = NULL;
  for (unsigned int i = 0; i < iters; i++) {
    if (primes != NULL) {
      free(*primes);
    }
    free(primes);
    primes = sieve(limit);
  }

  for (unsigned int i = 0; i < limit; i++) {
    if ((*primes)[i] == PRIME) {
      printf("%u\n", i);
    }
  }

  write_report(sieve_info);

  return 0;
}
