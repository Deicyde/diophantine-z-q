/* C3 (fast version of pattern_search.py). Progression n = RHO + 840 k, RHO = 241:
   n = 1 mod 8, 3 mod 7, 1 mod 3, 1 mod 5. Bit k is set iff n is a good prime
   (prime, and gcd(a, n+1) has no odd prime factor where n = a^2 + b^2, a odd).
   usage: psearch NMAX mode(sum|diff) A [A ...]
   sum : u1, u2 = RHO mod 1680, v = 1680 w (w odd); the 18 numbers u_j + |c| v (j = 1, 2)
         and (u1 + u2 - (A - c) v)/2 must be good primes.
   diff: u = RHO mod 1680, v = 1680 w; the numbers u - c v, c in C u (A + C), good primes.
   two : as diff with C u (A + 10 - C): slopes u/v, A + 10 - u/v and the fixed slope -10. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef unsigned __int128 u128;
static uint64_t *bits; static uint64_t K;
#define GET(k) ((bits[(k) >> 6] >> ((k) & 63)) & 1)
#define CLR(k) (bits[(k) >> 6] &= ~(1ULL << ((k) & 63)))
static const uint64_t RHO = 241, STEP = 840;
static const int64_t C[6] = {0, -15, -20, -24, -30, -60};
static uint64_t mulmod(uint64_t a, uint64_t b, uint64_t m) { return (u128)a * b % m; }
static uint64_t powmod(uint64_t a, uint64_t e, uint64_t m) {
  uint64_t r = 1; a %= m;
  while (e) { if (e & 1) r = mulmod(r, a, m); a = mulmod(a, a, m); e >>= 1; }
  return r;
}
static uint64_t gcd64(uint64_t a, uint64_t b) { while (b) { uint64_t t = a % b; a = b; b = t; } return a; }
static int good_given_prime(uint64_t p) {
  uint64_t x = powmod(7, (p - 1) / 4, p);         /* 7 is a non-residue: (7/p) = (p/7) = -1 */
  if (mulmod(x, x, p) != p - 1) return -1;        /* should not happen */
  uint64_t r0 = p, r1 = x, lim = (uint64_t)sqrtl((long double)p);
  while (lim * lim > p) lim--; while ((lim + 1) * (lim + 1) <= p) lim++;
  while (r1 > lim) { uint64_t t = r0 % r1; r0 = r1; r1 = t; }
  uint64_t a = r1, b2 = p - a * a, b = (uint64_t)sqrtl((long double)b2);
  while (b * b > b2) b--; while ((b + 1) * (b + 1) <= b2) b++;
  if (b * b != b2) return -1;
  if (a % 2 == 0) { uint64_t t = a; a = b; b = t; }
  uint64_t g = gcd64(a, p + 1);
  while (g % 2 == 0) g /= 2;
  return g == 1;
}
static int good_idx(int64_t k) { return k >= 0 && (uint64_t)k < K && GET((uint64_t)k); }
int main(int argc, char **argv) {
  uint64_t NMAX = (uint64_t)atof(argv[1]); const char *mode = argv[2];
  K = (NMAX - RHO) / STEP + 1;
  bits = malloc(((K >> 6) + 1) * 8); memset(bits, 0xff, ((K >> 6) + 1) * 8);
  uint64_t Q = (uint64_t)sqrt((double)NMAX) + 2;
  char *comp = calloc(Q + 1, 1);
  for (uint64_t q = 2; q <= Q; q++) {
    if (comp[q]) continue;
    for (uint64_t m = q * q; m <= Q; m += q) comp[m] = 1;
    if (STEP % q == 0) continue;
    uint64_t inv = powmod(STEP % q, q - 2, q);
    uint64_t k0 = mulmod((q - RHO % q) % q, inv, q);
    if (RHO + STEP * k0 == q) k0 += q;
    for (uint64_t k = k0; k < K; k += q) CLR(k);
  }
  uint64_t ngood = 0;
  for (uint64_t k = 0; k < K; k++) if (GET(k)) {
    int g = good_given_prime(RHO + STEP * k);
    if (g < 0) { fprintf(stderr, "two-squares failure at %llu\n", (unsigned long long)(RHO + STEP * k)); return 1; }
    if (!g) CLR(k); else ngood++;
  }
  fprintf(stderr, "good primes in progression up to %.2e: %llu\n", (double)NMAX, (unsigned long long)ngood);
  int64_t *L = malloc(sizeof(int64_t) * 4000000);
  for (int ai = 3; ai < argc; ai++) {
    int64_t A = atoll(argv[ai]); int found = 0;
    int64_t absA = A < 0 ? -A : A;
    if (!strcmp(mode, "sum")) {
      uint64_t Ymax = K / 4;
      for (int64_t w = 1; !found && (uint64_t)((absA + 61) * 2 * w) < Ymax; w += 2) {
        size_t n = 0;
        for (uint64_t k = 0; k < Ymax && n < 4000000; k += 2) {
          int ok = 1;
          for (int j = 0; j < 6 && ok; j++) ok = good_idx((int64_t)k - 2 * C[j] * w);
          if (ok) L[n++] = (int64_t)k;
        }
        for (size_t i = 0; i < n && !found; i++) for (size_t j = i; j < n && !found; j++) {
          int ok = 1;
          for (int c = 0; c < 6 && ok; c++) ok = good_idx((L[i] + L[j]) / 2 - (A - C[c]) * w);
          if (ok) {
            printf("sum A=%lld u1=%llu u2=%llu v=%llu\n", (long long)A,
                   (unsigned long long)(RHO + STEP * L[i]), (unsigned long long)(RHO + STEP * L[j]),
                   (unsigned long long)(1680 * w));
            found = 1;
          }
        }
      }
    } else {
      int64_t sh[12]; int ns = 0;
      for (int j = 0; j < 6; j++) sh[ns++] = C[j];
      int two = !strcmp(mode, "two");   /* t1 + t2 + (-10) = A: second set A + 10 - C */
      for (int j = 0; j < 6; j++) { int64_t s = two ? A + 10 - C[j] : A + C[j], dup = 0; for (int i = 0; i < ns; i++) dup |= sh[i] == s; if (!dup) sh[ns++] = s; }
      uint64_t Ymax = K / 2;
      for (int64_t w = 1; !found && (uint64_t)((absA + 61) * 4 * w) < Ymax; w += 2) {
        for (uint64_t k = 0; k < Ymax && !found; k += 2) {
          int ok = 1;
          for (int j = 0; j < ns && ok; j++) ok = good_idx((int64_t)k - 2 * sh[j] * w);
          if (ok) {
            printf("%s A=%lld u=%llu v=%llu\n", mode, (long long)A, (unsigned long long)(RHO + STEP * k),
                   (unsigned long long)(1680 * w));
            found = 1;
          }
        }
      }
    }
    if (!found) printf("%s A=%lld none\n", mode, (long long)A);
    fflush(stdout);
  }
  return 0;
}
