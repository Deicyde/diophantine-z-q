---
article_id: af_85601b4f63ca8f5eb41719f4
declaration: theorem
origin: background
---

# An effective Dirichlet theorem

Let $q\ge2^{16}$ be an integer and $a$ an integer coprime to $q$. Then at least $22$ primes
$p\equiv a\pmod q$ satisfy
$$q^2<p<2^{q^8} .$$

**Proof sketch.** By the uniform bound for twisted sums, the hypothesis of the twenty-two
primes statement holds with $B=2^{24}q^5$. Take $y=q^2$ and $x=2^{q^8}$, so
$\log(x/y)=q^8\log2-2\log q$. Since $q\ge2^{16}$, $q^8\log2\ge q^8/2\ge2^{31}q^6$, while
$q(2B+11)+12+\log q+2\log q=2^{25}q^6+11q+12+3\log q\le2^{26}q^6$. So at least $22$ primes
$p\equiv a\pmod q$ lie in $(q^2,2^{q^8}]$, and $2^{q^8}$ itself is not prime.

The bound is far from sharp: the proof gives such primes below $\exp(C q^6)$ for an explicit
$C$, and the exponent $8$ leaves room for cruder constants.

## Depends on

None.

## Proof depends on

- [A uniform bound for twisted sums](counting/uniform-twisted-bound.md)
- [Twenty-two primes from a twisted sum bound](counting/twentytwo-primes.md)

## Sources

- [Apostol, Chapter 7](../../sources/progressions-locators.md#apostol-chapter-7)
- [Davenport, Chapter 4](../../sources/progressions-locators.md#davenport-chapter-4)
