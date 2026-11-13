---
article_id: af_1c33d93dc5c1b83fd43ca980
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Translation.four_squares
---

# Lagrange's four-square theorem

For every natural number $n$ there are natural numbers $a_0,a_1,a_2,a_3$ with
$$n=a_0^2+a_1^2+a_2^2+a_3^2 .$$

**Proof sketch.** Classical. By Euler's four-square identity the set of sums of four
integer squares is closed under multiplication, so it suffices to treat primes; $2=1+1+0+0$.
For an odd prime $p$ the $(p+1)/2$ values $x^2$ and the $(p+1)/2$ values $-1-y^2$ modulo $p$
cannot be pairwise distinct, so $x^2+y^2+1\equiv0\pmod p$ for some $x,y$; hence some multiple
$mp$ with $1\le m<p$ is a sum of four squares, and the least such $m$ is $1$ by Euler's
descent. Replacing each integer $a_i$ by $|a_i|$ gives natural numbers.

## Depends on

None.

## Sources

- [Lagrange four squares](../../../sources/compiler-translation-locators.md#lagrange-four-squares)
- [Section 3.1](../../../sources/compiler-translation-locators.md#section-31-natural-predicate)
