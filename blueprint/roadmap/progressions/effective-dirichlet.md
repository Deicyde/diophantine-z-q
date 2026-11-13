---
article_id: af_85601b4f63ca8f5eb41719f4
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.effective_dirichlet
---

# An effective Dirichlet theorem

Let $q\ge2^{16}$ be an integer and $a$ an integer coprime to $q$. Then at least $22$ primes
$p\equiv a\pmod q$ satisfy
$$q^2<p<2^{q^8} .$$

**Proof sketch.** Put $M=\log q+3$ and $c=\min\bigl(1/(256M^7),1/(40q^{3/2})\bigr)$. By the
lower bound at every nonprincipal character, $|L(1,\chi)|\ge c$ for all $\chi\ne\chi_0$, so
the twenty-two primes statement gives $22$ primes $p\equiv a\pmod q$ with
$q^8<p\le q^8e^{5qB}$, where $B=(M^2+6q)/c$. It remains to show $q^8e^{5qB}<2^{q^8}$. From
$\log t\le t-1$ at $t=\sqrt q$, $\log q\le2\sqrt q-2$, so $M\le3\sqrt q$ and
$M^2+6q\le15q$. Then $1/c=\max(256M^7,40q^{3/2})\le256\cdot3^7q^{7/2}\le2^{20}q^{7/2}$, so
$B\le15\cdot2^{20}q^{9/2}$ and $8\log q+5qB\le8q+2^{27}q^{11/2}\le2^{28}q^{11/2}$. Since
$q\ge2^{16}$, $q^{5/2}\ge2^{40}$ and $q^8\log2\ge q^8/2\ge2^{39}q^{11/2}$. Hence
$\log(q^8e^{5qB})<q^8\log2$, and every such prime satisfies $q^2<q^8<p<2^{q^8}$.

The bound is far from sharp: the proof gives such primes below $\exp(Cq^{11/2})$ for an
explicit $C$, and the exponent $8$ leaves room for cruder constants.

## Depends on

None.

## Proof depends on

- [A lower bound for $|L(1,\chi)|$ at every nonprincipal character](counting/uniform-lower-bound.md)
- [Twenty-two primes from a twisted sum bound](counting/twentytwo-primes.md)

## Sources

- [Apostol, Chapter 7](../../sources/progressions-locators.md#apostol-chapter-7)
- [Davenport, Chapter 4](../../sources/progressions-locators.md#davenport-chapter-4)
