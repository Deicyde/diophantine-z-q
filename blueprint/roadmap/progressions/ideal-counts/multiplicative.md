---
article_id: af_23536ccacc85e8fb70736142
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.idealCount_mul, ZInQ.Progressions.idealCount_one, ZInQ.Progressions.idealCountMulEquiv
---

# Ideal counts are multiplicative

Let $K$ be a number field. For coprime natural numbers $m,n$,
$$a_K(mn)=a_K(m)\,a_K(n),$$
and $a_K(1)=1$.

**Proof sketch.** The only ideal of norm $1$ is $\mathcal O_K$. The map
$(J,J')\mapsto JJ'$ sends pairs of ideals of norms $m$ and $n$ to ideals of norm $mn$, since
the norm is multiplicative. It is a bijection, with inverse
$I\mapsto(I+m\mathcal O_K,\,I+n\mathcal O_K)$: since $(m)+(n)=\mathcal O_K$, one has
$(I+(m))(I+(n))=I$ when $mn\in I$, and $JJ'+(m)=J$ when $m\in J$ and $J'+(m)=\mathcal O_K$. The
norm of $I+(m)$ divides both $m^{[K:\mathbb Q]}$ and $mn$, hence divides $m$; likewise for
$n$, and the product of the two norms is $mn$, so they are exactly $m$ and $n$. No prime
factorization is used.

## Depends on

- [The ideal counting function](ideal-count.md)

## Sources

- [Marcus, Chapter 3](../../../sources/progressions-locators.md#marcus-chapter-3)
- [Marcus, Chapter 7](../../../sources/progressions-locators.md#marcus-chapter-7)
