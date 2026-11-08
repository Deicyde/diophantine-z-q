---
article_id: af_23536ccacc85e8fb70736142
declaration: theorem
origin: background
---

# Ideal counts are multiplicative

Let $K$ be a number field. For coprime positive integers $m,n$,
$$a_K(mn)=a_K(m)\,a_K(n),$$
and $a_K(1)=1$.

**Proof sketch.** The only ideal of norm $1$ is $\mathcal O_K$. Every nonzero ideal factors
uniquely into prime ideals, the norm is multiplicative, and a prime ideal has norm a power of
the rational prime below it. Given $I$ with $N(I)=mn$, group its prime factors by whether
they lie above primes dividing $m$ or $n$: this writes $I=JJ'$ with $N(J)=m$ and $N(J')=n$,
uniquely. Conversely $N(JJ')=mn$. So $(J,J')\mapsto JJ'$ is a bijection between pairs of
ideals of norms $m$ and $n$ and ideals of norm $mn$.

## Depends on

- [The ideal counting function](ideal-count.md)

## Sources

- [Marcus, Chapter 3](../../../sources/progressions-locators.md#marcus-chapter-3)
- [Marcus, Chapter 7](../../../sources/progressions-locators.md#marcus-chapter-7)
