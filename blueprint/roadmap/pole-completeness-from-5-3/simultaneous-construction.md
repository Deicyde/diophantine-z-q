---
article_id: af_69935b0fbbad060da4a03217
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.PoleS12.simultaneousConstruction, ZInQ.Manuscript.PoleRC.SimultaneousConstruction
---

# The simultaneous construction

Let $\beta$ and $\theta$ be positive squarefree integers with $\beta\equiv17$ and $\theta\equiv1\pmod{24}$,
coprime, each a square modulo every prime of the other. Then there is $n>0$ with $n\theta$ squarefree and
$n\equiv11\pmod{12}$ such that the explicit 2-Selmer systems of $E_n$ and $E_{n\theta}$ both have eight
elements and contain $(\beta,1)$. Here $E_\ell:y^2=x(x-\ell)(x+3\ell)$, and the explicit 2-Selmer system is
as in [Lemma 5.4](lemma-5-4.md).

**Proof sketch.** The manuscript prints the matrix conditions over $\mathbb F_2$ (a matrix $K$ of Legendre
symbols on the primes of $n$, with prescribed kernel and image) and the count that gives dimension three,
and leaves the construction of $n$ to its supplementary files S11 and S12. The Lean proof follows S12. It
chooses auxiliary primes one at a time, each with a prescribed class modulo $12$ and prescribed Legendre
symbols modulo the primes already fixed, by the Chinese remainder theorem and Dirichlet's theorem, so that
the matrix conditions hold for both $n$ and $n\theta$. It then proves every local condition of the count:
at $2$, at $3$, at the primes of $n$ and at every other prime. Only eight candidate classes survive the
necessary conditions, and each is shown to be local everywhere.

## Depends on

None.

## Sources

- [Section 5.1](../../sources/manuscript.md#section-51)
