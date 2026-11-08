---
article_id: af_ae76263b094e8b8df983f7ad
---

# Counting primes in a residue class

The count follows the classical proof of Dirichlet's theorem with explicit constants.
Mertens' first theorem controls $\sum_{n\le x}\Lambda(n)/n$ to within $6$, and the
principal character inherits this up to the primes dividing $q$.

- [Mertens' first theorem](mertens.md)
- [The principal character](principal-character.md)

For a nonprincipal $\chi$, the identity $\log n=\sum_{d\mid n}\Lambda(d)$ relates
$L(1,\chi)\sum_{n\le x}\chi(n)\Lambda(n)/n$ to the bounded sum
$\sum_{n\le x}\chi(n)\log n/n$, and the lower bounds for $|L(1,\chi)|$ of the preceding
sections make the twisted sum at most $2^{24}q^5$.

- [The twisted sum and $L(1,\chi)$](twisted-sum-bound.md)
- [A uniform bound for twisted sums](uniform-twisted-bound.md)

Orthogonality isolates one residue class; prime powers with exponent at least $2$ add at
most $3$; each prime adds at most $1/e$. So a long enough interval holds twenty-two primes
of the class.

- [Detecting a residue class by characters](orthogonality.md)
- [Higher prime powers contribute little](prime-powers.md)
- [Twenty-two primes from a twisted sum bound](twentytwo-primes.md)
