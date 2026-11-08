---
article_id: af_ae76263b094e8b8df983f7ad
---

# Counting primes in a residue class

The count follows the classical proof of Dirichlet's theorem with explicit constants.
Mertens' first theorem controls $\sum_{n\le x}\Lambda(n)/n$ to within $3$, and the
principal character inherits this up to the primes dividing $q$.

- [Mertens' first theorem](mertens.md)
- [The principal character](principal-character.md)

For a nonprincipal $\chi$, the identity $\log n=\sum_{d\mid n}\Lambda(d)$ relates
$L(1,\chi)\sum_{n\le x}\chi(n)\Lambda(n)/n$ to the bounded sum
$\sum_{n\le x}\chi(n)\log n/n$, so the twisted sum is at most $(M^2+6q)/|L(1,\chi)|$; the
lower bounds for $|L(1,\chi)|$ of the preceding sections combine into one bound for all
nonprincipal characters.

- [The twisted sum and $L(1,\chi)$](twisted-sum-bound.md)
- [A lower bound for $|L(1,\chi)|$ at every nonprincipal character](uniform-lower-bound.md)

Orthogonality isolates one residue class; above $y=q^8$, prime powers with exponent at least
$2$ add less than $1/5$ and each prime adds at most $\log y/y$. So the interval
$(q^8,q^8e^{5qB}]$ holds twenty-two primes of the class when every twisted sum is at most $B$.

- [Detecting a residue class by characters](orthogonality.md)
- [Higher prime powers contribute little](prime-powers.md)
- [Twenty-two primes from a twisted sum bound](twentytwo-primes.md)
