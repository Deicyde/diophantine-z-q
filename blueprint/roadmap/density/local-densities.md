---
article_id: af_e71448061e96f47d0033132e
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Density.GaussSieve.card_zset_prod, ZInQ.Density.GaussSieve.ZSet, ZInQ.Density.GaussSieve.card_zset_prime, ZInQ.Density.GaussSieve.card_zset_mul
---

# Local densities of $(\ell U)^2+(b+\ell V)^2$

Let $\ell,b$ be integers and $F(U,V)=(\ell U)^2+(b+\ell V)^2$. For a prime $q\equiv1\pmod4$ with
$q\nmid\ell$, the equation $F(U,V)=0$ has exactly $2q-1$ solutions in $\mathbb F_q^2$. Consequently, for
a finite set $t$ of such primes and $d=\prod_{q\in t}q$, the congruence $F(U,V)\equiv0\pmod d$ has exactly
$\prod_{q\in t}(2q-1)$ solutions in $(\mathbb Z/d)^2$.

**Proof sketch.** $(U,V)\mapsto(\ell U,b+\ell V)$ is a bijection of $\mathbb F_q^2$ since $\ell$ is
invertible. With $i^2=-1$ in $\mathbb F_q$, $x^2+y^2=(x-iy)(x+iy)$ vanishes exactly on two lines meeting
only at $0$: $2q-1$ points. The Chinese remainder theorem makes the count multiplicative in $d$.

## Depends on

None.

## Sources

- [The sieve](../../sources/density-locators.md#the-sieve)
