---
article_id: af_e8e8162e3cfc1f5d821f3ae1
declaration: def
origin: cited
statement: formalized
lean: ZInQ.FixedPrimePattern
---

# The twenty-two-prime pattern

Let $P_s$ be the product of the primes at most $324$ and $W=4P_s$. Let $\mathcal H$ consist
of the first twenty-two primes greater than $324$ in each unit residue class modulo $W$,
and $\mathcal K=\{dh: d\mid P_s^4,\ d>0,\ h\in\mathcal H\}$. Call a prime $p$ good if it
splits in $\mathbb Q(\sqrt2)$, both reductions of $E$ at the places above $p$ are good, and
their orders $d_1,d_2$ satisfy $\gcd(d_1,d_2)=4$ and $p\nmid d_1d_2$.

The pattern assertion is that for every $A\in\mathbb Z$ and every real $B_0$ there are
integers $u_1,u_2,v$ with $v\ne0$ such that, with $u_3=Av-u_1-u_2$, each of the
twenty-two values
$$v,\qquad u_j-bv\quad(1\le j\le3,\ b\in\{0,-15,-20,-24,-30,-60,1\})$$
equals $\epsilon kp$ with $\epsilon=\pm1$, $k\in\mathcal K$ and $p>B_0$ a good prime.

The manuscript proves it with the Green–Tao asymptotic for linear equations in primes;
here it is a hypothesis of the main theorem.

## Depends on

None.

## Sources

- [Proposition 6.2](../../sources/manuscript.md#proposition-62)
