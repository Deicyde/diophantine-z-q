# The least formal multiple

The constant $M_0=\mathrm{LFM}(N_s)$ is the least $m\ge1$ for which the normalized
representation $(a+bs)/c$ of $1/x([m]P_0)$ has $N_s^4\mid a$, $N_s^4\mid b$ and
$\gcd(c,N_s)=1$, with inverse abscissa $0$ at the identity. The specification only defines
it; this section shows that the search succeeds at an index at most $N_s^{10}$. The
argument works for every integer $N\ge1$ in place of $N_s$ and does not use the catalogue
bound.

## Places of $K_0$

Above an odd prime $p$ there are one or two primes of $\mathbb Z[\sqrt2]$, each unramified
with residue field of at most $p^2$ elements. Conjugation permutes them, which lets one read
off $p$-adic valuations of the two rational coordinates of an element from its valuations at
these primes. At the prime $(s)$ above $2$ the model chapter's formula
$v_s(c_0+c_1s)=\min(2v_2(c_0),2v_2(c_1)+1)$ does the same.

- [Primes above an odd prime](odd-primes.md)
- [Rational coordinates at odd primes](odd-coefficient-extraction.md)

## Reduction and the filtration

Reduction modulo a prime not above $2$ is a homomorphism from the points with nonsingular
reduction onto the nonsingular points of the reduced curve, with kernel the points of
negative abscissa valuation. Over a finite field of odd characteristic the reduced curve has
at most $2|k|+1$ points, which replaces Hasse's bound used in the manuscript.

- [Reduction on the nonsingular part](reduction-homomorphism.md)
- [The trivial point count](trivial-point-count.md)

The points with $v(x)\le-2r$ form subgroups $W_r$, and multiplication by $n$ moves $W_r$
into $W_{r+v(n)}$ as long as the residue characteristic has valuation at most four. This
replaces the manuscript's formal group and logarithm isometry by an elementary statement
about valuations on $K_0$ itself.

- [The filtration by abscissa valuation](filtration.md)

## The point $P_0$ at the special places

At the prime $(d)$ above $7$ the curve has a cusp, and $P_0$ reduces to the nonsingular
point $(2,6)$ of $y^2=x^3$; at every other prime not above $2$ the reduction is good. At the
prime $(s)$, $v_s(x(P_0))=-6$ and $v_s(y(P_0))=-9$, so $P_0$ lies in $W_3$.

- [Reduction of $P_0$ at the bad place](bad-place-reduction.md)
- [$P_0$ at the dyadic place](dyadic-start.md)

## The successful index

Let $m_0$ be the product of the orders of the reductions of $P_0$ at the primes above the
odd prime divisors of $N$. Each order is at most $2|k|+1$, so $m_0\le N^6$, and $[m_0]P_0$
lies in the kernel of reduction at every such prime. Multiplying further by $N^4$ gives
$v(1/x)\ge2+8v_p(N)$ at those primes and $v_s(1/x)\ge6+16v_2(N)$ at $(s)$, which is the
required divisibility.

- [Reduction orders of $P_0$](reduction-orders.md)
- [A successful formal multiple](formal-multiple-existence.md)
