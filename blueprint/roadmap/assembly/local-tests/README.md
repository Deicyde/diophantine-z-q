---
article_id: af_adb97b4864b033078289530c
---

# The six local tests

The relation Test (defined with the value templates) puts the six tests $D_1,\dots,D_6$ over
the common denominator $F(t)$, forms $W=\prod(1+RC_j^2)$, the trace $\Theta=\operatorname{Tr}(W^{-1})$ and
one pole instance $\Phi(R/\Theta^2)$. Both lemmas about it are local: soundness works at the
primes above one contact prime $p>324$, completeness at the primes above $2730^6F(n)$ and at
the two real places.

## Valuations and formal groups

Odd primes are unramified in $\mathbb Z[s]$ and the trace of an element that is small at the
primes above $p$ is small at $p$
([the primes above an odd prime](../../multiplication/local/primes-above-p.md)); $2$ is ramified,
and at $(s)$ the trace gains one more power of $2$.

- [Valuation and trace at the prime $(s)$](dyadic-trace.md)

At every prime, the points with negative abscissa valuation form a filtration by subgroups
([the formal neighbourhood and its filtration](../../multiplication/local/formal-group.md)), on
which $z=-x/y$ is additive up to terms of five times the depth. The manuscript uses the formal
logarithm; the following elementary statement gives what is needed, including
$z([m]Q)=m\,z(Q)\cdot(\text{unit}\equiv1)$ at an odd prime.

- [Multiplication in a formal neighbourhood](formal-multiplication.md)

## Soundness

At a prime above a contact prime $p$, the pole obstruction forces the pole input to have
positive valuation, which makes all six tests small at one prime above $p$. The first four
put the four points in formal groups, and the last two, through the multiplication
estimate, give $s_0/h\equiv t$ and $(s_0-\kappa n)/(h-\kappa)\equiv t$, hence $p\mid\kappa(n-c)$.

- [Divisibility from the six local tests](test-divisibility.md)

## Completeness

Some multiple of $P_0$ lies in any given formal neighbourhood: at the primes above an odd
prime by the reduction orders of the size chapter
([reduction orders of $P_0$](../../size/formal-multiple/reduction-orders.md)), including the bad
prime $d$, and at $s$ because $P_0$ already lies in the dyadic formal group
([the generator in the dyadic formal group](../../multiplication/local/dyadic-generator.md)).

- [Deep multiples of the generator](deep-multiples.md)

With such a shift the tests are divisible by $F(n)$ at every prime of $R_0$, so $W\equiv1$ and
$\Theta\equiv2$ there and the pole input has the local properties required by pole completeness;
a rational $q$ close to $R_0^{-1/2}$ makes it lie in $(0,1/2)$.

- [Local conditions on the pole input](pole-input-local.md)
- [Real conditions on the pole input](pole-input-real.md)
- [One suitable shift](test-completeness.md)
