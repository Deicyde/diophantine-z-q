---
article_id: af_ea9fc206c9b7c3d897205e2c
---

# The construction: the polynomial and why its zeros project to ℤ

The target polynomial $P_*$ is written down explicitly, as a finite composition of existential gadgets
([the specification](syntax/README.md)): sums of squares express conjunction over $\mathbb Q$, products
express disjunction, and each call of a template gets a fresh block of witness variables. A few
astronomically large constants enter through their defining expressions and are never evaluated.

**Integers as points.** The polynomial never handles an integer index directly. It represents $n$ by the
five rational coordinates of $[n]P_0$, a multiple of a fixed point on an elliptic curve over
$\mathbb Q(\sqrt2)$. [The elliptic model](model/README.md) proves that this coding is faithful: the codes
form the infinite cyclic group $\mathbb ZP_0$, a membership polynomial recognizes exactly the codes among
all rational inputs, and raw addition of codes is the group law. The Mordell–Weil theorem for this curve,
which the coding needs, is proved.

**Multiplication.** [The multiplication template](multiplication/README.md) accepts a triple of codes
exactly when it is $\iota(a),\iota(b),\iota(ab)$. Its soundness, on arbitrary rational inputs, uses the
height input. Its completeness uses pole completeness for the pole witnesses and needs every integer to
be a sum of three good slopes; the manuscript gets this from a pattern of twenty-two primes, and this project instead from long arithmetic progressions of
good primes ([route AP](route-ap/README.md), with [Szemerédi's theorem in the primes](green-tao/README.md)
and [the density of good slope primes](density/README.md)).

**The value relation.** A rational input $t$ comes with a code of an integer index $n$, and
[the assembly](assembly/README.md) must force $t=n$. For six exceptional values of $n$ a branch says so
outright. Otherwise a shift $\kappa$ is chosen, and two relations share it. *Close* says that $t$ lies
within $e^{-B(n,\kappa)}$ of $n$; it rests on [an exact precision computation](compiler/README.md) compiled
into point-code constraints. *Test* forms six local tests from the shift; its soundness uses the pole
obstruction and the height input to bound the height of $t$ by $B(n,\kappa)$, and its completeness chooses a shift
deep in the formal groups and uses pole completeness for the pole witness. A rational number of height at most $B$ that lies within
$e^{-B}$ of an integer is that integer, so the value relation is exactly the graph $t=n$, and the rational
zero projection of $P_*$ is $\mathbb Z$.

**Size.** [The size chapter](size/README.md) bounds the constants symbolically and proves that $P_*$ has
degree below $2\uparrow\uparrow7$ and coefficients below $2\uparrow\uparrow8$; the prime catalogue it needs
comes from [an effective Dirichlet theorem](progressions/README.md).

Everything in this part is proved in Lean, with every finite computation checked by the kernel. The two
inputs, the height estimate and pole completeness, are the subject of the next two parts.
