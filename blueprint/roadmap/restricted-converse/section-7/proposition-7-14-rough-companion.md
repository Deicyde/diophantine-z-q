---
article_id: af_94b43598cb3fd56b7ddcdfd8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Nonvanishing.roughCompanion, ZInQ.Manuscript.RC.Wiring.f3Target_of, ZInQ.Manuscript.RC.Wiring.F3Target
---

# Proposition 7.14: a bounded companion in the prepared filter (3.3)

Let $E/\mathbb Q$ be an elliptic curve and $S$ a finite set of primes containing $2$ and the primes of
bad reduction. Call $h$ *prepared* if $h>0$ is squarefree, $h\equiv1\pmod8$ and $h$ is prime to $S$.
Let "partitionable" and "corank zero" be predicates on parameters and $v(d)=v_2L_*(d)$, $s(d)$ functions.
Assume:

- Hoffstein–Luo for elliptic curves, the twist sign of Bump–Friedberg–Hoffstein, and modularity, which
  follow from [the cited results](../printed-results.md) and fields of [the remaining
  hypotheses](../remaining-hypotheses.md) (`RCLeaves.hl`, `RCLeaves.twistSign`, `Prints.bcdt`);
- a dummy supply (ELLIOT): a number $A_0$ such that for every prepared $h$ and finite set $X$ of primes
  there is a squarefree $a>0$ with $\omega(a)=A_0$, prime to $S$, $X$ and $h$, such that every
  $k'=au$ with $k'<0$, $k'\equiv1\pmod8$, $k'$ squarefree and a square in $\mathbb Q_p$ at every $p\in S$
  and every $p\mid h$, and with $L(E^{(hk')},1)\ne0$, makes $hk'$ partitionable;
- forward rank zero: $L(E^{(d)},1)\ne0$ implies corank zero;
- [(3.3b)](proposition-7-13-even-upper-bound.md) with a constant $C_1$.

Then there are $A$ and $C_E$ such that for every prepared $h$ with $w(E^{(h)})=-1$ and every finite set
$X$ of primes there is a negative fundamental discriminant $k'\equiv1\pmod8$, a square and a unit at
every $p\in S$ and every $p\mid h$, prime to $X$, with $hk'$ partitionable, $L(E^{(hk')},1)\ne0$, and
$$\omega(k')\le A,\qquad v_2L_*(hk')\le2\omega(h)+2\omega(k')+s(hk')+C_E.\tag{3.3}$$

The Lean constants are $A=A_0+5$ and $C_E=C_1$. The theorem takes the dummy supply as a hypothesis;
in the reduction of Theorem 5.3 it is derived from the field `PreLeaves.aux_factor`, and the
proposition is used in the form `F3Target` over the interface data, through `f3Target_of`. That field
asks for unit seeds only at the prepared total types: the manuscript prepares a seed for every total
type, which the field's docstring notes is false at negative types of root number $-1$. The condition
$k'\equiv1\pmod8$ excludes the fields with extra units.

**Proof sketch.** The dummies are fixed before $h$. For given $h$ and $X$, realize them by the product
$a$, absorb $h$ and $a$ into the curve, and apply the even case of [Proposition
7.3](proposition-7-3-nonvanishing.md) to $E^{(ha)}$ in the filter that makes $k'=au$ negative,
$\equiv1\pmod8$ and a square at $S$ and at the primes of $h$; it adds at most five primes. The dummy
supply makes $hk'$ partitionable, nonvanishing gives corank zero, and (3.3b) gives the bound, since
$\omega(hk')=\omega(h)+\omega(k')$.

## Depends on

- [The cited results](../printed-results.md)
- [The remaining hypotheses](../remaining-hypotheses.md)
- [Proposition 7.13: the partitionable even upper bound (3.3b)](proposition-7-13-even-upper-bound.md)

## Proof depends on

- [Proposition 7.3: nonvanishing in a signed unit filter](proposition-7-3-nonvanishing.md)

## Sources

- [Section 7](../../../sources/manuscript.md#section-7)
