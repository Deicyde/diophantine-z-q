---
article_id: af_4a49ea6f49a9d4e65eeeb83b
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Size.card_affineSolutions_le, ZInQ.Size.card_points_le, ZInQ.Size.addOrderOf_le_two_card_add_one, ZInQ.Size.odd_prime_count_bounds
---

# The trivial point count

Let $k$ be a finite field of odd characteristic and $a\in k$. Then
$$\#\{(x,y)\in k^2:y^2=x^3+ax\}+1\le2|k|+1,$$
so every element of the nonsingular group $\widetilde W_{\rm ns}(k)$ of $y^2=x^3+ax$ has order
at most $2|k|+1$. Moreover, for every odd prime $p$,
$$2p^2+1\le p^6\qquad\text{and}\qquad(2p+1)^2\le p^6 .$$

**Proof sketch.** For each $x\in k$ the equation $y^2=c$ has at most two solutions in a
field, so there are at most $2|k|$ affine points. The nonsingular group is a subset of the
affine points together with $O$, and the order of an element of a finite group is at most
the order of the group. For $p\ge3$: $2p^2+1\le3p^2\le p^6$ and $2p+1\le p^3$.

This replaces Hasse's bound $(p+1)^2<p^3$ in the manuscript: with at most two primes above
$p$, a residue field of $p$ elements at each of two split primes contributes at most
$(2p+1)^2\le p^6$, and the single inert prime with $p^2$ elements at most
$2p^2+1\le p^6$.

## Depends on

None.

## Sources

- [Proof of Proposition 12.1, formal multiple](../../../sources/size-locators.md#proof-of-proposition-121-formal-multiple)
