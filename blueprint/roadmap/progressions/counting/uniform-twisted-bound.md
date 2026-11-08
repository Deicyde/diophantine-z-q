---
article_id: af_2bb9d092ac43a2d8ca9d38bb
declaration: theorem
origin: background
---

# A uniform bound for twisted sums

Let $q\ge1$ and let $\chi$ be a nonprincipal Dirichlet character modulo $q$. For every real
$x\ge1$,
$$\Bigl|\sum_{n\le x}\frac{\chi(n)\Lambda(n)}{n}\Bigr|\le2^{24}q^5 .$$

**Proof sketch.** Let $M=\log q+3$. From $\log t\le t-1$ at $t=\sqrt q$,
$\log q\le2\sqrt q-2$, so $M\le3\sqrt q$, $M^2\le9q$ and $M^2+12q\le21q$. By the twisted sum
bound, $|S_\chi(x)|\le(M^2+12q)/|L(1,\chi)|$, the value $L(1,\chi)$ being nonzero by either
lower bound below. If $\chi^2\ne\chi_0$, then $|L(1,\chi)|\ge1/(256M^7)$ and
$|S_\chi(x)|\le256\cdot3^7q^{7/2}\cdot21q\le11757312\,q^5<2^{24}q^5$. If $\chi^2=\chi_0$,
then $|L(1,\chi)|\ge1/(40q^{3/2})$ and $|S_\chi(x)|\le40q^{3/2}\cdot21q=840q^{5/2}\le2^{24}q^5$.

## Depends on

None.

## Proof depends on

- [The twisted sum and $L(1,\chi)$](twisted-sum-bound.md)
- [A lower bound for $|L(1,\chi)|$ at complex characters](../lseries/complex-lower-bound.md)
- [A lower bound for $L(1,\chi)$ at real characters](../real-characters/real-lower-bound.md)

## Sources

- [Apostol, Chapter 7](../../../sources/progressions-locators.md#apostol-chapter-7)
