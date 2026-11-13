---
article_id: af_b748c0f7e1277d9d92558eb9
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Density.jacobsthal, ZInQ.Density.jac_even, ZInQ.Density.sum_jac_sq
---

# Jacobsthal's identity

Let $p$ be an odd prime. Every $\varphi_p(a)$ is even, and
$\sum_{a\in\mathbb F_p}\varphi_p(a)^2=p(p-1)(1+\chi(-1))$. If $p\equiv1\pmod4$ and $r\in\mathbb F_p$ is
not a square, then
$$\varphi_p(1)^2+\varphi_p(r)^2=4p .$$

**Proof sketch.** *Evenness:* for $x\ne0$, $\chi(x^3+ax)=\chi(x)\chi(x^2+a)$, and the involution
$x\mapsto-x$ pairs the summands (for $p\equiv3\pmod 4$ they cancel, for $p\equiv1$ they agree), its
fixed point $x=0$ contributing $0$. *Second moment:* by the shifted product sums,
$\sum_a\varphi_p(a)^2=\sum_{x,y}\chi(x)\chi(y)\sum_a\chi\bigl((a+x^2)(a+y^2)\bigr)=p(p-1)(1+\chi(-1))$,
which is $2p(p-1)$ for $p\equiv1\pmod4$. *Square classes:* $\varphi_p(0)=0$ and, by scaling,
$\varphi_p(a)^2$ is $\varphi_p(1)^2$ on the $(p-1)/2$ nonzero squares and $\varphi_p(r)^2$ on the
$(p-1)/2$ non-squares; so $\tfrac{p-1}2\bigl(\varphi_p(1)^2+\varphi_p(r)^2\bigr)=2p(p-1)$.

## Depends on

- [Character sums for the curves $y^2=x^3+ax$](character-sums.md)

## Sources

- [Character sums](../../sources/density-locators.md#character-sums)
