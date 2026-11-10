---
article_id: af_38d0094a627fbd5bd12b0d7a
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Density.pointCount_eq, ZInQ.Density.jac, ZInQ.Density.jac_sq_mul, ZInQ.Density.jac_zero, ZInQ.Density.sum_quadraticChar_shift_mul, ZInQ.Density.sum_quadraticChar_shift_mul_self, ZInQ.Density.jac_eq_cubicCharSum, ZInQ.Density.card_mod_two_eq_card_fixed
---

# Character sums for the curves $y^2=x^3+ax$

Let $p$ be an odd prime, $\chi$ the quadratic character of $\mathbb F_p$, and for $a\in\mathbb F_p$
put $\varphi_p(a)=\sum_{x\in\mathbb F_p}\chi(x^3+ax)$. Let $\#E_a(\mathbb F_p)$ be the number of
solutions of $y^2=x^3+ax$ over $\mathbb F_p$ plus one (the point at infinity). Then:

1. $\#E_a(\mathbb F_p)=p+1+\varphi_p(a)$;
2. $\varphi_p(k^2a)=\chi(k)\,\varphi_p(a)$ for $k\in\mathbb F_p^\times$, and $\varphi_p(0)=0$;
3. $\sum_{t\in\mathbb F_p}\chi\bigl((t+\alpha)(t+\beta)\bigr)=-1$ for $\alpha\ne\beta$, and $=p-1$ for
   $\alpha=\beta$.

**Proof sketch.** (1) The equation $y^2=c$ has $1+\chi(c)$ solutions; sum over $x$ with
$c=x^3+ax$. (2) Substitute $x=kX$: $(kX)^3+k^2a\,kX=k^3(X^3+aX)$ and $\chi(k^3)=\chi(k)$; and
$\varphi_p(0)=\sum\chi(x)^3=\sum\chi(x)=0$. (3) For $t\ne-\beta$ the summand is
$\chi\bigl((t+\alpha)/(t+\beta)\bigr)$, and $t\mapsto(t+\alpha)/(t+\beta)$ is a bijection of
$\mathbb F_p\setminus\{-\beta\}$ onto $\mathbb F_p\setminus\{1\}$, so the sum is
$\sum_{w\ne1}\chi(w)=-1$. The Lean proofs reuse the character sums of the Selmer chapter, since
$\varphi_p(a)$ is the cubic character sum at $-a$.

## Depends on

None.

## Sources

- [Character sums](../../sources/density-locators.md#character-sums)
