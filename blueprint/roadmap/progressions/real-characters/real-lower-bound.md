---
article_id: af_c04ea1b527b5dcd8b27db4eb
declaration: theorem
origin: background
---

# A lower bound for $L(1,\chi)$ at real characters

Let $q\ge1$ and let $\chi$ be a nonprincipal Dirichlet character modulo $q$ with
$\chi^2=\chi_0$. Then
$$|L(1,\chi)|\ge\frac1{40\,q^{3/2}} .$$

**Proof sketch.** Take $d$ from the classification of real characters and
$K=\mathbb Q(\sqrt d)$, with $\varepsilon_p=a_K(p)-1\in\{-1,0,1\}$. Multiply the
factorization of $\zeta_K$ by $s-1$ and let $s\to1^+$: $(s-1)\zeta_K(s)\to\kappa_K$ by the
class number formula, $(s-1)\zeta(s)\to1$, $L(s,\chi)\to L(1,\chi)$, and the finite product
is continuous. Hence
$$L(1,\chi)=\kappa_K\prod_{p\mid2q}\frac{1-\varepsilon_p/p}{1-\chi(p)/p}.$$
Each factor is at least $(1-1/p)/(1+1/p)=(p-1)/(p+1)$, and
$\prod_{p\mid2q}(p+1)/(p-1)\le3\prod_{p\mid q,\ p\text{ odd}}p\le3q$, since
$(p+1)/(p-1)\le p$ for $p\ge3$ and the factor at $p=2$ is $3$ (when $q$ is even the odd
primes dividing $q$ have product at most $q/2$). So $|L(1,\chi)|\ge\kappa_K/(3q)$. The
residue bound with $|d|\le q$ gives $\kappa_K\ge\log\frac{1+\sqrt5}2/(6\sqrt q)$, and
$\log\frac{1+\sqrt5}2>0.48>18/40$, so $|L(1,\chi)|\ge1/(40q^{3/2})$.

## Depends on

None.

## Proof depends on

- [Real characters are Legendre symbols away from $2q$](classification.md)
- [The factorization of $\zeta_K$](../ideal-counts/zeta-factorization.md)
- [Ideal counts at prime powers in a quadratic field](../ideal-counts/local-factors.md)
- [A lower bound for the residue of $\zeta_K$](../quadratic-fields/residue-bound.md)

## Sources

- [Davenport, Chapter 6](../../../sources/progressions-locators.md#davenport-chapter-6)
- [Marcus, Chapter 7](../../../sources/progressions-locators.md#marcus-chapter-7)
- [Apostol, Chapter 6](../../../sources/progressions-locators.md#apostol-chapter-6)
