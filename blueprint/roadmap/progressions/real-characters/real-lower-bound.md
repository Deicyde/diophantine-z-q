---
article_id: af_c04ea1b527b5dcd8b27db4eb
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.norm_LFunction_one_ge_of_sq_eq_one, ZInQ.Progressions.log_golden_div_le_norm_LFunction_one
---

# A lower bound for $L(1,\chi)$ at real characters

Let $q\ge1$ and let $\chi$ be a nonprincipal Dirichlet character modulo $q$ with
$\chi^2=\chi_0$. Then
$$|L(1,\chi)|\ge\frac1{40\,q^{3/2}} .$$

**Proof sketch.** Take $d$ from the classification of real characters: $d\ne1$ is squarefree,
$|d|$ divides $q$, and $\chi(p)=(d/p)$ for every prime $p\nmid2q$. Then $d$ is not the square
of a rational number; let $K=\mathbb Q(\sqrt d)$, with $\alpha=\sqrt d\in\mathcal O_K$ and
$\varepsilon_p=a_K(p)-1\in\{-1,0,1\}$. Since $|d|$ divides $q$, no prime $p\nmid2q$ divides
$d$, so the factorization of $\zeta_K$ applies: for real $s>1$,
$$\zeta_K(s)=\zeta(s)\,L(s,\chi)\prod_{p\mid2q}\frac{1-\chi(p)p^{-s}}{1-\varepsilon_pp^{-s}},$$
where $L(s,\chi)$, the sum of the Dirichlet series, is the value of the $L$-function. Multiply
by $s-1$ and let $s\to1^+$: $(s-1)\zeta_K(s)\to\kappa_K$ by the class number formula,
$(s-1)\zeta(s)\to1$, $L(s,\chi)\to L(1,\chi)$ by continuity, and the finite product is
continuous at $s=1$ (its denominators do not vanish since $|\varepsilon_p|\le1<p$). Hence
$$\kappa_K=L(1,\chi)\prod_{p\mid2q}\frac{1-\chi(p)/p}{1-\varepsilon_p/p}.$$
Each factor has absolute value at most $(1+1/p)/(1-1/p)=(p+1)/(p-1)$, and
$\prod_{p\mid2q}(p+1)/(p-1)\le3\prod_{p\mid q,\ p\text{ odd}}p\le3q$, since
$(p+1)/(p-1)\le p$ for $p\ge3$ and the factor at $p=2$ is $3$. So $|L(1,\chi)|\ge\kappa_K/(3q)$.
The residue bound with $|d|\le q$ gives $\kappa_K\ge\log\frac{1+\sqrt5}2/(6\sqrt q)$, and
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
