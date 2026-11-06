---
article_id: af_429f9b160ce7eb19cb6edb13
declaration: def
origin: cited
---

# The precision quantities and the precision predicate

Let $\sigma$ be the conjugation $s\mapsto-s$ of $K_0$, $\operatorname{Tr}(\alpha)=\alpha+\sigma(\alpha)$
the trace to $\mathbb Q$ (so $\operatorname{Tr}(a+bs)=2a$), and $\sigma_\pm:K_0\to\mathbb R$ the two
real embeddings, $\sigma_\pm(a+bs)=a\pm b\sqrt2$.

**Local parameter and inverse abscissa.** For $Q\in E(K_0)$ put
$$z(Q)=-x/y,\qquad w(Q)=1/x\qquad\text{if }Q=(x,y)\text{ is affine with }x\ne0,\ y\ne0,$$
and $z(O)=w(O)=0$ (and $z=w=0$ at the three affine points with $xy=0$, which never occur
below). For $m\in\mathbb Z$ write $z_m=z([m]P_0)\in K_0$ and $z_m=u_m+v_ms$ with
$u_m,v_m\in\mathbb Q$.

**The coordinate window.** For $l,a,j\in\mathbb Z$ put
$$\epsilon_l=|u_l|+|v_l|\in\mathbb Q,\qquad r(a,j)=\tfrac12\operatorname{Tr}\bigl(z_j/z_a\bigr)\in\mathbb Q,$$
with $r(a,j)=0$ when $z_a=0$. Thus $r(a,j)$ is the rational component of $z_j/z_a$.

**The height constant.** Let $\mathcal C=\{0,-15,-20,-24,-30,-60\}$,
$F(u)=u(u+15)(u+20)(u+24)(u+30)(u+60)$, and $S_{\rm ht}$ the set of primes $p\le324$, whose
largest element is $317$. With the constants $D,E_0,C_{\rm cm}$ of the six-contact estimate,
let $R_{\rm ht}=\max(D,317,10^{12})$ and
$$A_0=H_6(S_{\rm ht})=2\cdot10^{13}\max\bigl(1,\ C_{\rm cm},\ Q_{R_{\rm ht}}^{17}\bigr),\qquad Q_{R_{\rm ht}}=R_{\rm ht}^{R_{\rm ht}E_0},$$
a positive integer. For $n,\kappa\in\mathbb Z$ put
$$B(n,\kappa)=A_0\,|\kappa F(n)|^{24}\in\mathbb N .$$
$A_0$ is astronomically large; it is only ever handled through this defining expression
and is never evaluated.

**Signed encoding.** $\operatorname{enc}:\mathbb Z\to\mathbb N$ is $\operatorname{enc}(m)=2m$ for
$m\ge0$ and $-2m-1$ for $m<0$; $\operatorname{dec}:\mathbb N\to\mathbb Z$ is $\operatorname{dec}(c)=c/2$
for even $c$ and $-(c+1)/2$ for odd $c$. They are inverse bijections.

**The precision predicate.** For $n,\kappa,a,l,j\in\mathbb Z$, $\operatorname{Prec}(n,\kappa,a,l,j)$ is
the conjunction of
$$n\notin\mathcal C,\quad\kappa\ne0,\quad a\ge1,\quad l\ge1,\quad j=na,\quad
|r(a,j)-n|<\epsilon_l,\quad 4\epsilon_l\cdot4^{B(n,\kappa)}<1 .$$
The last condition is the manuscript's $4\epsilon_l<4^{-A^{(0)}_{\rm ht}|\kappa F(n)|^{24}}$ with
$A^{(0)}_{\rm ht}=A_0$. The five natural inputs of the precision polynomial are
$(\operatorname{enc}n,\operatorname{enc}\kappa,\operatorname{enc}a,\operatorname{enc}l,\operatorname{enc}j)$, in this order.

This is a definition. All quantities are exact rationals and integers; the comparisons are
strict.

## Depends on

- [Point codes](../../model/point-codes.md)
- [The six-contact height estimate](../../main/six-contact-estimate.md)

## Sources

- [Section 10 precision predicate](../../../sources/assembly-locators.md#section-10-precision-predicate)
- [Section 4 height constants](../../../sources/assembly-locators.md#section-4-height-constants)
- [Section 11.1 approximation](../../../sources/assembly-locators.md#section-111-approximation)
