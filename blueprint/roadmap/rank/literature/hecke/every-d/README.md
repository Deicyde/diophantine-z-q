---
article_id: af_af664e675dd6b9d4e1facb01
---

# The L-series of $C_d$ for every $d\ne0$

[Hecke's continuation](../../hecke-continuation.md) is stated for every $d\ne0$, while
[the computation of $L(C_d,s)$](../../l-function-cd/README.md) covers odd squarefree $d$. This
subsection removes both restrictions.

For even squarefree $d=2e$, the discriminant $(2d)^6$ of $y^2=x^3-d^2x$ has $2$-adic valuation
$12$, so the discriminant criterion does not decide minimality at $2$. Instead $c_4=48d^2=192e^2$
has $2$-adic valuation $6$, while every integral equation over $\mathbb Z_2$ has $c_4$ a unit or
divisible by $16$; so no change of variables with $v(u)>0$ keeps the equation integral, and the
equation is minimal. With that, the computation of $L(C_d,s)$ holds for every squarefree $d$.

For non-squarefree $d=m^2d'$, the scaling $(x,y)\mapsto(x/m^2,y/m^3)$ carries $C_{m^2d'}$ to
$C_{d'}$. The local polynomial at each place does not depend on the equation chosen in the
isomorphism class when $j$ is integral, which excludes multiplicative reduction; for $C_d$,
$c_4^3=1728\Delta$. So $L(C_{m^2d'},s)=L(C_{d'},s)$.

For squarefree $d$, the substitution $x\mapsto dx$ makes the coefficients of $C_d$ those of $C_1$
twisted by the Jacobi symbol $\left(\frac dn\right)$. With Deuring's identity for $C_1$, this
writes $L(C_d,s)$ as a periodic twist of the lattice series of $\mathbb Z[i]$ modulo $4d$, which has
an entire continuation.

Throughout, notation is that of [the computation of $L(C_d,s)$](../../l-function-cd/README.md).

- [Minimality of $C_d$ at $2$ for even squarefree $d$](minimal-at-two.md)
- [The local factors of $C_d$ for every squarefree $d$](cd-local-every-squarefree.md)
- [$L(C_d,s)$ for every squarefree $d$](cd-coefficients-every-squarefree.md)
- [The local polynomial is invariant under changes of variables when $j$ is integral](l-function-invariance.md)
- [$L(C_{m^2d},s)=L(C_d,s)$](cd-square-factor.md)
- [The coefficients of $C_d$ as a quadratic twist of $C_1$](quadratic-twist-coefficients.md)
- [The continuation of $L(C_d,s)$ for every squarefree $d$, from Gauss's point count](continuation-squarefree.md)
