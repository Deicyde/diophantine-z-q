---
article_id: af_c05412d70698f82bddf68e5e
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Literature.rootNumberVanishing_of_functionalEquation
---

# The functional equation gives vanishing at the centre

The functional equation of $L(C_d,s)$ on the critical strip implies vanishing at the centre: if
for every squarefree natural number $d\equiv5\pmod8$, every entire continuation $F$ of
$L(C_d,s)$ and every $s$ with $0<\operatorname{Re}s<2$ one has
$\Lambda_{32d^2}(2-s)=-\Lambda_{32d^2}(s)$, then $F(1)=0$ for every such $d$ and $F$.

**Proof sketch.** Let $d$ and $F$ be given and take $s=1$, which lies in the strip. Since
$2-1=1$, the functional equation reads $\Lambda_{32d^2}(1)=-\Lambda_{32d^2}(1)$, so
$\Lambda_{32d^2}(1)=0$. Since $\Gamma(1)=1$, this says
$(32d^2)^{1/2}(2\pi)^{-1}F(1)=0$. As $d\equiv5\pmod8$, $d\ne0$, so $32d^2\ne0$; also
$2\pi\ne0$. A nonzero base raised to a nonzero exponent is nonzero, so both powers are nonzero and
$F(1)=0$.

## Depends on

- [The functional equation of $L(C_d,s)$ on the strip $0<\operatorname{Re}s<2$](functional-equation.md)
- [Vanishing at the centre for $d\equiv5\pmod8$](root-number-vanishing.md)

## Sources

- [The functional equation and the root number](../../../sources/rank-locators.md#the-functional-equation-and-the-root-number)
