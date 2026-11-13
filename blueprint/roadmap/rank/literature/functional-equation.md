---
article_id: af_f2d81192cc842ffdc7021864
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Literature.completedL, ZInQ.Literature.FunctionalEquation5
---

# The functional equation of $L(C_d,s)$ on the strip $0<\operatorname{Re}s<2$

For a natural number $N$, a function $F:\mathbb C\to\mathbb C$ and a complex number $s$, the
*completed function* is
$$\Lambda_N(s)=N^{s/2}\,(2\pi)^{-s}\,\Gamma(s)\,F(s),$$
where $\Gamma$ is the gamma function, given the value $0$ at its poles $0,-1,-2,\dots$;
$(2\pi)^{-s}=e^{-s\log2\pi}$; $N^{s/2}=e^{(s/2)\log N}$ if $N>0$; and $0^{s/2}$ is $0$ for
$s\ne0$ and $1$ for $s=0$. Below, only $N=32d^2$ with $d>0$ is used, and only at points $s$ and
$2-s$ with $0<\operatorname{Re}s<2$.

The *functional equation on the critical strip* is the following assertion. For every natural
number $d$ with $d\equiv5\pmod8$ and $d$ squarefree, every entire continuation $F$ of $L(C_d,s)$,
and every complex number $s$ with $0<\operatorname{Re}s<2$,
$$\Lambda_{32d^2}(2-s)=-\Lambda_{32d^2}(s).$$

For every $s$ in the strip, neither $s$ nor $2-s$ is a pole of $\Gamma$, so there $\Gamma(s)$
and $\Gamma(2-s)$ are the true values. The textbook functional equation of $L(C_d,s)$, which is
the L-function of a Hecke character of $\mathbb Q(i)$ since $C_d$ has complex multiplication by
$\mathbb Z[i]$ (Hecke, Deuring), has conductor $32d^2$ for odd squarefree $d$ and root number $-1$
for $d\equiv5,6,7\pmod8$ (Birch–Stephens); restricted to the strip it gives this statement. Only
$s=1$ is used. The identity is not asserted off the strip; with the value $0$ at the poles of
$\Gamma$ it would fail at $s=0$, where it would say $L(C_d,2)=0$. It is a hypothesis, not proved
here.

## Depends on

- [Entire continuations of the L-series of an elliptic curve](l-series-continuation.md)

## Sources

- [The functional equation and the root number](../../../sources/rank-locators.md#the-functional-equation-and-the-root-number)
- [Hecke and Deuring](../../../sources/rank-locators.md#hecke-and-deuring)
