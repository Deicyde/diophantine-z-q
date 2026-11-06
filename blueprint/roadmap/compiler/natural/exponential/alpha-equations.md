---
article_id: af_6860395c898618c5b0a8665f
declaration: def
origin: cited
statement: formalized
lean: ZInQ.AlphaPower.AlphaEqns
---

# The alpha formula

For natural numbers $X,b,N$, the *alpha formula* $\mathrm{Alpha}(X,b,N)$ is the statement that
there are natural numbers $r,s,t,u,v,w,x,y$ satisfying the fifteen conditions (C.2):
$$\begin{gathered}
b>3,\quad u^2+t^2=1+but,\quad s^2+r^2=1+bsr,\quad r<s,\quad u^2\mid s,\quad v+2r=bs,\\
w\equiv b\pmod v,\quad w\equiv2\pmod u,\quad w>2,\quad x^2+y^2=1+wxy,\\
2X<u,\quad 2X<v,\quad x\equiv X\pmod v,\quad 2N<u,\quad x\equiv N\pmod u .
\end{gathered}$$
Here $p\equiv q\pmod M$ means $p\bmod M=q\bmod M$ for natural numbers (so for $M=0$ it
means $p=q$), and $p\mid q$ is divisibility in $\mathbb N$.

The compiler emits this system as the alpha macro: each strict inequality, divisibility
and congruence is replaced by an equation with fresh natural witnesses (see the
equational gadgets), and the macro introduces its eight witnesses in the order
$r,s,t,u,v,w,x,y$. The conditions are exactly those of `Exp_Matrices.alpha_equations` in
the AFP development, with $a=X$ and $c=N$; equation order and the orientation of each
equality are immaterial.

This is a definition.

## Depends on

None.

## Sources

- [Section 10.2 alpha formula](../../../../sources/compiler-natural-locators.md#section-102-alpha-formula)
- [Compiler source](../../../../sources/compiler-natural-locators.md#compiler-source)
- [AFP DPRM development](../../../../sources/compiler-natural-locators.md#afp-dprm-development)
