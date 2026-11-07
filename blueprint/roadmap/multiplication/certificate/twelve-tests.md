---
article_id: af_37201bee3678c1995776dedf
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Mult.invX, ZInQ.Mult.zOf, ZInQ.Mult.Lam, ZInQ.Mult.testValues, ZInQ.Mult.testValues_eq
---

# The twelve local tests

Let $h,z_1,z_2,z_3,c_0,c_1,c_2,c_3\in\mathbb Z$ with $h\ne0$ and $h\ne c_0$. Put
$$H=[h]P_0,\quad U_i=[z_i]P_0,\quad V_0=[h-c_0]P_0,\quad V_i=[z_i-c_i]P_0\qquad(i=1,2,3),$$
so that $V_0=H-[c_0]P_0$ and $V_i=U_i-[c_i]P_0$. For $Q\in\mathbb ZP_0$ let $\rho(Q)=1/x(Q)$ with
$\rho(O)=0$, and $\Lambda(Q)=L(z(Q))$ with $\Lambda(O)=L(0)=0$, where $L$ is the truncated
logarithm. Put
$$A_i=\frac{\Lambda(U_i)}{\Lambda(H)},\qquad B_i=\frac{\Lambda(V_i)}{\Lambda(V_0)}\qquad(i=1,2,3).$$
With $\sigma$ the conjugation of $K_0$, the twelve test values
$\tau(h,z;c)=(\tau_1,\dots,\tau_{12})\in K_0^{12}$ are
$$\begin{aligned}
&\tau_1=\rho(H),\quad \tau_{1+i}=\rho(U_i),\quad \tau_5=\sigma\rho(V_0),\quad \tau_{5+i}=\sigma\rho(V_i),\\
&\tau_{8+i}=A_i-\sigma B_i\quad(i=1,2,3),\qquad \tau_{12}=A_1A_2-A_3 .
\end{aligned}$$
That is: four inverse abscissas at $H,U_i$, their four conjugate counterparts at $V_0,V_i$,
three differences of the corresponding $L$-ratios, and the product of the first two
unprimed ratios minus the third. Identity inverse abscissas are zero.

In the multiplication certificate $c_0=c_*$ and $c_i=c_*n_i$, where $n_1,n_2,n_3$ are the
indices of the three inputs; then $V_0=H-[c_*]P_0$ and $V_i=U_i-[c_*n_i]P_0$.

This is a definition. The quantities $\rho(Q)$ and $\Lambda(Q)$ are well defined because a
nonidentity multiple of $P_0$ has $x,y\ne0$, and the denominators $\Lambda(H),\Lambda(V_0)$
are nonzero because $H,V_0\ne O$ (the nonvanishing lemma); as a formal definition any
convention for a zero denominator may be used.

## Depends on

- [The point $P_0$](../../model/field/generator-point.md)
- [The truncated logarithm template](../../syntax/templates/template-log25.md)

## Sources

- [Twelve tests](../../../sources/multiplication-locators.md#twelve-tests)
- [Multiplication certificate generator](../../../sources/multiplication-locators.md#multiplication-certificate-generator)
