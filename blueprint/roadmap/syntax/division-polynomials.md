---
article_id: af_f401bef0ba7e28873cf85a34
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.normDiv, ZInQ.Syntax.divPsi, ZInQ.Syntax.psiComponent
---

# Normalized division polynomials and their components

Let $R$ be a commutative ring and $A\in R$. The normalized division polynomials
$f_n\in R[x]$, $n\ge0$, of $y^2=x^3+Ax$ are defined by
$$f_0=0,\quad f_1=f_2=1,\quad f_3=3x^4+6Ax^2-A^2,\quad f_4=2(x^6+5Ax^4-5A^2x^2-A^3),$$
and, for larger indices,
$$f_{2m}=f_m\bigl(f_{m+2}f_{m-1}^2-f_{m-2}f_{m+1}^2\bigr)\qquad(m\ge3),$$
$$f_{2m+1}=\begin{cases}D_0L-R_m,& m\text{ even},\\ L-D_0R_m,& m\text{ odd},\end{cases}\qquad(m\ge2),$$
where $L=f_{m+2}f_m^3$, $R_m=f_{m-1}f_{m+1}^3$ and $D_0=16(x^3+Ax)^2$. The recursion
terminates because every index on the right is smaller than the index on the left for
$n\ge5$. The division polynomials $\psi_n\in R[x,y]$, $n\in\mathbb Z$, are
$$\psi_n=f_n\ (n\ge0\text{ odd}),\qquad\psi_n=2y\,f_n\ (n\ge0\text{ even}),\qquad\psi_{-n}=-\psi_n .$$

**Components.** Take $R=\mathbb Z[x_0,x_1,y_0,y_1][s]/(s^2-2)$, whose elements are pairs
over $\mathbb Z[x_0,x_1,y_0,y_1]$ with the pair product $(a,b)(c,d)=(ac+2bd,ad+bc)$, and
$A=-11243+7950s$. For $n\in\mathbb Z$ and $c\in\{0,1\}$, the component polynomial
$\Psi_{n,c}\in\mathbb Z[x_0,x_1,y_0,y_1]$ is the coefficient of $s^c$ in
$\psi_n(x_0+x_1s,\ y_0+y_1s)$. The constructor $\mathrm{psi}\ e\ (a_0,\dots,a_3)\ c$ denotes
$\Psi_{\mathrm{val}(e),c}$ evaluated at the polynomials of its four argument nodes.

The index of every occurring component is a fixed integer expression ($n$, $n+1$, $n-1$ or
$2n$ for a fixed index $n$ of a scalar template); the polynomials $\Psi_{n,c}$ for the
astronomical index $c_*$ are never expanded, and every statement about them is proved from
the recurrences.

This is a definition.

## Depends on

None.

## Sources

- [Section 2.2](../../sources/syntax-locators.md#section-22-division-polynomials)
- [Appendix C.1](../../sources/syntax-locators.md#appendix-c1-scalar-nodes)
