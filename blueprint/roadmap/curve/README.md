---
article_id: af_499338b42ca5fb1547638960
---

# The generator curve and its point codes

This chapter fixes the field, the curve, the base point and the coding of points by rationals. The
specification of the polynomial and the elliptic model of integer indices both build on these
definitions, so they form a chapter of their own, before either.

Everything takes place over $K_0=\mathbb Q(s)$, $s^2=2$, written in the basis $1,s$, so that
each field equation is two rational equations.

- [The field $K_0=\mathbb Q(\sqrt2)$](quadratic-field.md)

The handful of explicit identities and sign facts used throughout (the square of $d$, powers of
$\epsilon=1+s$, $\delta=\epsilon^4d$, norms, total positivity of $d$ and $\delta$) are collected in one
closed statement.

- [Explicit identities in $K_0$](explicit-identities.md)

The curve is $E:y^2=x^3-d^2x$ with $d=75-53s$, and the base point is
$P_0=\bigl(\frac{1641-1160s}{8},\frac{-123720+87483s}{32}\bigr)$; that its coordinates satisfy the
curve equation is a closed identity in $K_0$.

- [The generator curve $E$](generator-curve.md)
- [The coordinates of $P_0$ satisfy the curve equation](generator-point-equation.md)
- [The point $P_0$](generator-point.md)

A point is coded by five rationals: $(1,0,0,0,0)$ for the identity and $(0,x_0,x_1,y_0,y_1)$ for an
affine point with $x=x_0+x_1s$, $y=y_0+y_1s$; $\iota(n)$ is the code of $[n]P_0$. The integer index
and the coordinates play distinct roles throughout.

- [Point codes](point-codes.md)
