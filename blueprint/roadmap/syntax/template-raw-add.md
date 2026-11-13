---
article_id: af_67ee9f551814beef54b38198
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.rawAddTemplate, ZInQ.Syntax.rawAddTemplate_rel_iff
---

# The raw addition template

The template $\mathtt{raw\_add}$ has $15$ parameters and $6$ witnesses ($21$ variables).
Its variables are the points $p=(X_0,\dots,X_4)$, $q=(X_5,\dots,X_9)$, $r=(X_{10},\dots,X_{14})$,
the slope pairs $m_g=(X_{15},X_{16})$ and $m_d=(X_{17},X_{18})$, and the inverse witnesses
$u_g=X_{19}$, $u_d=X_{20}$. Write $x=x(p)$, $y=y(p)$, $x'=x(q)$, $y'=y(q)$,
$\mathrm{both}=\bigwedge(\mathrm{fin}(p),\mathrm{fin}(q))$ and, for a slope pair $m$,
$$\mathrm{out}(m)=\bigwedge\bigl(\mathrm{fin}(r),\ x(r)\doteq m^2-x-x',\ y(r)\doteq m\cdot(x-x_r)-y\bigr),\qquad x_r=m^2-x-x'.$$
The formula is the disjunction of five branches, in this order:
$$\varphi_{\rm add}=\bigvee(\beta_1,\beta_2,\beta_3,\beta_4,\beta_5),$$
$$\beta_1=\bigwedge(\mathrm{isO}(p),\ \mathrm{eq}(q,r)),\qquad
\beta_2=\bigwedge(\mathrm{fin}(p),\ \mathrm{isO}(q),\ \mathrm{eq}(p,r)),$$
$$\beta_3=\bigwedge(\mathrm{both},\ x\doteq x',\ y\doteq-y',\ \mathrm{isO}(r)),$$
$$\beta_4=\bigwedge\bigl(\mathrm{both},\ N(x'-x)\,u_g\doteq1,\ (x'-x)\cdot m_g\doteq y'-y,\ \mathrm{out}(m_g)\bigr),$$
$$\beta_5=\bigwedge\bigl(\mathrm{both},\ x\doteq x',\ y\doteq y',\ N(y)\,u_d\doteq1,\ (2y)\cdot m_d\doteq3x^2+A,\ \mathrm{out}(m_d)\bigr).$$
Its polynomial is $[\![\mathtt{raw\_add}]\!]=\kappa(\varphi_{\rm add})^2$.

The branches cover both identities, opposite points, distinct abscissas and doubling with
nonzero ordinate. The contract $\mathrm{Add}_{\rm raw}(\iota(a),\iota(b),r)\iff r=\iota(a+b)$ is
proved in the model chapter.

This is a definition (template index $1$).

## Depends on

- [Formulas and their polynomial compilation](language/formula-compilation.md)
- [Quadratic-field pairs and point-code formulas](language/field-pair-gadgets.md)

## Sources

- [Section 3.1](../../sources/syntax-locators.md#section-31-membership-and-natural-codes)
- [Appendix C.2](../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
- [Saved specification](../../sources/syntax-locators.md#saved-specification)
