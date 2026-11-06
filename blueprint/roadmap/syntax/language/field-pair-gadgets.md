---
article_id: af_aa1527fc60fde10afbc8ab0f
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.Pair, ZInQ.Syntax.Build.fdiv, ZInQ.Syntax.Build.zGadget
---

# Quadratic-field pairs and point-code formulas

These are the formula-level abbreviations shared by the templates. Throughout,
$K_0=\mathbb Q(s)$ with $s^2=2$.

**Pairs.** A pair is $u=(u_0,u_1)$ of polynomials, standing for $u_0+u_1s$. Define
$u+u'=(u_0+u_0',u_1+u_1')$, $-u=(-u_0,-u_1)$, $u-u'=u+(-u')$, $k\,u=(ku_0,ku_1)$ for an
integer or polynomial $k$,
$$u\cdot u'=(u_0u_0'+2u_1u_1',\ u_0u_1'+u_1u_0'),$$
$u^2=u\cdot u$, $u^{n}$ by repeated squaring, the conjugate $\bar u=(u_0,-u_1)$ and the norm
$N(u)=u_0^2-2u_1^2$. Integer pairs are written $(a,b)$; $1=(1,0)$. The curve coefficient is
$A=(-11243,7950)$, that is $A=-d^2$ for $d=75-53s$, and $\delta=(11243,-7950)=d^2$.

**Pair formulas.** $u\doteq u'$ is $\bigwedge(u_0\doteq u_0',u_1\doteq u_1')$.
$\mathrm{NZ}_K(u)$ is $\mathrm{NZ}(N(u))$ (one fresh variable).
$\mathrm{Div}(n,d)$ takes a fresh pair $q$, then forms
$\bigwedge(\mathrm{NZ}_K(d),\ d\cdot q\doteq n)$; its value is $q$.

**Point codes.** A point code is $p=(p_0,\dots,p_4)$, with $x(p)=(p_1,p_2)$ and
$y(p)=(p_3,p_4)$; a fresh point takes five fresh variables. Define
$O=(1,0,0,0,0)$, $\mathrm{neg}(p)=(p_0,p_1,p_2,-p_3,-p_4)$,
$\mathrm{eq}(p,p')=\bigwedge_{i=0}^4(p_i\doteq p_i')$, $\mathrm{isO}(p)=\mathrm{eq}(p,O)$,
$\mathrm{fin}(p)$ the atom $p_0\doteq0$, and the curve atom pair
$\mathrm{curve}(X,Y)$: $Y^2\doteq X^2\cdot X+A\cdot X$. The generator point of a template is
$G=(0,c_1,-145,c_2,c_3)$ with $c_1,c_2,c_3$ the rational constants $1641/8$, $-15465/4$,
$87483/32$, requested in this order.

**Local parameter and inverse abscissa.** For a point $p$ and a pair $\zeta$,
$$Z(p,\zeta)=\bigvee\Bigl(\bigwedge(\mathrm{isO}(p),\ \zeta\doteq(0,0)),\ \
\bigwedge(\mathrm{fin}(p),\ \mathrm{NZ}_K(y(p)),\ y(p)\cdot\zeta\doteq-x(p))\Bigr)$$
(one fresh variable) expresses $\zeta=z(p)=-x/y$, with $z(O)=0$. For a pair $v$,
$$I\!X(p,v)=\bigvee\Bigl(\bigwedge(\mathrm{isO}(p),\ v\doteq(0,0)),\ \
\bigwedge(\mathrm{fin}(p),\ x(p)\cdot v\doteq(1,0))\Bigr)$$
expresses $v=1/x$, with value $0$ at the identity.

This is a definition. In each template these abbreviations allocate their fresh variables
at the moment they are formed, in the order written.

## Depends on

- [Formulas and their polynomial compilation](formula-compilation.md)

## Sources

- [Appendix C.1](../../../sources/syntax-locators.md#appendix-c1-scalar-nodes)
- [Section 3](../../../sources/syntax-locators.md#section-3-point-codes)
- [Saved specification](../../../sources/syntax-locators.md#saved-specification)
