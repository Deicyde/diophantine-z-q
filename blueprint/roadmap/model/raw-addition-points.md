---
article_id: af_51908b404b3c3c366bfec93a
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.rel_rawAdd_iff
---

# Raw addition on canonical codes

For all $P,Q\in E(K_0)$ and every $r\in\mathbb Q^5$,
$$\mathrm{Rel}_{\mathtt{raw\_add}}\bigl(\operatorname{code}(P),\operatorname{code}(Q),r\bigr)\iff
r=\operatorname{code}(P+Q),$$
where $\mathrm{Rel}_{\mathtt{raw\_add}}(p,q,r)$ means that the polynomial of the raw addition
template vanishes at $(p,q,r)$ and some rational values of its six witnesses (two slope
pairs $m_g,m_d$ and two inverse witnesses $u_g,u_d$). No assumption beyond $P,Q\in E(K_0)$
is needed; two-torsion inputs are included.

Write $x,y$ for the abscissa and ordinate encoded by $p$, $x',y'$ for those of $q$, and
$x_r,y_r$ for those of $r$. The five branches of the template are: (1) $p=O$ and $q=r$;
(2) $p_0=0$, $q=O$ and $p=r$; (3) $p_0=q_0=0$, $x=x'$, $y=-y'$ and $r=O$; (4) $p_0=q_0=0$,
$u_g\operatorname N(x'-x)=1$, $(x'-x)m_g=y'-y$, $r_0=0$, $x_r=m_g^2-x-x'$, $y_r=m_g(x-x_r)-y$;
(5) $p_0=q_0=0$, $x=x'$, $y=y'$, $u_d\operatorname N(y)=1$, $2ym_d=3x^2-d^2$, $r_0=0$,
$x_r=m_d^2-x-x'$, $y_r=m_d(x-x_r)-y$. Here $O=(1,0,0,0,0)$.

**Proof sketch.** The template polynomial is the square of the compilation of its formula,
so it vanishes exactly when one branch holds, the witnesses of the other branches being
arbitrary. Cases. *$P=O$*: branches 2-5 need $p_0=0$, and branch 1 holds exactly when
$r=\operatorname{code}(Q)=\operatorname{code}(P+Q)$. *$P$ affine, $Q=O$*: branch 1 needs $p_0=1$,
branches 3-5 need $q_0=0$, and branch 2 holds exactly when $r=\operatorname{code}(P)$. *Both
affine*: if $x\ne x'$, branches 3 and 5 fail, branch 4 is satisfiable ($\operatorname N(x'-x)\ne0$),
it forces $m_g$ to be the chord slope, and then $r$ is the code of the chord sum. If $x=x'$
then $y'=\pm y$ by the curve equation, and branch 4 fails. If $y=-y'$, branch 3 holds with
$r=\operatorname{code}(O)=\operatorname{code}(P+Q)$, and branch 5 would need $y=y'$ and
$\operatorname N(y)\ne0$, i.e. $y=0$ and $y\ne0$. If $y=y'\ne0$, branch 3 fails and branch 5 forces
the tangent slope and $r=\operatorname{code}([2]P)$. In each case the forced $r$ is the code given
by the group law of $E$, and conversely that $r$ with the forced witnesses satisfies the
branch.

## Depends on

- [The raw addition template](../syntax/template-raw-add.md)
- [Point codes](point-codes.md)

## Proof depends on

- [Sums of squares and products over the rationals](../syntax/sum-of-squares-semantics.md)
- [Pair arithmetic represents the quadratic field](../syntax/field-pair-arithmetic.md)
- [Elementary properties of codes](field/point-code-properties.md)

## Sources

- [Membership and addition](../../sources/model-locators.md#membership-and-addition)
- [Translation typing](../../sources/model-locators.md#translation-typing)
