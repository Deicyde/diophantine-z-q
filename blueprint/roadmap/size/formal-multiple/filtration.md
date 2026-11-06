---
article_id: af_573c53f86fa85fe33fa0205f
declaration: theorem
origin: background
---

# The filtration by abscissa valuation

Let $K$ be a field with a discrete valuation $v:K^\times\to\mathbb Z$ (surjective,
$v(0)=+\infty$), valuation ring $\mathcal O$ and residue field of characteristic $p>0$. Let
$a\in\mathcal O$ and $W:y^2=x^3+ax$ over $K$.

1. If $(x,y)\in W(K)$ and $v(x)<0$, there is an integer $m\ge1$ with $v(x)=-2m$ and
   $v(y)=-3m$; then $t=x/y$ has $v(t)=m$.
2. For $r\ge1$ the set $W_r=\{O\}\cup\{(x,y)\in W(K):v(x)\le-2r\}$ is a subgroup of $W(K)$.
3. Put $t(O)=0$ and $t(x,y)=x/y$. For $Q_1,Q_2\in W_r$ ($r\ge1$),
   $$v\bigl(t(Q_1+Q_2)-t(Q_1)-t(Q_2)\bigr)\ge5r .$$
4. If $v(p)\le4$, then $[n]W_r\subseteq W_{r+v(n)}$ for every integer $n\ne0$ and every
   $r\ge1$.

On $K_0$ this applies at every prime $\mathfrak p$ of $\mathbb Z[s]$: at an odd prime
$v_{\mathfrak p}(p)=1$, and at $(s)$, $v_s(2)=2$.

**Proof sketch.** (1) $v(x^3)<v(ax)$, so $2v(y)=3v(x)$. (2) and (3) are proved in the
coordinates $t=x/y$, $w=1/y$, in which the curve is $w=t^3+atw^2$, the identity is
$(0,0)$, negation is $(t,w)\mapsto(-t,-w)$, and points of $W_r$ have $v(t)\ge r$,
$v(w)\ge3r$. For two such points with $t_1\ne t_2$ the line $w=\alpha t+\beta$ through them has
$$\alpha=\frac{t_1^2+t_1t_2+t_2^2+aw_2^2}{1-at_1(w_1+w_2)},$$
with a unit denominator, so $v(\alpha)\ge2r$ and $v(\beta)=v(w_1-\alpha t_1)\ge3r$. If $t_1=t_2$
the points coincide: subtracting the two curve equations gives $(w_1-w_2)(1-at_1(w_1+w_2))=0$
with a unit second factor; then use the tangent slope $(3t^2+aw^2)/(1-2atw)$. (The formula for
$\alpha$ comes from $w_2-w_1=(t_2^3-t_1^3)+a\bigl((t_2-t_1)w_2^2+t_1(w_2-w_1)(w_2+w_1)\bigr)$.) Substituting the line into the curve gives
$(1+a\alpha^2)t^3+2a\alpha\beta t^2+\dots=0$, so the third intersection $t_3$ satisfies
$t_1+t_2+t_3=-2a\alpha\beta/(1+a\alpha^2)$, of valuation at least $5r$ (the denominator is a
unit). Put $w_3=\alpha t_3+\beta$, so $v(t_3)\ge r$ and $v(w_3)\ge3r$. If $w_3=0$, then $t_3^3=0$
and the third point is $O$; otherwise $(t_3/w_3,1/w_3)$ is the third intersection point of $W$
with the corresponding line in $(x,y)$ coordinates, and $w_3=t_3^3+at_3w_3^2$ with
$v(at_3w_3^2)>v(w_3)$ gives $v(w_3)=3v(t_3)$, hence $v(x_3)=-2v(t_3)\le-2r$. The sum
$Q_1+Q_2$ is the negative of the third point, so $t(Q_1+Q_2)=-t_3$, which gives (3) and
$Q_1+Q_2\in W_r$; closure under negation is $(t,w)\mapsto(-t,-w)$. (4) By induction from (3), $v(t([n]Q)-n\,t(Q))\ge5r$ for
$Q\in W_r$. For $n=p$ this gives $v(t([p]Q))\ge\min(5r,r+v(p))=r+v(p)$, so
$[p]W_r\subseteq W_{r+v(p)}$; iterate, and note that $[n']W_r\subseteq W_r$ with $v(n')=0$ for
$p\nmid n'$.

This is the elementary form of the formal-group statements the manuscript uses (Silverman,
Chapters IV and VII: $W_r$ corresponds to the formal group on $\mathfrak m^r$, and for
$v(z)>v(p)/(p-1)$ the formal logarithm is an isometry). The manuscript argues at $(s)$ with
the logarithm isometry, $v_s(z([2]Q))=v_s(z(Q))+2$ for $v_s(z(Q))\ge3$; part (4) gives the
inequality $\ge$, which is all that is used.

## Depends on

None.

## Sources

- [Proof of Proposition 12.1, formal multiple](../../../sources/size-locators.md#proof-of-proposition-121-formal-multiple)
- [Silverman](../../../sources/size-locators.md#silverman)
