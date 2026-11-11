---
article_id: af_89fdee3a33b76cb93a1cd93b
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.mwKummer_range_finite, ZInQ.RouteK.Rank.mwEven_padicValRat_x, ZInQ.RouteK.Rank.mwSqc_eq_divisor
---

# The Kummer image over $\mathbb Q$ is finite

Let $c$ be a nonzero integer. Then the Kummer image
$\alpha_c(E_c(\mathbb Q))\subseteq\mathbb Q^\times/\mathbb Q^{\times2}$ of $E_c:y^2=x^3+cx$ is
finite.

Along the way:

- if $x,y\in\mathbb Q$ satisfy $y^2=x^3+cx$ and $x\ne0$, then $v_p(x)$ is even for every prime
  $p\nmid c$;
- if $B$ is a positive integer and $q\in\mathbb Q^\times$ has $v_p(q)$ even for every prime
  $p\nmid B$, then $q\equiv m$ modulo squares for some integer $m$ with $|m|$ dividing $B$.

**Proof sketch.** (Silverman–Tate, Section III.5.)

*Valuations.* Let $p\nmid c$, so $v_p(cx)=v_p(x)$. If $y=0$ then $x^2=-c$, so
$2v_p(x)=v_p(c)=0$. Otherwise $2v_p(y)=v_p(x^3+cx)$. If $v_p(x)<0$, the term $x^3$ dominates:
$2v_p(y)=3v_p(x)$, so $v_p(x)$ is even. If $v_p(x)>0$, the term $cx$ dominates:
$2v_p(y)=v_p(x)$.

*Signed divisors.* Write $q=r/s$ in lowest terms with $s>0$, let $N=rs=qs^2$, and write
$|N|=t^2a$ with $a$ squarefree. Put $m=\operatorname{sign}(N)\,a$, so $q\equiv N\equiv m$
modulo squares. Every prime $p\mid a$ divides $B$: otherwise $v_p(N)=v_p(q)+2v_p(s)$ is even, so
$v_p(a)=v_p(N)-2v_p(t)\ge1$ is even, hence $p^2\mid a$, against squarefreeness. As $a$ is
squarefree, $|m|=a$ divides $B$.

*Finiteness.* The image lies in the classes of the integers $m$ with $|m|$ dividing $|c|$, a
finite set. Indeed
$\alpha_c(O)=1$ (take $m=1$) and $\alpha_c((0,y))=c$ (take $m=c$). For $x\ne0$,
$\alpha_c((x,y))$ is the class of $x$, which by the two lemmas, with $B=|c|$, is the class of
such an $m$.

## Depends on

- [Two-isogenies and the Kummer map](../../model/descent/kummer-map.md)

## Sources

- [Silverman-Tate](../../../sources/rank-locators.md#silverman-tate)
