---
article_id: af_64a731d3120f967fc7bc668b
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Assembly.poleInput_real
---

# Real conditions on the pole input

Let $R_0>1$ be an integer and $C_1,\dots,C_6\in K_0$. There is $q\in\mathbb Q$ whose reduced denominator
is coprime to $R_0$ such that, with
$$a_0=1-R_0q^2,\qquad R=R_0a_0^2,\qquad W=\prod_{j=1}^6\bigl(1+RC_j^2\bigr),\qquad\Theta=\operatorname{Tr}(W^{-1}),$$
one has $a_0\ne0$, $W\ne0$, $\Theta\ne0$ and
$$0<R/\Theta^2<1/2 .$$

**Proof sketch.** *Positivity.* For any $q$ with $a_0\ne0$, $R>0$. In each real embedding
$\tau=\sigma_\pm$, $\tau(RC_j^2)=R\,\tau(C_j)^2\ge0$, so $\tau(W)\ge1$; hence $W\ne0$,
$0<\tau(W^{-1})\le1$ and $\Theta=\sigma_+(W^{-1})+\sigma_-(W^{-1})\in(0,2]$. So $R/\Theta^2>0$.

*Smallness.* Let $c=\max_{j,\pm}\sigma_\pm(C_j)^2$. If $R\le r:=\min\bigl(1/4,\ 1/(10(c+1))\bigr)$ then
$\tau(W)\le(1+Rc)^6\le e^{6/10}<2$, so $\tau(W^{-1})>1/2$, $\Theta>1$ and $R/\Theta^2<R\le1/4$.

*Choice of $q$.* For $j\in\mathbb N$ put $m_j=R_0j+1$, coprime to $R_0$, and let $k_j$ be the integer
nearest to $m_j/\sqrt{R_0}$, so $q_j=k_j/m_j$ has $|q_j-R_0^{-1/2}|\le1/(2m_j)$ and reduced
denominator dividing $m_j$. Then
$|a_0|=R_0\,|R_0^{-1/2}-q_j|\,|R_0^{-1/2}+q_j|\to0$, so $R=R_0a_0^2<r$ for $j$ large. Finally
$a_0\ne0$: $R_0q_j^2=1$ would give $R_0k_j^2=m_j^2$, so $R_0\mid m_j^2$, impossible as
$\gcd(R_0,m_j)=1$ and $R_0>1$. (The manuscript's "adjusting by one if equality occurs" is
therefore never needed.)

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](../../model/field/quadratic-field.md)

## Sources

- [Lemma 11.2](../../../sources/assembly-locators.md#lemma-112)
