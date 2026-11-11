---
article_id: af_07b61cae8c50eaaa6ef18746
declaration: def
origin: cited
statement: formalized
lean: ZInQ.PoleCompleteness, ZInQ.polePoly, ZInQ.PoleSoluble, ZInQ.poleS0
---

# Pole completeness

For $B\in\mathbb Q$ and witnesses $b_0,\ldots,b_5,e,z,r_1,r_2,w\in\mathbb Q$ put
$m=(1-2b_0)(1+b_1)(1+2b_2)(1+4b_3)(1+6b_4)(1+12b_5)$, $A=mB$, $H=A(A-B^2)$,
$T_1=A(A-e)(A+e)$, $T_2=A(Az^2-eH)(Az^2+eH)$ and
$$Q_{\rm pole}=B\Bigl(\sum_{i=0}^5(b_i^2-b_i)^2+(eHzw-1)^2+(r_1^2-T_1)^2+(r_2^2-T_2)^2\Bigr).$$
Write $\Phi(B)$ when $Q_{\rm pole}$ has a rational zero with input $B$. For $B\ne0$ a zero puts
$(A,r_1)$ on the congruent number curve $y^2=x(x-e)(x+e)$ and $(Az^2,zr_2)$ on $y^2=x(x-eH)(x+eH)$.

Pole completeness is the assertion that every rational $B$ with square reduced
denominator, $0<B<1/2$ and $v_p(B)\ge4$ for every $p\in S_0=\{2,3,5,7,13\}$ satisfies $\Phi(B)$.

This is the pole polynomial of Route K, with the curves $y^2=x(x-\ell)(x+\ell)$; the
manuscript's $Q_{\rm pole}$ has the factors $A+3e$ and $Az^2+3eH$ (the curves
$y^2=x(x-\ell)(x+3\ell)$) and derives pole completeness from its restricted converse theorem by a
simultaneous descent. Here pole completeness is no longer a hypothesis of the main theorem: it
is proved from the certified rank hypothesis CR₃
([pole completeness from the certified rank hypothesis](../route-k/pole-completeness-from-cr3.md)),
and also from positive rank on the two congruent number curves of a slot choice, CR₃^DL,Rk
([pole completeness from CR₃^DL,Rk](../rank/two-curves/pole-completeness-from-dl-rk.md)).

## Depends on

None.

## Sources

- [Theorem 5.2](../../sources/manuscript.md#theorem-52)
- [Pole predicate](../../sources/multiplication-locators.md#pole-predicate)
