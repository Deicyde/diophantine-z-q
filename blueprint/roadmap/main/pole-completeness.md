---
article_id: af_07b61cae8c50eaaa6ef18746
declaration: def
origin: cited
statement: formalized
lean: ZInQ.PoleCompleteness
---

# Pole completeness

For $B\in\mathbb Q$ and witnesses $b_0,\ldots,b_5,e,z,r_1,r_2,w\in\mathbb Q$ put
$m=(1-2b_0)(1+b_1)(1+2b_2)(1+4b_3)(1+6b_4)(1+12b_5)$, $A=mB$, $H=A(A-B^2)$,
$T_1=A(A-e)(A+3e)$, $T_2=A(Az^2-eH)(Az^2+3eH)$ and
$$Q_{\rm pole}=B\Bigl(\sum_{i=0}^5(b_i^2-b_i)^2+(eHzw-1)^2+(r_1^2-T_1)^2+(r_2^2-T_2)^2\Bigr).$$
Write $\Phi(B)$ when $Q_{\rm pole}$ has a rational zero with input $B$.

Pole completeness is the assertion that every rational $B$ with square reduced
denominator, $0<B<1/2$ and $v_p(B)\ge4$ for every $p\in\{2,3,5,7,13\}$ satisfies $\Phi(B)$.

The manuscript derives it from its restricted converse theorem by a simultaneous descent;
here it is a hypothesis of the main theorem.

## Depends on

None.

## Sources

- [Theorem 5.2](../../sources/manuscript.md#theorem-52)
