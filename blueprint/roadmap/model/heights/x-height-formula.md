---
article_id: af_4f21abe36db357529726c285
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.hK0_div, ZInQ.hK0_div_of_isCoprime, ZInQ.hK0_ratCast
---

# The height of a fraction in $\mathbb Z[\sqrt2]$

Let $a,b\in\mathbb Z[s]$ with $b\ne0$, and let $g$ be a greatest common divisor
of $a$ and $b$ in $\mathbb Z[s]$. Then
$$h(a/b)=\frac12\Bigl(\log\max(|\sigma_+a|,|\sigma_+b|)+\log\max(|\sigma_-a|,|\sigma_-b|)
-\log|\operatorname N(g)|\Bigr).$$
In particular, for coprime $a,b$,
$\exp(2h(a/b))=\max(|\sigma_+a|,|\sigma_+b|)\cdot\max(|\sigma_-a|,|\sigma_-b|)$; for a rational
$p/q$ in lowest terms with $q>0$, $h(p/q)=\log\max(|p|,q)$; and $h\ge0$.

**Proof sketch.** Write $a=ga'$, $b=gb'$ with $a',b'$ coprime; the right side is unchanged
because $\prod_\sigma|\sigma g|=|\operatorname N(g)|$. For coprime $a',b'$ and $x=a'/b'$,
$\sum_v n_v\log\max(1,|x|_v)=\sum_v n_v\log\max(|a'|_v,|b'|_v)-\sum_vn_v\log|b'|_v$; the last sum
vanishes by the product formula, and at every finite place $\max(|a'|_v,|b'|_v)=1$ by
coprimality, leaving the two real places. Integers $p,q$ coprime in $\mathbb Z$ are coprime in
$\mathbb Z[s]$, and then both real places give $\max(|p|,q)$.

## Depends on

- [The $x$-height on $C(K_0)$](x-height.md)
- [$\mathbb Z[\sqrt2]$ is a principal ideal domain](../field/integers-pid.md)

## Sources

- [Duplication bounds](../../../sources/model-locators.md#duplication-bounds)
