---
article_id: af_18174ab9ea75bc03b5db2e73
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.legBit_absNorm_eq_of_mk0_eq, ZInQ.RouteK.Redei.legBit_absNorm_mul, ZInQ.RouteK.Redei.not_dvd_absNorm_mul, ZInQ.RouteK.Redei.intCast_natCast_zmod_ne_zero
---

# The norm residue bit depends only on the class

Let $n\ge1$ be squarefree, $\mathcal O$ the ring of integers of $\mathbb Q(\sqrt{-n})$ and $q$ a
prime dividing $n$. If $I$ and $J$ are nonzero ideals of $\mathcal O$ in the same ideal class,
with $q\nmid N(I)$ and $q\nmid N(J)$, then
$$[N(I)/q]=[N(J)/q].$$
Along the way, for every $n\ge1$, every prime $q$ and ideals $I,J$ of $\mathcal O$ with
$q\nmid N(I)$ and $q\nmid N(J)$: $q\nmid N(IJ)$ and $[N(IJ)/q]=[N(I)/q]+[N(J)/q]$. (A natural
number not divisible by $q$ is nonzero modulo $q$.)

**Proof sketch.** Take a nonzero ideal $M$ in the inverse class of $[I]$ with $q\nmid N(M)$. For
every nonzero $L$ in the class of $I$ with $q\nmid N(L)$, the ideal $LM=(\alpha)$ is principal, so
$[N(L)/q]+[N(M)/q]=[N(LM)/q]=[N((\alpha))/q]=0$, because norms are squares modulo $q$ and the
residue bit is additive on integers prime to $q$. In $\mathbb F_2$, $a+b=0$ means $a=b$, so
$[N(L)/q]=[N(M)/q]$. Apply this to $L=I$ and $L=J$.

## Depends on

- [The genus class number](../genus-class-number.md)
- [Residue bits](../../route-k/residue-bits.md)

## Proof depends on

- [Every class has a representative of norm prime to $q$](coprime-representatives.md)
- [Norms are squares modulo the primes of $n$](norms-are-squares.md)
- [Quadratic reciprocity in residue bits](../../route-k/reciprocity-bits.md)

## Sources

- [The chosen route](../../../sources/redei-locators.md#the-chosen-route)
- [Step 4: genus characters](../../../sources/redei-locators.md#step-4-genus-characters)
