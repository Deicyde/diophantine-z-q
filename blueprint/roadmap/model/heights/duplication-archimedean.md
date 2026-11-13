---
article_id: af_1e120dbdaee11316bbac7642
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.duplication_archimedean
---

# Archimedean bounds for the duplication forms

Let $\Delta$ be a real number with $1\le\Delta\le5$, let $a,b\in\mathbb R$, $M=\max(|a|,|b|)$,
$F=(a^2+\Delta^2b^2)^2$ and $G=4ab(a^2-\Delta^2b^2)$. Then
$$M^4\le\max(|F|,|G|)\le676\,M^4 .$$
Since $\sigma_\pm(\delta)=3\mp\sqrt2\in[1,5]$, at either real embedding of $K_0$ the values of the
duplication forms satisfy
$\max(|\sigma a|,|\sigma b|)^4\le\max(|\sigma F_2(a,b)|,|\sigma G_2(a,b)|)\le676\max(|\sigma a|,|\sigma b|)^4$.

**Proof sketch.** $a^2+\Delta^2b^2\ge a^2+b^2\ge M^2$ gives the lower bound from $F$ alone.
$a^2+\Delta^2b^2\le26M^2$ gives $F\le676M^4$, and
$|G|\le4|a||b|(a^2+\Delta^2b^2)\le104M^4$. The constant $676=26^2$.

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](../field/quadratic-field.md)
- [The duplication forms on $C$](duplication-forms.md)

## Proof depends on

- [Explicit identities in $K_0$](../field/explicit-identities.md)

## Sources

- [Duplication bounds](../../../sources/model-locators.md#duplication-bounds)
