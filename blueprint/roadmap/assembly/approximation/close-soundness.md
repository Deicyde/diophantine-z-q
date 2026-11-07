---
article_id: af_851f7522e171d8ed1b5ad5a0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Assembly.close_sound
---

# Soundness of Close

Assume the six-contact estimate, pole completeness and the twenty-two-prime
pattern. Let $n,\kappa\in\mathbb Z$ and $t\in\mathbb Q$. If
$\mathrm{Rel}_{\mathtt{close}}(\iota(n),\iota(\kappa),t)$, then $n\notin\mathcal C$, $\kappa\ne0$ and, in
$\mathbb R$,
$$|t-n|<e^{-B(n,\kappa)} .$$

**Proof sketch.** The Close relation gives $n',\kappa',a,l$ with $\iota(n')=\iota(n)$,
$\iota(\kappa')=\iota(\kappa)$, $\operatorname{Prec}(n',\kappa',a,l,n'a)$ and $|t-r(a,n'a)|<\epsilon_l$;
injectivity of $\iota$ gives $n'=n$, $\kappa'=\kappa$. The precision relation contains
$n\notin\mathcal C$, $\kappa\ne0$, $|r(a,na)-n|<\epsilon_l$ and $4\epsilon_l\cdot4^{B}<1$ with $B=B(n,\kappa)\ge0$.
By the triangle inequality,
$$|t-n|<2\epsilon_l<\tfrac12\,4^{-B}<e^{-B},$$
the last step because $(e/4)^B\le1<2$. No height input is used here.

## Depends on

- [The precision relation](../../compiler/natural/precision/precision-relation.md)
- [The precision constant is the six-contact constant](../../compiler/natural/precision/precision-height-constant-value.md)
- [The outer composition recipes](../../syntax/recipes/outer-recipes.md)
- [Point codes](../../model/point-codes.md)
- [The six-contact height estimate](../../main/six-contact-estimate.md)
- [Pole completeness](../../main/pole-completeness.md)
- [The twenty-two-prime pattern](../../main/prime-pattern.md)

## Proof depends on

- [The relation Close](close-relation.md)
- [Nonzero multiples of the generator](../../model/descent/nonzero-multiples.md)

## Sources

- [Section 11.1 approximation](../../../sources/assembly-locators.md#section-111-approximation)
