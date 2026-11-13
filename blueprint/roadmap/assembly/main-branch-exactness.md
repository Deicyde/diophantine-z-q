---
article_id: af_c2eabc7d6216274a29a6698f
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Assembly.main_branch_eq
---

# An accepting main branch forces the exact value

Assume the minimal height hypothesis, pole completeness and the slope
representation. Let $n,\kappa\in\mathbb Z$ and $t\in\mathbb Q$. If
$\mathrm{Rel}_{\mathtt{close}}(\iota(n),\iota(\kappa),t)$ and $\operatorname{Test}(n,\kappa,t)$, then $t=n$.

**Proof sketch.** Soundness of Close gives $n\notin\mathcal C$, $\kappa\ne0$ and
$|t-n|<e^{-B(n,\kappa)}$. The test gives $t\notin\mathcal C$ and, by the divisibility lemma,
$M_{S_{\rm ht}}(t)\mid\kappa F(n)$; as $\kappa F(n)\ne0$, $M_{S_{\rm ht}}(t)\le|\kappa F(n)|$. Apply the
minimal height hypothesis at $u=t\notin\mathcal C$; since $S_{\rm ht}\subseteq S_{\rm mul}$,
$M_{S_{\rm mul}}(t)$ divides $M_{S_{\rm ht}}(t)$, so
$$h(t)\le H_6(D)\,M_{S_{\rm mul}}(t)^{24}\le H_6(D)\,M_{S_{\rm ht}}(t)^{24}\le A^{(0)}_{\rm ht}\,|\kappa F(n)|^{24}=B(n,\kappa),$$
where $H_6(D)=H_6(S_{\rm ht};D)=A^{(0)}_{\rm ht}$ is the precision height constant. Suppose
$t=a/b\ne n$ in lowest terms, $b>0$. Then $|a-nb|\ge1$, so
$$|t-n|\ge1/b\ge e^{-h(t)}\ge e^{-B(n,\kappa)},$$
contradicting soundness of Close. Hence $t=n$. No numerical value of $A^{(0)}_{\rm ht}$ or $D$ is needed.

## Depends on

- [The precision height constant](../compiler/natural/precision/precision-height-constant.md)
- [The precision constant is the six-contact constant](../compiler/natural/precision/precision-height-constant-value.md)
- [The six local tests](value-templates/six-local-tests.md)
- [The outer composition recipes](../syntax/recipes/outer-recipes.md)
- [Point codes](../model/point-codes.md)
- [The minimal height hypothesis](../main/six-contact-min.md)
- [Pole completeness](../main/pole-completeness.md)
- [The slope representation](../multiplication/completeness/slope-representation.md)

## Proof depends on

- [Soundness of Close](approximation/close-soundness.md)
- [Divisibility from the six local tests](local-tests/test-divisibility.md)

## Sources

- [Section 11.3 exact ordinary value](../../sources/assembly-locators.md#section-113-exact-ordinary-value)
- [Section 4 height constants](../../sources/assembly-locators.md#section-4-height-constants)
