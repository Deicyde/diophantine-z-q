---
article_id: af_c2eabc7d6216274a29a6698f
declaration: theorem
origin: bridged
---

# An accepting main branch forces the exact value

Assume the six-contact estimate, pole completeness, the Mordell–Weil hypothesis and the
twenty-two-prime pattern. Let $n,\kappa\in\mathbb Z$ and $t\in\mathbb Q$. If
$\mathrm{Rel}_{\mathtt{close}}(\iota(n),\iota(\kappa),t)$ and $\operatorname{Test}(n,\kappa,t)$, then $t=n$.

**Proof sketch.** Soundness of Close gives $n\notin\mathcal C$, $\kappa\ne0$ and
$|t-n|<e^{-B(n,\kappa)}$. The test gives $t\notin\mathcal C$ and, by the divisibility lemma,
$M_{S_{\rm ht}}(t)\mid\kappa F(n)$; as $\kappa F(n)\ne0$, $M_{S_{\rm ht}}(t)\le|\kappa F(n)|$. Apply the
six-contact estimate with $S=S_{\rm ht}$ (all primes $p\le324$, maximum $317$) and $R=D$,
which satisfies $R\ge\max(D,\max S,10^{12})$ because that maximum is $D$, at $u=t\notin\mathcal C$:
$$h(t)\le H_6(S_{\rm ht};D)\,M_{S_{\rm ht}}(t)^{24}\le A^{(0)}_{\rm ht}\,|\kappa F(n)|^{24}=B(n,\kappa),$$
where $H_6(S_{\rm ht};D)=A^{(0)}_{\rm ht}$ is the precision height constant. Suppose
$t=a/b\ne n$ in lowest terms, $b>0$. Then $|a-nb|\ge1$, so
$$|t-n|\ge1/b\ge e^{-h(t)}\ge e^{-B(n,\kappa)},$$
contradicting soundness of Close. Hence $t=n$. No numerical value of $A^{(0)}_{\rm ht}$ or $D$ is needed.

## Depends on

- [The precision height constant](../compiler/natural/precision/precision-height-constant.md)
- [The precision constant is the six-contact constant](../compiler/natural/precision/precision-height-constant-value.md)
- [The six local tests](value-templates/six-local-tests.md)
- [The outer composition recipes](../syntax/recipes/outer-recipes.md)
- [Point codes](../model/point-codes.md)
- [The six-contact height estimate](../main/six-contact-estimate.md)
- [Pole completeness](../main/pole-completeness.md)
- [Mordell–Weil for the generator curve](../main/mordell-weil.md)
- [The twenty-two-prime pattern](../main/prime-pattern.md)

## Proof depends on

- [Soundness of Close](approximation/close-soundness.md)
- [Divisibility from the six local tests](local-tests/test-divisibility.md)

## Sources

- [Section 11.3 exact ordinary value](../../sources/assembly-locators.md#section-113-exact-ordinary-value)
- [Section 4 height constants](../../sources/assembly-locators.md#section-4-height-constants)
