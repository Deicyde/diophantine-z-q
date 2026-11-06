---
article_id: af_733a993b598b73f751803fd0
declaration: theorem
origin: cited
---

# Natural codes

Assume the six-contact estimate, pole completeness, the Mordell–Weil hypothesis and the
twenty-two-prime pattern (the hypotheses of the multiplication statement M). Then for every
$A\in\mathbb Q^5$,
$$\mathrm{Rel}_{\mathtt{natural}}(A)\iff\exists\,c\in\mathbb N:\ A=\iota(c).$$
This is an all-input statement: $A$ is an arbitrary rational $5$-tuple.

**Proof sketch.** The $\mathtt{natural}$ template is $\kappa(\varphi)^2$ for the conjunction
$\varphi$ of four calls $\langle\mathtt{multiply}[\sigma_i,\sigma_i,\Sigma_i]\rangle$ and three calls
$\langle\mathtt{raw\_add}[\Sigma_0,\Sigma_1,\pi_1]\rangle$, $\langle\mathtt{raw\_add}[\pi_1,\Sigma_2,\pi_2]\rangle$,
$\langle\mathtt{raw\_add}[\pi_2,\Sigma_3,A]\rangle$, with fresh points $\sigma_i,\Sigma_i,\pi_1,\pi_2$ and pairwise
disjoint call blocks that occur in no parameter. By the private-witness lemma,
$\mathrm{Rel}_{\mathtt{natural}}(A)$ holds exactly when there are $\sigma_i,\Sigma_i,\pi_1,\pi_2\in\mathbb Q^5$ with
the seven callee relations.

($\Rightarrow$) Statement M (soundness on arbitrary rational triples) gives
$\sigma_i=\iota(a_i)$ and $\Sigma_i=\iota(a_i^2)$ with $a_i\in\mathbb Z$. Raw addition on canonical
codes then forces $\pi_1=\iota(a_0^2+a_1^2)$, $\pi_2=\iota(a_0^2+a_1^2+a_2^2)$ and
$A=\iota(c)$ with $c=a_0^2+a_1^2+a_2^2+a_3^2\in\mathbb N$.

($\Leftarrow$) By Lagrange's four-square theorem $c=a_0^2+a_1^2+a_2^2+a_3^2$ with $a_i\in\mathbb N$.
Take $\sigma_i=\iota(a_i)$, $\Sigma_i=\iota(a_i^2)$ and the partial sums for $\pi_1,\pi_2$; statement
M (completeness) and raw addition supply the seven callee relations.

The order matters: the tuples $\sigma_i,\Sigma_i$ are untyped until the multiplication calls
type them, and only then do the raw additions receive canonical inputs.

## Depends on

- [The natural-code template](../../syntax/templates/template-natural.md)
- [Point codes](../../model/point-codes.md)
- [The six-contact height estimate](../../main/six-contact-estimate.md)
- [Pole completeness](../../main/pole-completeness.md)
- [Mordell–Weil for the generator curve](../../main/mordell-weil.md)
- [The twenty-two-prime pattern](../../main/prime-pattern.md)

## Proof depends on

- [Correctness of the multiplication template](../../multiplication/multiplication-template.md)
- [Raw addition](../../model/raw-addition.md)
- [Private witness blocks](../../syntax/language/existential-lifting.md)
- [Template construction from formulas](../../syntax/language/builder-soundness.md)
- [Witness scope of constructed templates and recipes](../../syntax/language/builder-well-formed.md)

## Sources

- [Section 3.1 natural codes](../../../sources/assembly-locators.md#section-31-natural-codes)
- [Section 10.4 translation](../../../sources/assembly-locators.md#section-104-translation)
