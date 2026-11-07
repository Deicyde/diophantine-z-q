---
article_id: af_8ffaa295758fff6712545d61
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Translation.MultiplicationExact, ZInQ.Translation.natural_rel_iff
---

# The natural-code predicate

Assume the multiplication statement M in its
all-input form: for all $p,q,r\in\mathbb Q^5$,
$$\mathrm{Rel}_{\mathtt{multiply}}(p,q,r)\iff\exists\,a,b\in\mathbb Z:\ p=\iota(a),\ q=\iota(b),\ r=\iota(ab).$$
Then for every $A\in\mathbb Q^5$ (an arbitrary rational $5$-tuple, not assumed to be a code)
$$\mathrm{Rel}_{\mathtt{natural}}(A)\iff A=\iota(n)\ \text{for some }n\in\mathbb N .$$
In words: the natural-code template accepts exactly the codes of the nonnegative indices.
Its four square roots are typed by the multiplication calls before their squares are added,
so the three raw additions only ever receive canonical codes.

**Proof sketch.** The polynomial of $\mathtt{natural}$ is the square of the compilation of a
conjunction of seven calls with pairwise disjoint private blocks; the points
$\sigma_0,\dots,\sigma_3,\Sigma_0,\dots,\Sigma_3,\pi_1,\pi_2$ are fresh variables occurring in no
block. By the private-block theorem,
$\mathrm{Rel}_{\mathtt{natural}}(A)$ holds exactly when there are
$\sigma_i,\Sigma_i,\pi_1,\pi_2\in\mathbb Q^5$ with
$$\mathrm{Rel}_{\mathtt{multiply}}(\sigma_i,\sigma_i,\Sigma_i)\ (i=0,\dots,3),\quad
\mathrm{Add}_{\rm raw}(\Sigma_0,\Sigma_1,\pi_1),\quad\mathrm{Add}_{\rm raw}(\pi_1,\Sigma_2,\pi_2),\quad
\mathrm{Add}_{\rm raw}(\pi_2,\Sigma_3,A).$$

($\Rightarrow$) By M, $\sigma_i=\iota(a_i)=\iota(b_i)$ and $\Sigma_i=\iota(a_ib_i)$ for integers
$a_i,b_i$. Since $\iota$ is injective (generator certificate), $a_i=b_i$ and
$\Sigma_i=\iota(a_i^2)$. (Injectivity can be avoided: codes are injective on points, so
$[a_i]P_0=[b_i]P_0$ and $[a_ib_i]P_0=[a_i]([b_i]P_0)=[a_i]([a_i]P_0)=[a_i^2]P_0$.) The three raw additions now have canonical inputs, so by the
raw-addition contract $\pi_1=\iota(a_0^2+a_1^2)$, $\pi_2=\iota(a_0^2+a_1^2+a_2^2)$ and
$A=\iota(a_0^2+a_1^2+a_2^2+a_3^2)$, and $n=\sum_ia_i^2\in\mathbb N$.

($\Leftarrow$) Write $n=\sum_ia_i^2$ with $a_i\in\mathbb N$ by Lagrange's theorem and put
$\sigma_i=\iota(a_i)$, $\Sigma_i=\iota(a_i^2)$, $\pi_1=\iota(a_0^2+a_1^2)$,
$\pi_2=\iota(a_0^2+a_1^2+a_2^2)$. The multiplication relations hold by M (with $a=b=a_i$) and
the three additions by the raw-addition contract; the private-block theorem supplies the
witnesses of the seven calls.

The completeness half of M is essential here; the generator certificate alone does not give
this predicate.

## Depends on

- [The natural-code template](../../syntax/templates/template-natural.md)
- [Point codes](../../model/point-codes.md)
- [Correctness of the multiplication template](../../multiplication/multiplication-template.md)

## Proof depends on

- [Private witness blocks](../../syntax/language/existential-lifting.md)
- [Template construction from formulas](../../syntax/language/builder-soundness.md)
- [Raw addition](../../model/raw-addition.md)
- [The generator certificate](../../model/generator.md)
- [Lagrange's four-square theorem](lagrange-four-squares.md)
- [Mordell-Weil for $E/K_0$ from the descent](../../model/descent/mordell-weil-from-descent.md)

## Sources

- [Section 3.1](../../../sources/compiler-translation-locators.md#section-31-natural-predicate)
- [Section 10.4](../../../sources/compiler-translation-locators.md#section-104-typing-order)
- [Translation artifacts](../../../sources/compiler-translation-locators.md#translation-artifacts)
