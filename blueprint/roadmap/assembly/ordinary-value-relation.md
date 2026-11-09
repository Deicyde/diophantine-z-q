---
article_id: af_bf7be178fc60cecba49ca513
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Assembly.value_relation_iff, ZInQ.Assembly.exists_value_relation_iff
---

# The exact ordinary-value relation

Assume the minimal height hypothesis, pole completeness and the slope
representation. Then for every $N\in\mathbb Q^5$ and every $t\in\mathbb Q$,
$$\mathrm{Rel}_{\mathtt{value}}(N,t)\iff\exists\,n\in\mathbb Z:\ N=\iota(n)\ \text{and}\ t=n .$$
Consequently, for every $t\in\mathbb Q$,
$$\bigl(\exists\,N\in\mathbb Q^5:\ \mathrm{Rel}_{\mathtt{value}}(N,t)\bigr)\iff t\in\mathbb Z .$$

In the manuscript's notation, $\operatorname{Val}(N,t)$ is membership of $N$ together with
$\bigvee_{c\in\mathcal C}(N=\iota(c)\wedge t=c)\ \vee\ \exists\mathcal K\,(\operatorname{Close}(N,\mathcal K,t)\wedge\operatorname{Test}(N,\mathcal K,t))$,
with the same five coordinates $\mathcal K$ in both calls, and $\operatorname{Val}(\iota(n),t)$
is exactly the graph $t=n$.

**Proof sketch.** By the relations of the outer recipes, $\mathrm{Rel}_{\mathtt{value}}(N,t)$ holds
exactly when $N$ is accepted by membership and either the exceptional relation holds or
there is $K$ with $\mathrm{Rel}_{\mathtt{close}}(N,K,t)$ and $\mathrm{Rel}_{\mathtt{value.test}}(N,K,t)$.

($\Rightarrow$) Membership gives $N=\iota(n)$. In the exceptional branch, $N=\iota(c)$ and $t=c$ for
some $c\in\mathcal C$, and $c=n$ by injectivity of $\iota$. In the main branch, the value-test
semantics gives $N=\iota(n')$, $K=\iota(\kappa)$ and $\operatorname{Test}(n',\kappa,t)$ with $n'=n$; then
$\mathrm{Rel}_{\mathtt{close}}(\iota(n),\iota(\kappa),t)$ and $\operatorname{Test}(n,\kappa,t)$ force $t=n$.

($\Leftarrow$) Let $N=\iota(n)$ and $t=n$; $N$ is accepted by membership. If $n\in\mathcal C$, the
exceptional relation holds. If $n\notin\mathcal C$, choose $\kappa\ne0$ with $\operatorname{Test}(n,\kappa,n)$
(one suitable shift), then $\mathrm{Rel}_{\mathtt{close}}(\iota(n),\iota(\kappa),n)$ for that same shift
(completeness of Close), and $\mathrm{Rel}_{\mathtt{value.test}}(\iota(n),\iota(\kappa),n)$; the main
relation holds with $K=\iota(\kappa)$. The two calls have disjoint private blocks, so they are
satisfied simultaneously, and the block of the inactive factor of the product takes
arbitrary values.

For the consequence, project to $t$: the right side becomes $\exists n\in\mathbb Z,\ t=n$. For
$n\in\mathcal C$ the main branch is never accepted (Close requires $n\notin\mathcal C$), so the six
exceptional integers are given exactly by their displayed branches.

## Depends on

- [The outer composition recipes](../syntax/recipes/outer-recipes.md)
- [Point codes](../model/point-codes.md)
- [The minimal height hypothesis](../main/six-contact-min.md)
- [Pole completeness](../main/pole-completeness.md)
- [The slope representation](../multiplication/completeness/slope-representation.md)

## Proof depends on

- [Relations of the outer recipes](value-templates/outer-recipe-relations.md)
- [Accepted inputs have unique indices](../model/membership-indices.md)
- [Semantics of the exceptional values](value-templates/exceptions-semantics.md)
- [Semantics of the value-test template](value-templates/value-test-semantics.md)
- [An accepting main branch forces the exact value](main-branch-exactness.md)
- [One suitable shift](local-tests/test-completeness.md)
- [Completeness of Close for every fixed shift](approximation/close-completeness.md)
- [Mordell-Weil for $E/K_0$ from the descent](../model/descent/mordell-weil-from-descent.md)

## Sources

- [Section 11.3 exact ordinary value](../../sources/assembly-locators.md#section-113-exact-ordinary-value)
- [Section 11 opening](../../sources/assembly-locators.md#section-11-opening)
- [Lemma 1.2](../../sources/assembly-locators.md#lemma-12)
