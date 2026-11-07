---
article_id: af_300f2ca3b34a188effa5b5e6
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Assembly.close_rel_iff, ZInQ.Assembly.main_rel_iff, ZInQ.Assembly.valueUnion_rel_iff, ZInQ.Assembly.value_rel_iff, ZInQ.Assembly.spec_close_rel_iff, ZInQ.Assembly.spec_main_rel_iff, ZInQ.Assembly.spec_valueUnion_rel_iff, ZInQ.Assembly.spec_value_rel_iff
---

# Relations of the outer recipes

For all $N,K\in\mathbb Q^5$ and $t\in\mathbb Q$:

1. $\mathrm{Rel}_{\mathtt{close}}(N,K,t)$ holds exactly when there are
   $A,L,J,E_0,\dots,E_4\in\mathbb Q^5$ with
   $\mathrm{Rel}_{\mathtt{value.signed\_encode}}(\Sigma_i,E_i)$ for
   $(\Sigma_0,\dots,\Sigma_4)=(N,K,A,L,J)$, $\mathrm{Rel}_{\mathtt{precision}}(E_0,\dots,E_4)$ and
   $\mathrm{Rel}_{\mathtt{value.close\_coordinates}}(A,L,J,t)$;
2. $\mathrm{Rel}_{\mathtt{main}}(N,t)\iff\exists\,K\in\mathbb Q^5:\ \mathrm{Rel}_{\mathtt{close}}(N,K,t)\wedge\mathrm{Rel}_{\mathtt{value.test}}(N,K,t)$;
3. $\mathrm{Rel}_{\mathtt{value\_union}}(N,t)\iff\mathrm{Rel}_{\mathtt{value.exceptions}}(N,t)\vee\mathrm{Rel}_{\mathtt{main}}(N,t)$;
4. $\mathrm{Rel}_{\mathtt{value}}(N,t)\iff\mathrm{Rel}_{\mathtt{member}}(N)\wedge\mathrm{Rel}_{\mathtt{value\_union}}(N,t)$.

In 2 the same five coordinates of $K$ are passed to both calls: one shared shift.

**Proof sketch.** Each outer recipe is a composition recipe: its polynomial is the sum of the
squares (for $\mathtt{value\_union}$, the product) of its call polynomials, which is $\kappa$ of
the conjunction (disjunction) of the call atoms. By the witness accounting and the
witness-scope theorem, the call blocks lie inside the recipe's variables, are pairwise
disjoint, are disjoint from the fresh ranges, and occur in no parameter. The private-witness
lemma then replaces each call by its callee relation, and the fresh ranges ($A,L,J,E_0,\dots,E_4$
for $\mathtt{close}$, $K$ for $\mathtt{main}$) become existential quantifiers. For the product
recipe, the block of an inactive factor takes arbitrary values; this does not discard any
fixed equation of the active factor.

## Depends on

- [The outer composition recipes](../../syntax/recipes/outer-recipes.md)
- [Semantics of templates and recipes](../../syntax/template-semantics.md)

## Proof depends on

- [Witness accounting of the specified polynomial](../../syntax/recipes/witness-accounting.md)
- [Witness scope of constructed templates and recipes](../../syntax/language/builder-well-formed.md)
- [Private witness blocks](../../syntax/language/existential-lifting.md)
- [Evaluation of a template call](../../syntax/language/call-semantics.md)
- [Sums of squares and products over the rationals](../../syntax/sum-of-squares-semantics.md)

## Sources

- [Section 11.3 exact ordinary value](../../../sources/assembly-locators.md#section-113-exact-ordinary-value)
- [Lemma 1.2](../../../sources/assembly-locators.md#lemma-12)
- [Saved specification outer recipes](../../../sources/assembly-locators.md#saved-specification-outer-recipes)
