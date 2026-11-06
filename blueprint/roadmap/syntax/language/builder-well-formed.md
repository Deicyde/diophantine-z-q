---
article_id: af_8ec1e84ea39a69fedee17d32
declaration: theorem
origin: bridged
---

# Witness scope of constructed templates and recipes

Let $\tau$ be a template obtained from a template construction, or a recipe obtained by the
model-evaluation translation or as a composition recipe, with parameter count $p$ and
variable count $v$, and suppose every template and recipe it calls has the properties
below. Then:

1. every call of $\tau$ with callee witness count $m$ and witness start $w$ satisfies
   $p\le w$ and $w+m\le v$, and the blocks $[w,w+m)$ of distinct calls are disjoint;
2. the blocks, the fresh variables (including rational-constant variables, generator
   variables, allocated points and the fresh ranges of a composition) are pairwise disjoint
   and together cover $[p,v)$ exactly;
3. no variable of a call's block occurs in a parameter polynomial of any call of $\tau$, in a
   point reference of $\tau$, or in any atom or constraint of $\tau$ other than through that
   call;
4. every variable occurring in $[\![\tau]\!]$ has index below $v$.

**Proof sketch.** All three kinds of construction allocate variables from one counter that
starts at $p$: a fresh variable or point takes the next one or five indices, a call takes
the next $m$ indices for its block, and nothing else changes the counter. Hence the
allocated intervals are consecutive, disjoint and cover $[p,v)$, giving 1 and 2. A caller
never creates a variable node, a point reference or a parameter expression for an index
inside a block: block indices are only passed to the callee as its witness start. This
gives 3. For 4, a variable node of $\tau$ has index below the counter (by the construction
theorem for templates, and by inspection of the reference and composition rules for
recipes), and a call contributes the variables of its parameter polynomials together with
the shifted callee variables $X_{w+i-p'}$ for callee variables $i<v'$, which lie in the
block $[w,w+m)$ by the induction hypothesis on the callee.

## Depends on

- [Formulas and their polynomial compilation](formula-compilation.md)
- [Semantics of templates and recipes](../template-semantics.md)
- [Translation of a natural circuit into a model-evaluation recipe](../recipes/model-evaluation-translation.md)

## Proof depends on

- [Template construction from formulas](builder-soundness.md)

## Sources

- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
- [Section 2.1](../../../sources/syntax-locators.md#section-21-literal-operations)
