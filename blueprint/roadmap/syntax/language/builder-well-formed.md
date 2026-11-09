---
article_id: af_8ec1e84ea39a69fedee17d32
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Syntax.Formula.InScope, ZInQ.Syntax.ExPoly.WitnessScope, ZInQ.Syntax.ExPoly.WitnessScope.rel_iff, ZInQ.Syntax.ExPoly.WitnessScope.wf, ZInQ.Syntax.Build.Facts.witnessScope, ZInQ.Syntax.templateLibrary_witnessScope, ZInQ.Syntax.CompositionRecipe.witnessScope_of, ZInQ.Syntax.closeRecipe_callBlocks_disjoint, ZInQ.Syntax.mainRecipe_callBlocks_disjoint, ZInQ.Syntax.valueUnionRecipe_callBlocks_disjoint, ZInQ.Syntax.valueRecipe_callBlocks_disjoint, ZInQ.Syntax.integersRecipe_callBlocks_disjoint, ZInQ.Syntax.translate_witnessScope, ZInQ.Syntax.specLib_witnessScope, ZInQ.Syntax.specLib_precisionCircuit_witnessScope
---

# Witness scope of constructed templates and recipes

Call an existential polynomial $\tau$ with $p$ parameters and $v$ variables *in scope* if
$[\![\tau]\!]=\kappa(\varphi)$ for a formula $\varphi$ such that

1. every call atom of $\varphi$ with callee witness count $m$ and witness start $w$ satisfies
   $p\le w$ and $w+m\le v$, and its callee has all its variables below its variable count;
2. the blocks $[w,w+m)$ of the call atoms are pairwise disjoint;
3. no variable of a block occurs in a parameter polynomial of any call atom or in any atom
   $a\doteq b$ or $\langle f\rangle$ of $\varphi$;
4. every variable occurring in $\kappa(\varphi)$ has index below $v$.

Then $\mathrm{Rel}_\tau(a)$ holds exactly when $\varphi^\ast$ holds at some assignment
extending $a$, and every variable of $[\![\tau]\!]$ has index below $v$.

Every template of the library is in scope (with $\varphi=\bigwedge(E_1,\dots,E_r,\varphi_0)$
for its construction). A composition recipe is in scope when its call arguments lie below a
bound $B\ge p$, its calls start at or above $B$, and its call blocks are pairwise disjoint;
the five composition recipes of the specification satisfy this with
$B=51$ (close), $11$ (main), $6$ (value_union, value, integers): their blocks are
allocated one after another above the parameters and fresh ranges. The model-evaluation
translation of a well-formed natural circuit is in scope. Hence every recipe of the
specification is in scope.

**Proof sketch.** For a template, the list of call blocks of its construction is computed
from the counter and checked to be separated and above $p$; the parameter polynomials and
atoms are checked to use only variables below $v$ outside the blocks; constant variables
are allocated by the counter. A construction may use a call atom twice, so this check is
made per template. For a composition recipe the arguments are parameters or fresh-range
variables below $B$ and the blocks lie at or above $B$. For the translation every
reference, generator variable and block is allocated by its counter. The relational form
is the private-witness lemma.

## Depends on

- [Formulas and their polynomial compilation](formula-compilation.md)
- [Semantics of templates and recipes](../template-semantics.md)
- [Translation of a natural circuit into a model-evaluation recipe](../recipes/model-evaluation-translation.md)

## Proof depends on

- [Template construction from formulas](builder-soundness.md)

## Sources

- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
- [Section 2.1](../../../sources/syntax-locators.md#section-21-literal-operations)
