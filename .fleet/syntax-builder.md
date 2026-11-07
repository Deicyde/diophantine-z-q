# syntax-builder: template constructions and witness scope

Directory `ZInQKernel/Syntax/Builder/`, root module `ZInQKernel/Syntax/Builder.lean` (imported
from `ZInQKernel.lean`). `lake build ZInQKernel` succeeds. No `sorry`, no new hypothesis, no
finite-computation input.

| Article | Lean name | Status |
| --- | --- | --- |
| syntax/language/formula-compilation.md | `ZInQ.Syntax.Formula`, `ZInQ.Syntax.Formula.compile`, `ZInQ.Syntax.Formula.Holds`, `ZInQ.Syntax.Build`, `ZInQ.Syntax.Build.fresh`, `ZInQ.Syntax.Build.call`, `ZInQ.Syntax.Build.rational`, `ZInQ.Syntax.globalEq`, `ZInQ.Syntax.Build.template`, `ZInQ.Syntax.Build.fullFormula`, `ZInQ.Syntax.Build.nz`, `ZInQ.Syntax.Build.pos` (all existing); `ZInQ.Syntax.Build.template_eq` (new) | proved (definition) |
| syntax/language/builder-soundness.md | `ZInQ.Syntax.Build.template_construction` (new), with `ZInQ.Syntax.Build.Allocates` | proved |
| syntax/language/builder-well-formed.md | `ZInQ.Syntax.ExPoly.WitnessScope`, `ZInQ.Syntax.templateLibrary_witnessScope`, `ZInQ.Syntax.specLib_witnessScope`, `ZInQ.Syntax.specLib_precisionCircuit_witnessScope` (new) | proved |

## What plays the role of each article

The articles were written for a hash-consed node encoding. The Lean library builds templates
with the state monad `Build` (counter and global equations) and defines the template of a
construction directly as `⟨p, v - p, κ(⋀(E₁, …, E_r, φ))⟩` (`Build.template`). There is no node
list, so "the node list denotes the compiled formula" is true by definition
(`Build.template_eq`, `rfl`). The consumers use three facts.

1. **Formula compilation** (definition). Consumers (every template article, `rational-constants`,
   `positivity-gadget`, …) use `Formula.compile`, `Build.template`, `Build.rational` with
   `Build.rational_apply_new/old/one`, the gadgets `Build.nz`, `Build.pos` with
   `Build.nz_apply`, `Build.pos_apply`. All of these existed; I added only
   `Build.template_eq`.

2. **Builder soundness.** Consumers (`template-witness-counts`, the semantics articles of the
   templates, `natural-code-semantics`, `hierarchical-calls`) need: parameter count `p`,
   variable count `v`, polynomial `κ(⋀(E, φ))`, and the variables below `v`. New:
   `Build.Allocates b` (the program uses the state only as a counter: the counter does not
   decrease, and new global equations are for newly allocated variables, in increasing
   order), proved for every primitive (`fresh`, `freshIdx`, `call`, `rational`, `nz`, `pos`,
   `fnz`, `fdiv`, `zGadget`, `freshPoint`, `freshPair`, `point`, `freshPoints`, `freshPairs`,
   `gen`, `mapL`) and closed under `bind` (`Build.Allocates.bind`), and
   `Build.template_construction`: for an allocating construction, `params = p`,
   `varCount = v`, `poly = κ(⋀(E₁, …, E_r, φ))`, the constant variables are increasing and lie
   in `[p, v)`, and the template is well formed as soon as `κ(φ)` has its variables below
   `v`. The counts of the library templates were already proved
   (`templateLibrary_params`, `templateLibrary_witnesses`, `Build.Facts.witnesses`).

3. **Witness scope.** Consumers: `witness-accounting` (variables below the variable count),
   `outer-recipe-relations` (composition recipes: blocks inside the variables, disjoint,
   above the fresh ranges, in no parameter), `model-recipe-relation` (translation),
   and the template semantics articles (`*-semantics.md`, through `Build.Facts.rel_iff`).
   New:
   * `Formula.InScope φ p v`: the compiler chapter's `Translation.ScopedIn φ p v` (callees
     well formed, blocks pairwise disjoint, at or above `p`, avoided by every parameter
     polynomial and atom; variables below `v`; `p ≤ v`) plus `w + m ≤ v` for every block.
   * `ExPoly.WitnessScope τ := ∃ φ, τ.poly = φ.compile ∧ φ.InScope τ.params τ.varCount`, with
     `ExPoly.WitnessScope.wf` and `ExPoly.WitnessScope.rel_iff` (the relation through the
     private blocks).
   * Templates: `Build.Facts.inScope`, `Build.Facts.witnessScope`,
     `Build.template_witnessScope_of_blocks_eq_nil` (call-free templates), the six call-free
     templates (`memberTemplate_witnessScope`, `rawAddTemplate_witnessScope`,
     `rawZTemplate_witnessScope`, `rawInverseXTemplate_witnessScope`,
     `log25Template_witnessScope`, `poleTemplate_witnessScope`) and
     `templateLibrary_witnessScope` (all 23 templates), `templateLibrary_getEx_witnessScope`.
   * Composition recipes: `CompositionRecipe.callBlocks`, `CompositionRecipe.inScope_of`,
     `CompositionRecipe.witnessScope_of` (hypotheses of
     `Assembly.compositionRecipe_rel_iff`). **Disjointness of the private blocks of the five
     composition recipes of the specification**, for every template library and recipe list
     with the right witness counts (the hypotheses of `Assembly.close_rel_iff`, …):
     `closeRecipe_callBlocks_disjoint`, `mainRecipe_callBlocks_disjoint`,
     `valueUnionRecipe_callBlocks_disjoint`, `valueRecipe_callBlocks_disjoint`,
     `integersRecipe_callBlocks_disjoint`; and their witness scope
     `closeRecipe_witnessScope`, `mainRecipe_witnessScope`, `valueUnionRecipe_witnessScope`,
     `valueRecipe_witnessScope`, `integersRecipe_witnessScope`.
   * Translation: `translate_blocks_end_le`, `translate_witnessScope`,
     `translate_witnessScope_library`, `ModelRecipe.witnessScope_of`.
   * Specification: `specLib_witnessScope_0`, …, `specLib_witnessScope_6`,
     `specLib_witnessScope` (hypotheses: the precision circuit is well formed, its nontrivial
     constants are in `integerConstants c₃`), and `specLib_precisionCircuit_witnessScope`
     (for `Compiler.Universal.precisionCircuit` and `c₃`: every template and every recipe is in
     scope, no hypothesis), with `precisionCircuit_consts_mem_integerConstants`.

## Statement corrections

* **No node encoding.** The node-encoding paragraph of formula-compilation, and in
  builder-soundness the clauses "every node refers only to earlier nodes, every call node
  names a template defined earlier, every variable node has index below $v$", have no Lean
  counterpart: a call atom carries the callee polynomial itself, and the polynomial is the
  compiled formula. The last clause becomes "every variable of the polynomial lies below
  $v$" (well-formedness).
* **Call atoms.** Lean formulas have a separate call atom $\langle\tau[g;w]\rangle$ (compiled
  to the call polynomial) besides $\langle f\rangle$, so that blocks can be tracked.
* **Generic statements about constructions.** `Build` is a shallow embedding: a program can in
  principle do anything with its state, and a construction may use a call atom twice in its
  final formula (for example in two branches of a disjunction), in which case the list of
  blocks of the final formula is not pairwise disjoint. Hence (a) builder-soundness holds for
  constructions that allocate (`Build.Allocates`), which every construction built from the
  primitives does; (b) the disjointness of blocks is a property of each template (checked by
  `decide` on its concrete list of blocks, `Build.Facts`), not a theorem about all
  constructions; it is proved for every template of the library.
* **Item 2 of builder-well-formed** ("blocks and fresh variables are disjoint and cover
  $[p,v)$ exactly") is dropped: `Build` does not record fresh variables, and no consumer needs
  the covering. The exact variable counts are the counts of the template and recipe articles.
* **Item 3** is stated with the free polynomials of the formula: the parameter polynomials of
  all calls and the atoms $a\doteq b$, $\langle f\rangle$ avoid every block. Point references and
  generator constraints of model-evaluation recipes are among these.
* **Recipes.** For composition recipes the scope needs the arguments below a bound $B\ge p$
  and the starts at or above $B$ (true for the five recipes of the specification, with
  $B=51,11,6,6,6$); for the translation it needs a well-formed circuit and the library's
  witness counts.
* **rational constants.** `Build.rational` accepts any $q$; after sign normalization $q=1$ gives
  the polynomial $u$, otherwise a variable with equation $qX_c\doteq u$. The article's
  assumption $q\ge2$ is what makes $q\ne0$; `Build.Facts` checks $q\ne0$ per template.

## Replacement statement sections

### formula-compilation.md

> **Formulas.** A formula over $\mathbb Z[X_i:i\in\mathbb N]$ is built from atoms $a\doteq b$
> ($a,b$ polynomials), $\langle f\rangle$ ($f$ a polynomial) and call atoms
> $\langle\tau[g;w]\rangle$ ($\tau$ an existential polynomial with $p$ parameters and $m$
> witnesses, $g$ a $p$-tuple of polynomials, $w\in\mathbb N$ the witness start) by the
> connectives $\bigwedge(\varphi_1,\dots,\varphi_k)$ and $\bigvee(\varphi_1,\dots,\varphi_k)$, $k\ge0$.
> A formula holds at $x:\mathbb N\to\mathbb Q$ when its atoms are read as $a(x)=b(x)$, $f(x)=0$
> and $\tau[g;w](x)=0$ and the connectives as conjunction and disjunction (the empty
> conjunction is true, the empty disjunction false). Its compilation $\kappa$ is
> $$\kappa(a\doteq b)=a-b,\quad \kappa(\langle f\rangle)=f,\quad \kappa(\langle\tau[g;w]\rangle)=\tau[g;w],\quad
> \kappa\Bigl(\bigwedge_i\varphi_i\Bigr)=\sum_i\kappa(\varphi_i)^2,\quad
> \kappa\Bigl(\bigvee_i\varphi_i\Bigr)=\prod_i\kappa(\varphi_i),$$
> with empty sum $0$ and empty product $1$. A conjunction nested inside a conjunction is
> squared twice; no flattening takes place. The call atom $\langle\tau[g;w]\rangle$ owns the
> block $[w,w+m)$.
>
> **Template constructions.** A construction of a template with $p$ parameters keeps a
> counter $c$, initially $p$, and a list of global equations, initially empty; the
> parameters are $X_0,\dots,X_{p-1}$. It may:
>
> 1. take a fresh variable $X_c$ and increase $c$ by one;
> 2. call an existential polynomial $\tau$ with $m$ witnesses on parameter polynomials $g$:
>    this takes the block $X_c,\dots,X_{c+m-1}$, increases $c$ by $m$ and yields the call atom
>    $\langle\tau[g;c]\rangle$ (a block of length zero takes no variable);
> 3. request a rational constant $u/q$ (the pair $(u,q)$ normalized only by the sign of $q$):
>    an integer constant ($q=1$) is the polynomial $u$; otherwise the first request takes a
>    fresh variable $X_c$ and records the global equation $q\,X_c\doteq u$, and later requests
>    of the same normalized pair return the same variable.
>
> If the construction ends with formula $\varphi$, recorded global equations $E_1,\dots,E_r$
> (in order of creation) and counter $v$, the template has $p$ parameters, $v-p$ witnesses
> and polynomial
> $$\kappa\bigl(\textstyle\bigwedge(E_1,\dots,E_r,\varphi)\bigr)=\sum_{i=1}^r\kappa(E_i)^2+\kappa(\varphi)^2 .$$
> In particular a template without rational constants has polynomial $\kappa(\varphi)^2$.
>
> **Gadgets.** $\mathrm{NZ}(a)$ takes a fresh $w$ and is the atom $a\cdot w\doteq1$.
> $\mathrm{POS}(a)$ takes fresh $z_1,z_2,z_3,z_4$ and is the atom
> $a\,(z_1^2+z_2^2+z_3^2+z_4^2)\doteq1$.
>
> This is a definition. Every later template article describes its construction by listing
> its variables in allocation order and its formula; the order of the constructor's steps is
> the order in which the allocations occur.

Lean names: `ZInQ.Syntax.Formula`, `ZInQ.Syntax.Formula.compile`, `ZInQ.Syntax.Formula.Holds`,
`ZInQ.Syntax.Build`, `ZInQ.Syntax.Build.fresh`, `ZInQ.Syntax.Build.call`,
`ZInQ.Syntax.Build.rational`, `ZInQ.Syntax.globalEq`, `ZInQ.Syntax.Build.template`,
`ZInQ.Syntax.Build.fullFormula`, `ZInQ.Syntax.Build.template_eq`, `ZInQ.Syntax.Build.nz`,
`ZInQ.Syntax.Build.pos`.

### builder-soundness.md

> Call a construction *allocating* if, run from any counter and list of global equations, it
> never decreases the counter and only appends global equations $q\,X_c\doteq u$ whose
> variables $c$ are newly allocated (at least the initial and below the final counter), in
> increasing order. Every fresh variable, call, rational constant and gadget is allocating,
> and so is every construction composed of them.
>
> Let an allocating construction with $p$ parameters end with formula $\varphi$, global
> equations $E_1,\dots,E_r$ and counter $v$, and let $\tau$ be its template. Then $\tau$ has
> parameter count $p$ and variable count $v$,
> $$[\![\tau]\!]=\kappa\bigl(\textstyle\bigwedge(E_1,\dots,E_r,\varphi)\bigr),$$
> the variables $c_1<\dots<c_r$ of $E_1,\dots,E_r$ lie in $[p,v)$, and if every variable of
> $\kappa(\varphi)$ has index below $v$, so has every variable of $[\![\tau]\!]$.
>
> **Proof sketch.** The polynomial and the counts are the definition of the template.
> Allocation is closed under sequencing: the counter of the second step starts where the
> first ended, so the equations appended by the first step lie below every equation
> appended by the second. A fresh variable or call only advances the counter; a rational
> constant either returns a constant or a recorded variable, or records the equation for the
> variable $X_c$ it allocates. Run from $(p,[\,])$ this gives the ranges of the constant
> variables, and the polynomial of $E_i$ has the single variable $c_i<v$.

Lean names: `ZInQ.Syntax.Build.Allocates`, `ZInQ.Syntax.Build.Allocates.bind`,
`ZInQ.Syntax.Build.template_construction`.

### builder-well-formed.md

> Call an existential polynomial $\tau$ with $p$ parameters and $v$ variables *in scope* if
> $[\![\tau]\!]=\kappa(\varphi)$ for a formula $\varphi$ such that
>
> 1. every call atom of $\varphi$ with callee witness count $m$ and witness start $w$ satisfies
>    $p\le w$ and $w+m\le v$, and its callee has all its variables below its variable count;
> 2. the blocks $[w,w+m)$ of the call atoms are pairwise disjoint;
> 3. no variable of a block occurs in a parameter polynomial of any call atom or in any atom
>    $a\doteq b$ or $\langle f\rangle$ of $\varphi$;
> 4. every variable occurring in $\kappa(\varphi)$ has index below $v$.
>
> Then $\mathrm{Rel}_\tau(a)$ holds exactly when $\varphi^\ast$ holds at some assignment
> extending $a$, and every variable of $[\![\tau]\!]$ has index below $v$.
>
> Every template of the library is in scope (with $\varphi=\bigwedge(E_1,\dots,E_r,\varphi_0)$
> for its construction). A composition recipe is in scope when its call arguments lie below a
> bound $B\ge p$, its calls start at or above $B$, and its call blocks are pairwise disjoint;
> the five composition recipes of the specification satisfy this with
> $B=51$ (close), $11$ (main), $6$ (value_union, value, integers): their blocks are
> allocated one after another above the parameters and fresh ranges. The model-evaluation
> translation of a well-formed natural circuit is in scope. Hence every recipe of the
> specification is in scope.
>
> **Proof sketch.** For a template, the list of call blocks of its construction is computed
> from the counter and checked to be separated and above $p$; the parameter polynomials and
> atoms are checked to use only variables below $v$ outside the blocks; constant variables
> are allocated by the counter. A construction may use a call atom twice, so this check is
> made per template. For a composition recipe the arguments are parameters or fresh-range
> variables below $B$ and the blocks lie at or above $B$. For the translation every
> reference, generator variable and block is allocated by its counter. The relational form
> is the private-witness lemma.

Lean names: `ZInQ.Syntax.Formula.InScope`, `ZInQ.Syntax.ExPoly.WitnessScope`,
`ZInQ.Syntax.ExPoly.WitnessScope.rel_iff`, `ZInQ.Syntax.ExPoly.WitnessScope.wf`,
`ZInQ.Syntax.Build.Facts.witnessScope`, `ZInQ.Syntax.templateLibrary_witnessScope`,
`ZInQ.Syntax.CompositionRecipe.witnessScope_of`, `ZInQ.Syntax.closeRecipe_callBlocks_disjoint`,
`ZInQ.Syntax.mainRecipe_callBlocks_disjoint`, `ZInQ.Syntax.valueUnionRecipe_callBlocks_disjoint`,
`ZInQ.Syntax.valueRecipe_callBlocks_disjoint`, `ZInQ.Syntax.integersRecipe_callBlocks_disjoint`,
`ZInQ.Syntax.translate_witnessScope`, `ZInQ.Syntax.specLib_witnessScope`,
`ZInQ.Syntax.specLib_precisionCircuit_witnessScope`.

## Lemmas beyond the leaves

`Build.Allocates.*` (closure lemmas for every primitive), `Build.blocks_fullFormula`,
`Build.template_params`, `Build.Facts.varCount`, `Formula.callees_eq_nil_of_blocks_eq_nil`,
`Formula.inScope_of_blocks_eq_nil`, `Recipe.denote_varCount`, `translate_blocks_end_le`,
`precisionCircuit_consts_mem_integerConstants`.

## Problems

None open. The assembly chapter proves the block disjointness of the outer recipes inline in
`Assembly.close_rel_iff`, …; the new lemmas state the same facts once.

## Suggestions for the next agent

* `Assembly.close_rel_iff`, `main_rel_iff`, `valueUnion_rel_iff`, `value_rel_iff` could take
  the disjointness from `closeRecipe_callBlocks_disjoint`, … instead of re-proving it.
* `Build.Allocates` is proved for every primitive and closed under `bind`, but not yet stated
  for the individual library constructions (no consumer needs it: their counts and scope come
  from `Build.Facts`). A small tactic in the style of `wp_run` (apply `Allocates.bind`,
  `Allocates.pure`, the primitive lemmas, `Allocates.mapL`, unfold other heads, split on
  pattern matches of bound values) would give `Build.template_construction` for each of them.
* If a generic disjointness theorem is ever wanted, the construction language needs an
  ownership discipline (each call atom used once), for instance a linear `Build` interface;
  the per-template check is cheap and already covers the library.
