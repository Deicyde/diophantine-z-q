---
article_id: af_0f101b9e91748e2bf42d0e17
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Translation.translate_rel_iff, ZInQ.Translation.modelRecipe_rel_iff
---

# Relational form of a model-evaluation recipe

Let $\rho$ be the model-evaluation recipe obtained by translating a natural circuit with $k$
inputs that is well-formed with some bound, in value or zero mode, with or without natural
constraints on the inputs and with an optional well-formed power recipe $\pi$ (present when the
circuit has call nodes), and let $p$ be its parameter count ($5k$ or $5(k+1)$). The table of
nontrivial constants of the translation is a prefix of $(4,2,3,c_3,1399)$ that contains the
constants of the circuit. Call
the variables of $\rho$ that are neither parameters nor in a private block of one of its calls
its *free witnesses*: the generator variables $g_0,g_1,g_2$, the fresh points of the explicit
witness variables and the fresh points of the constant, addition, multiplication and call
nodes. For $a\in\mathbb Q^p$, $\mathrm{Rel}_\rho(a)$ holds if and only if there is an
assignment $x:\mathbb N\to\mathbb Q$ with $x_i=a_i$ for $i<p$ such that:

1. $8x_{g_0}=1641$, $4x_{g_1}=-15465$, $32x_{g_2}=87483$;
2. $\mathrm{Rel}_{\mathtt{natural}}(\mathrm{ref}(r)(x))$ for every source-variable row $(i,r,s)$ with a
   natural start $s$;
3. $\mathrm{Rel}_{S_h}(\mathrm{ref}(-2)(x),\mathrm{ref}(r)(x))$ for every constant definition $(S_h,r,s)$;
4. $\mathrm{Add}_{\rm raw}(\mathrm{ref}(a)(x),\mathrm{ref}(b)(x),\mathrm{ref}(o)(x))$,
   $\mathrm{Rel}_{\mathtt{multiply}}(\mathrm{ref}(a)(x),\mathrm{ref}(b)(x),\mathrm{ref}(o)(x))$ and
   $\mathrm{Rel}_\pi(\mathrm{ref}(a)(x),\mathrm{ref}(b)(x),\mathrm{ref}(c)(x),\mathrm{ref}(o)(x))$ for the operations
   $(0,a,b,o,s)$, $(1,a,b,o,s)$ and $(2,a,b,c,o,s)$ respectively;
5. $\mathrm{ref}(r)(x)=\mathrm{ref}(r')(x)$ for the root equality $(r,r')$.

Under condition 1, $\mathrm{ref}(-1)(x)=\iota(0)$, $\mathrm{ref}(-2)(x)=\iota(1)$ and
$\mathrm{ref}(-3)(x)=\iota(-1)$. Only the values of $x$ at the parameters and the free witnesses
matter.

**Proof sketch.** $[\![\rho]\!]$ is the sum of the squares of its constraint polynomials, so it
vanishes at $x$ exactly when every constraint does. By the witness-scope theorem the
private blocks of the calls of $\rho$ are pairwise disjoint, disjoint from the parameters and
free witnesses, and no block variable occurs in a point reference or in another
constraint. Hence the existential over the witnesses of $\rho$ splits into an existential
over the free witnesses and, for each call, one over its own block; by the evaluation of a
call, the latter is the callee relation at the evaluated parameter points. The generator
constraints and root differences contain no block variable. The values of the three
negative references are the point-reference lemma.

## Depends on

- [Semantics of templates and recipes](../../syntax/template-semantics.md)
- [Translation of a natural circuit into a model-evaluation recipe](../../syntax/recipes/model-evaluation-translation.md)
- [Point references](../../syntax/language/point-references.md)
- [Point codes](../../model/point-codes.md)

## Proof depends on

- [Witness scope of constructed templates and recipes](../../syntax/language/builder-well-formed.md)
- [Evaluation of a template call](../../syntax/language/call-semantics.md)
- [Sums of squares and products over the rationals](../../syntax/sum-of-squares-semantics.md)
- [Values of the point references](../../syntax/language/generator-references.md)

## Sources

- [Appendix C.2](../../../sources/compiler-translation-locators.md#appendix-c2-model-recipes)
- [Section 10.4](../../../sources/compiler-translation-locators.md#section-104-primitive-formulas)
- [Translation artifacts](../../../sources/compiler-translation-locators.md#translation-artifacts)
