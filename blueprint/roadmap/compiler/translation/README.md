---
article_id: af_c8f84bf89012dbc5e6e05b65
---

# Translation to rational point codes

The natural precision polynomial speaks about natural numbers; the target polynomial has
rational witnesses. This chapter translates every natural-number constraint into rational
point-code constraints and proves that the translation is exact: natural variables become
codes typed by the natural-code predicate, additions become raw additions, multiplications
become multiplication templates, constants become fixed-scalar templates, power calls become
calls of the power-value recipe, and the root becomes one equality of codes. This page follows
Section 10.4; the interpreter, the lowering, the wrapper and the five-input specialization of
Section 10.3 are in [the natural chapter](../natural/README.md), whose equation (C.4) is the input
here.

Throughout, $\iota(n)$ is the code of $[n]P_0$, $\mathrm{Rel}_\tau$ is the rational relation of a
template or recipe, and the multiplication statement M is used in its all-input form:
$\mathrm{Rel}_{\mathtt{multiply}}(p,q,r)$ holds exactly when $p=\iota(a)$, $q=\iota(b)$ and $r=\iota(ab)$ for
some integers $a,b$. The multiplication chapter proves M from the six-contact estimate, pole
completeness and the twenty-two-prime pattern; the statements below assume M explicitly. The
Mordell–Weil theorem, used through the generator certificate, is proved by the two-isogeny
descent and is not a hypothesis.

## The typing order and the natural predicate

The typing order does not depend on the natural predicate. Membership forces a canonical code
in $D=2E(K_0)$, raw addition on two canonical inputs forces their canonical sum, the fixed
scalar templates give $[m]Q$ on $D$, and inside $\mathtt{multiply}$ the three root memberships are
forced conjuncts of the height certificate, so every raw addition of the certificate receives
canonical codes. Only once multiplication is typed on all rational inputs do the four square
products and three additions of $\mathtt{natural}$ make sense: its four untyped square roots are
typed by the multiplication calls before their squares are added, and Lagrange's theorem gives
exactly the codes of the natural numbers. This needs the completeness half of M. The outputs
of these additions are canonical by the raw-addition contract, so no separate membership of
the output is needed. The signed-encoding and exceptional templates of the assembly chapter
start their addition chains at such a natural code, at the literal origin or at the fixed
signed generator; the fixed generator equations are conjuncts outside the internal products
of the templates that use them, and an inactive product branch is never assumed true.

- [Lagrange's four-square theorem](lagrange-four-squares.md)
- [The natural-code predicate](natural-code-semantics.md)

## Natural circuits and their translation

A natural circuit has explicit variables, constant, variable, addition and multiplication
nodes, and call nodes that substitute the power template with a private block of
seventy-nine natural witnesses. Its value at an integer assignment is computed node by node;
a call contributes the value of the power template, which is not required to vanish.

- [Values and polynomial of a natural circuit](natural-circuit-values.md)
- [Well-formed natural circuits](natural-circuit-well-formed.md)

A model-evaluation recipe is a sum of squares of calls with pairwise disjoint private blocks,
so its rational relation unfolds into a conjunction of template relations on point
references, together with the generator equations and the root equality.

- [Relational form of a model-evaluation recipe](model-recipe-relation.md)

Induction along the source DAG gives every node point the code of the node's signed integer
value. Natural guards constrain only the explicit variables, never intermediate sums or
products; raw addition always receives canonical codes; globally typed multiplication types
the products; the generator equations and the scalar templates supply the constants. A power
call contributes the code of the power template's value at some private natural witnesses.
Conversely, a natural solution provides rational witnesses for every call.

- [Every node point is the code of the node's value](translation-soundness.md)
- [Natural solutions give rational witnesses](translation-completeness.md)
- [Semantics of the model-evaluation translation](model-evaluation-semantics.md)

## The power-value and precision recipes

The two translated circuits satisfy the scope conditions: no parent variable node reads a
private coordinate, the private blocks are disjoint, and every nontrivial constant is at least
two.

- [Scope conditions of the natural precision circuit](precision-circuit-scope.md)

The program literal $c_3$ is a constant of the precision recipe. Its digits are never
computed; the natural chapter bounds it by $1399<c_3<2^{2^{24}}$
([size of the program literal](../natural/universal/wrapper-code-size.md)), which gives the
scope condition $c_3\ge2$ here and the size chapter's literal bound.

The power-value recipe has three signed code inputs, seventy-nine private natural witnesses and
an output code for the value of the power-template polynomial.

- [Semantics of the power-value recipe](power-value-semantics.md)

The precision parent has $54056$ explicit variables and $15845$ disjoint private blocks;
replacing each block by its private power-value call preserves the existential assignment, and
only the final root is equated to the identity. This is input C on the rational side.

- [Semantics of the rational translation](rational-translation.md)

With equation (C.4), the precision recipe therefore holds at codes $\iota(c_0),\dots,\iota(c_4)$
exactly when the [precision relation](../natural/precision/precision-relation.md) accepts $c$;
the assembly chapter's relation Close uses it in this form.

At each primitive formula, equality is a difference, conjunction a sum of squares and
disjunction a product; the specification chapter proves that these compilations, including the
globally conjoined fixed equations, give equality of polynomial values under substitution
([Sums of squares and products over the rationals](../../syntax/sum-of-squares-semantics.md),
[Private witness blocks](../../syntax/language/existential-lifting.md)).
