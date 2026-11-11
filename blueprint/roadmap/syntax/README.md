---
article_id: af_b308239de19c9c5310e8dca8
---

# The finite specification of the polynomial

The target polynomial $P_*$ is defined by construction. It is a finite composition of
existential polynomial gadgets: a *template* is a polynomial in parameter and witness
variables, a *call* substitutes parameter polynomials and moves the callee's witnesses into
a fresh private block of the caller, a sum of squares expresses conjunction over $\mathbb Q$,
and a product expresses disjunction. A few astronomically large integers and finite
polynomials enter through three constructors whose values are never expanded. This
chapter defines the expression language and its semantics, proves the semantic lemmas that
make the gadgets behave as intended, defines every template, recipe, constant and
constructor of the manuscript's specification exactly, and defines $P_*$ with its witness
accounting. Whether each template expresses its intended relation is proved in the chapters
that use it; the inventory at the end says where.

## The expression language

Scalar nodes, templates, calls with witness blocks and recipes denote integer polynomials.

- [Semantics of templates and recipes](template-semantics.md)

Over $\mathbb Q$ a sum of squares vanishes exactly when every term does, and a product when
some factor does. Inverses are equations $uv=1$, and pairs of rationals represent the
arithmetic of $K_0=\mathbb Q(\sqrt2)$ faithfully.

- [Sums of squares and products over the rationals](sum-of-squares-semantics.md)
- [Inverse witnesses](nonzero-gadgets.md)
- [Pair arithmetic represents the quadratic field](field-pair-arithmetic.md)

Formulas, the template constructions that compile them, the scope of private witness
blocks, rational constants, positivity, absolute value and point references are developed
in their own section.

- [Formulas, gadgets and witness scope](language/README.md)

## Fixed constants and division polynomials

The fixed integer constants, the prime catalogue, the least formal multiple and the
false-triple product form one section.

- [Fixed constants and the guard product](constants/README.md)

The constructor `psi_component` inserts one coordinate of a normalized division
polynomial. The normalized recurrences agree with the classical division polynomials; the
classical multiplication-by-$n$ formulas, stated as a proposition, give the fixed-scalar
ordinate equation $2y([n]P)\psi_n(P)^4=\psi_{2n}(P)$, and with it the meaning of the
fixed-scalar templates on $2E(K_0)$.

- [Normalized division polynomials and their components](division-polynomials.md)
- [Agreement with the classical division polynomials](division-polynomials-classical.md)
- [The multiplication-by-n formulas](division-polynomial-multiplication.md)
- [Semantics of the fixed-scalar templates](fixed-scalar-semantics.md)

## The template library

The two basic elliptic templates express membership in $2E(K_0)$ and raw addition of
canonical codes.

- [The membership template](template-member.md)
- [The raw addition template](template-raw-add.md)

The remaining templates (local parameter, inverse abscissa, logarithm, pole, the
multiplication certificate, the guard, multiplication, natural codes and the value
templates) and the ordered library are in their own section.

- [The other templates](templates/README.md)

## Recipes and the specified polynomial

Natural circuits are translated into model-evaluation recipes, five composition recipes
assemble the root, and the witness counts are accounted for.

- [Recipes and witness accounting](recipes/README.md)

$P_*$ is the polynomial of the root recipe `integers`.

- [The specified polynomial](literal-polynomial.md)

## Inventory and correctness

| Template | Parameters | Witnesses | Correctness proved in |
| --- | ---: | ---: | --- |
| member | 5 | 7 | model chapter, membership (Section 3.1) |
| raw_add | 15 | 6 | model chapter, raw addition (Section 3.1) |
| raw_z | 7 | 1 | multiplication chapter (Section 6) |
| raw_inverse_x | 7 | 0 | multiplication chapter (Section 6) |
| log25 | 4 | 0 | multiplication chapter (Section 6) |
| pole | 1 | 11 | this chapter (pole-template semantics: the relation is $\Phi$); used with pole completeness |
| test_group | 44 | 162 | multiplication chapter (Section 6) |
| slope | 22 | 1,298 | multiplication chapter (Section 6) |
| height_certificate | 36 | 35,106 | multiplication chapter (Section 6) |
| multiply.scalar | 10 | 1 | this chapter (fixed-scalar semantics) |
| multiply.guard | 15 | 1 | this chapter (guard semantics) |
| multiply | 15 | 35,134 | multiplication chapter, input M |
| natural | 5 | 140,604 | this chapter (natural-code semantics, Section 3.1), from M and raw addition |
| value.signed_encode | 10 | 140,654 | assembly chapter (Sections 10-11) |
| value.abs | 2 | 4 | this chapter (absolute value by four squares, template corollary) |
| value.close_coordinates | 16 | 53 | assembly chapter (Section 11) |
| value.test | 11 | 35,282 | assembly chapter (Section 11) |
| value.exceptions | 6 | 406 | assembly chapter (Section 11) |
| scalar.integer_constant_0..4 | 10 | 1 | this chapter (fixed-scalar semantics) |

| Recipe | Kind | Parameters | Witnesses | Correctness proved in |
| --- | --- | ---: | ---: | --- |
| power_value | model evaluation | 20 | 17,786,698 | compiler chapter, rational translation |
| precision | model evaluation | 25 | 292,889,492,836 | compiler chapter, rational translation |
| close | sum of squares | 11 | 292,890,196,199 | assembly chapter |
| main | sum of squares | 6 | 292,890,231,486 | assembly chapter |
| value_union | product | 6 | 292,890,231,892 | assembly chapter |
| value | sum of squares | 6 | 292,890,231,899 | assembly chapter, ordinary-value relation |
| integers | sum of squares | 1 | 292,890,231,904 | this chapter (zero projection) and assembly |

## Cross-check against the saved specification

The manuscript ships its specification as a saved expression with the same 23 templates
and seven recipes. It is not an input to the proof; an external comparison checks that the
construction of this chapter reproduces it:

1. the fixed-constant expressions are compared as expression trees, and the two decimal
   literals with the primorial values;
2. each template is compared by parameter count, variable count and witness blocks
   exactly, and by its polynomial through a randomized identity test: both node lists are
   evaluated modulo a large prime at random points, with each constructor node replaced by
   a random function of its index expression and argument values, shared by both sides;
3. the recipes are compared record by record: generator indices, source variable rows,
   constant definitions, operations, root equality, composition calls and fresh ranges.

The comparison uses a small sample of points per template and never expands a
constructor.
