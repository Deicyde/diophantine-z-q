---
article_id: af_5cdfffe9bd1cdcaab466803e
---

# Formulas, gadgets and witness scope

Templates are generated from formulas: equality is a difference, conjunction a sum of
squares, disjunction a product, and rational constants are fresh variables tied by global
equations. The node encoding of a constructed template denotes the compiled formula, and
every construction keeps its private blocks apart.

- [Formulas and their polynomial compilation](formula-compilation.md)
- [Template construction from formulas](builder-soundness.md)
- [Witness scope of constructed templates and recipes](builder-well-formed.md)

A call evaluates its callee at the parameter values and its private block. Disjoint
private blocks can be moved to the front, and the block of an inactive branch may take any
values.

- [Evaluation of a template call](call-semantics.md)
- [Private witness blocks](existential-lifting.md)

Rational constants are fresh variables with global equations, which stay active outside
every internal disjunction. Strict positivity and absolute value are expressed with four
squares.

- [Rational constants by global equations](rational-constants.md)
- [Strict positivity by four squares](positivity-gadget.md)
- [Absolute value by four squares](absolute-value-gadget.md)

Elements of $K_0$ are pairs of rationals and points of $E$ are five-coordinate codes; the
shared pair and point formulas are fixed once.

- [Quadratic-field pairs and point-code formulas](field-pair-gadgets.md)

Model-evaluation recipes refer to points by references; the references $-1,-2,-3$ are the
codes of $O$, $P_0$ and $-P_0$ once the generator constraints hold.

- [Point references](point-references.md)
- [Values of the point references](generator-references.md)
