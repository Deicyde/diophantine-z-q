---
article_id: af_70d383dd7b7f4dcc6764ed10
declaration: theorem
origin: bridged
---

# Template construction from formulas

Let a template construction with $p$ parameters end with formula $\varphi$, global
equations $E_1,\dots,E_r$ and counter $v$, and let $\tau$ be the template whose node list is
its node encoding. Then $\tau$ has parameter count $p$ and variable count $v$, and
$$[\![\tau]\!]=\kappa\bigl(\textstyle\bigwedge(E_1,\dots,E_r,\varphi)\bigr).$$
Moreover every node of the encoding refers only to earlier nodes, every call node names a
template defined earlier, and every variable node has index below $v$.

**Proof sketch.** Induction over the construction steps with the invariant that every node
index handed out so far denotes the polynomial of the expression it was created for.
Creating a node appends it, so earlier denotations are unchanged; returning an existing
node happens only for a structurally equal node, whose denotation is the same. An atom
$a\doteq b$ is encoded as $a+(-1)b$, which denotes $a-b=\kappa(a\doteq b)$; a conjunction is
encoded as $\kappa(\varphi_1)\cdot\kappa(\varphi_1)+\dots$, a disjunction as a product, and a call
node denotes the call polynomial by definition. The final root is the encoding of
$\bigwedge(E_1,\dots,E_r,\varphi)$. Variable indices are below the counter because each
variable node is created for a parameter, a fresh variable or a rational constant already
allocated, and the counter only grows.

## Depends on

- [Formulas and their polynomial compilation](formula-compilation.md)
- [Semantics of templates and recipes](../template-semantics.md)

## Sources

- [Section 10.4](../../../sources/syntax-locators.md#section-10-translation)
- [Appendix C.1](../../../sources/syntax-locators.md#appendix-c1-scalar-nodes)
