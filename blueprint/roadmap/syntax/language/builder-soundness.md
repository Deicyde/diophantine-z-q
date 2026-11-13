---
article_id: af_70d383dd7b7f4dcc6764ed10
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Syntax.Build.Allocates, ZInQ.Syntax.Build.Allocates.bind, ZInQ.Syntax.Build.template_construction
---

# Template construction from formulas

Call a construction *allocating* if, run from any counter and list of global equations, it
never decreases the counter and only appends global equations $q\,X_c\doteq u$ whose
variables $c$ are newly allocated (at least the initial and below the final counter), in
increasing order. Every fresh variable, call, rational constant and gadget is allocating,
and so is every construction composed of them.

Let an allocating construction with $p$ parameters end with formula $\varphi$, global
equations $E_1,\dots,E_r$ and counter $v$, and let $\tau$ be its template. Then $\tau$ has
parameter count $p$ and variable count $v$,
$$[\![\tau]\!]=\kappa\bigl(\textstyle\bigwedge(E_1,\dots,E_r,\varphi)\bigr),$$
the variables $c_1<\dots<c_r$ of $E_1,\dots,E_r$ lie in $[p,v)$, and if every variable of
$\kappa(\varphi)$ has index below $v$, so has every variable of $[\![\tau]\!]$.

**Proof sketch.** The polynomial and the counts are the definition of the template.
Allocation is closed under sequencing: the counter of the second step starts where the
first ended, so the equations appended by the first step lie below every equation
appended by the second. A fresh variable or call only advances the counter; a rational
constant either returns a constant or a recorded variable, or records the equation for the
variable $X_c$ it allocates. Run from $(p,[\,])$ this gives the ranges of the constant
variables, and the polynomial of $E_i$ has the single variable $c_i<v$.

## Depends on

- [Formulas and their polynomial compilation](formula-compilation.md)
- [Semantics of templates and recipes](../template-semantics.md)

## Sources

- [Section 10.4](../../../sources/syntax-locators.md#section-10-translation)
- [Appendix C.1](../../../sources/syntax-locators.md#appendix-c1-scalar-nodes)
