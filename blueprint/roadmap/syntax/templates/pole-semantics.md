---
article_id: af_f61d3432262486c8d9d44cac
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Syntax.poleTemplate_rel_iff
---

# Semantics of the pole template

For every $B\in\mathbb Q$,
$$\mathrm{Rel}_{\mathtt{pole}}(B)\iff\Phi(B),$$
where $\Phi(B)$ is the statement that the pole polynomial $Q_{\rm pole}$ of pole completeness
has a rational zero with input $B$: there are $b_0,\dots,b_5,e,z,r_1,r_2,w\in\mathbb Q$ with
$Q_{\rm pole}(B;b,e,z,r_1,r_2,w)=0$.

**Proof sketch.** The template polynomial is $(B\,S)^2$, where $B\,S$ is $Q_{\rm pole}$ written
with $B=X_0$, $b_i=X_{1+i}$, $e=X_7$, $z=X_8$, $r_1=X_9$, $r_2=X_{10}$, $w=X_{11}$; the compilation
$B\,S-0$ of the atom $B\,S\doteq0$ is the same polynomial. Evaluating at
$(B,y_0,\dots,y_{10})$ gives $Q_{\rm pole}(B;y)^2$, which vanishes exactly when
$Q_{\rm pole}(B;y)=0$. The eleven witnesses of the template are exactly the eleven witnesses of
$\Phi$, in the same order.

## Depends on

- [The pole template](template-pole.md)
- [Pole completeness](../../main/pole-completeness.md)
- [Semantics of templates and recipes](../template-semantics.md)

## Proof depends on

- [Template construction from formulas](../language/builder-soundness.md)

## Sources

- [Section 6](../../../sources/syntax-locators.md#section-6-multiplication-template)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
