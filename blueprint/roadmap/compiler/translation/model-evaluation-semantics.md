---
article_id: af_a48917532060f169c6a957e0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Translation.translate_rel_iff_zero, ZInQ.Translation.translate_rel_iff_value
---

# Semantics of the model-evaluation translation

Assume the multiplication statement M in its all-input form.
Let $\mathcal N$ be a natural circuit with $k$ inputs that is well-formed with some bound, with
power template $\mathcal P$ and a well-formed power recipe $\pi$ satisfying (PV) if it has call
nodes, and let $\rho$ be its translation, with a table of nontrivial constants that is a prefix of
$(4,2,3,c_3,1399)$ containing the constants of $\mathcal N$.

1. *Zero mode, natural inputs.* For all $E_0,\dots,E_{k-1}\in\mathbb Q^5$,
   $$\mathrm{Rel}_\rho(E_0,\dots,E_{k-1})\iff\exists\,\theta\ \text{admissible for }\mathcal N\text{ with }
   \theta_0,\dots,\theta_{k-1}\in\mathbb N,\ E_i=\iota(\theta_i)\ (i<k)\ \text{and}\ \mathcal N(\theta)=0 .$$
2. *Value mode, unconstrained inputs.* For all $c_0,\dots,c_{k-1}\in\mathbb Z$ and $r\in\mathbb Q^5$,
   $$\mathrm{Rel}_\rho(\iota(c_0),\dots,\iota(c_{k-1}),r)\iff\exists\,\theta\ \text{admissible for }\mathcal N\text{ with }
   \theta_i=c_i\ (i<k)\ \text{and}\ r=\iota(\mathcal N(\theta)) .$$

In the first case the input points need not be assumed to be codes: the natural calls on the
inputs type them. In the second case nothing is claimed for non-canonical inputs.

**Proof sketch.** By the relational form, $\mathrm{Rel}_\rho$ is the existence of $x$ with the
prescribed parameters satisfying conditions 1-5. ($\Rightarrow$) The soundness statement
applies (in case 1 the inputs carry natural constraints; in case 2 they are canonical by
assumption) and gives $\theta$; the root equality yields $\mathcal N(\theta)=0$, respectively
$r=\iota(\mathcal N(\theta))$. ($\Leftarrow$) The completeness statement gives $x$.

## Depends on

- [Values and polynomial of a natural circuit](natural-circuit-values.md)
- [Well-formed natural circuits](natural-circuit-well-formed.md)
- [Every node point is the code of the node's value](translation-soundness.md)
- [Translation of a natural circuit into a model-evaluation recipe](../../syntax/recipes/model-evaluation-translation.md)
- [Correctness of the multiplication template](../../multiplication/multiplication-template.md)

## Proof depends on

- [Relational form of a model-evaluation recipe](model-recipe-relation.md)
- [Natural solutions give rational witnesses](translation-completeness.md)

## Sources

- [Section 10.4](../../../sources/compiler-translation-locators.md#section-104-typing-order)
- [Section 10.4 primitive formulas](../../../sources/compiler-translation-locators.md#section-104-primitive-formulas)
- [Appendix C.2](../../../sources/compiler-translation-locators.md#appendix-c2-model-recipes)
