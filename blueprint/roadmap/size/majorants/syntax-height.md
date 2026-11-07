---
article_id: af_7a7cd7c7002dcafc8aa364b6
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Size.Maj, ZInQ.Size.nodeHeight, ZInQ.Size.nodeHeights, ZInQ.Size.templateHeight, ZInQ.Size.libraryHeights, ZInQ.Size.recipeHeight, ZInQ.Size.recipeHeights
---

# Syntax heights

**Nodes and templates.** For a template $\tau$ with node list $n_0,\dots,n_{k-1}$ in a library
whose calls refer to earlier templates, the height $h(n_j)\in\mathbb N$ is defined in node order:

- $h(\mathrm{var}\ i)=0$;
- $h(\mathrm{const}\ c)=1$ and $h(\mathrm{fixed}\ e)=1$;
- $h(\mathrm{add}\ j\ j')=h(\mathrm{mul}\ j\ j')=1+\max(h(n_j),h(n_{j'}))$;
- $h(\mathrm{psi}\ e\ (a_0,\dots,a_3)\ c)=1+\max_ih(n_{a_i})$ and
  $h(\mathrm{guard}\ e\ (a_1,\dots,a_{15}))=1+\max_ih(n_{a_i})$;
- $h(\mathrm{call}\ \tau'\ (a_0,\dots,a_{p-1})\ w)=1+H(\tau')+\max\bigl(0,\max_ih(n_{a_i})\bigr)$.

The intrinsic height of $\tau$ is $H(\tau)=h(n_{\mathrm{root}})$.

**Recipes.** For a model-evaluation recipe $\rho$ whose calls have callees $\kappa$ (the
natural, raw-addition, multiplication and fixed-scalar templates and the power recipe that
actually occur),
$$H(\rho)=\max\Bigl(4,\ \max_\kappa\bigl(H(\kappa)+3\bigr)\Bigr)+2 .$$
For a composition recipe with callees $\kappa_1,\dots,\kappa_k$,
$H(\rho)=\max_iH(\kappa_i)+2$ for a sum of squares and $H(\rho)=\max_iH(\kappa_i)+1$ for a
product.

**Majorant.** For an integer $B\ge2$, an integer polynomial $P$ satisfies the height-$h$
majorant, written $\mathrm{Maj}_B(h,P)$, if
$$\deg P\le1\text{ and }\|P\|_1\le1\quad(h=0),\qquad
\deg P\le B^{8h}\text{ and }\|P\|_1\le2^{B^{8h}}\quad(h\ge1).$$

This is a definition. The height is a majorant for the compact syntax, not the depth of an
expanded expression; it deliberately overestimates (shared nodes and unused nodes are
counted). For the model-evaluation wrappers the safe value four bounds the generator
equations and root differences, as in the manuscript, rather than the literal height two
of the companion proof.

## Depends on

- [Semantics of templates and recipes](../../syntax/template-semantics.md)
- [Coefficient norms and degrees](../norms/l1-norm.md)

## Sources

- [Section 12.1 syntax heights](../../../sources/size-locators.md#section-121-syntax-heights)
- [Companion size proof](../../../sources/size-locators.md#companion-size-proof)
- [Height traversal](../../../sources/size-locators.md#height-traversal)
