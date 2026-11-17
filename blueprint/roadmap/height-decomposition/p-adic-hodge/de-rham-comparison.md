---
article_id: af_b184071dea638b3476f739d5
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves40.deRhamVpAbVarPrinted
---

# The Tate module of an abelian variety is de Rham

The *de Rham statement* is the following assertion. Let $A$ be an abelian variety over a finite
extension $F$ of $\mathbb Q_p$. Then its rational Tate module $V_p(A)$ is de Rham:
$$\dim_{\mathbb Q_p}\bigl(B_{\rm dR}\otimes_{\mathbb Q_p}V_p(A)\bigr)^{G_F}
  =[F:\mathbb Q_p]\cdot\dim_{\mathbb Q_p}V_p(A).$$

The project classes it as a published statement; its reading against the print is still pending.
The literature attributes the theorem to Fontaine for abelian varieties, and Faltings and Tsuji give
it for the étale cohomology $H^1$, the dual of $V_p(A)$. The ring $B_{\rm dR}$ is the one in
Mathlib, with its Galois action; the dimension is counted over $\mathbb Q_p$. With the statement on
the [Galois invariants of $B_{\rm dR}$](bdr-galois-invariants.md), the project's earlier form, for
the dual of $V_p(A)$, is proved here from this one. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [de Rham comparison](../../../sources/height-decomposition-locators.md#de-rham-comparison)
