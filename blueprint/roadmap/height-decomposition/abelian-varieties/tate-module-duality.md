---
article_id: af_0c7347a32b40c0ee27f665db
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenAddedLeaves28.t10TateDuality
---

# The first ℓ-adic cohomology of an abelian variety is dual to its Tate module

The *duality statement for the Tate module* is the following assertion. Let $K$ be a field,
$\overline K$ an algebraic closure, $G_K=\operatorname{Aut}_K(\overline K)$, $A$ an abelian variety
over $K$, $A_{\overline K}=A\times_K\overline K$, and $\ell$ a prime different from the
characteristic of $K$. Let $H^1(A_{\overline K},\mathbb Z_\ell)$ be the first cohomology group of
the pro-étale site of $A_{\overline K}$ with coefficients in the sheaf
$U\mapsto C(U,\mathbb Z_\ell)$ of continuous $\mathbb Z_\ell$-valued functions, a
$\mathbb Z_\ell$-module on which $\sigma\in G_K$ acts by pull-back along the automorphism
$1\times\operatorname{Spec}\sigma$ of $A_{\overline K}$, and let $G_K$ act on the Tate module
$T_\ell A=\varprojlim_n A(\overline K)[\ell^n]$ through its action on the points of $A$. Then there
is an isomorphism of $\mathbb Z_\ell$-modules
$\phi:H^1(A_{\overline K},\mathbb Z_\ell)\to\operatorname{Hom}_{\mathbb Z_\ell}(T_\ell A,\mathbb Z_\ell)$
with $\phi(\sigma x)=\phi(x)\circ\sigma^{-1}$ for every $\sigma\in G_K$ and every $x$.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. Milne prints the isomorphism for an abelian variety
over a separably closed field, with the étale cohomology group $H^1(A_{\rm et},\mathbb Z_\ell)$, as
Theorem 12.1(a) with Remark 12.5, and records in that remark, without proof, that it is compatible
with the natural action of $\operatorname{Gal}(k^{\rm sep}/k)$ when $A$ is defined over $k$; the
statement applies this to $A_{\overline K}$. An AI reading of the notes found the statement a
consequence of these, not a direct instance, through two steps: the agreement of pro-étale
cohomology with coefficients $C(-,\mathbb Z_\ell)$ with étale $\ell$-adic cohomology, a comparison
theorem of Bhatt and Scholze, and the use of an algebraic closure in place of a separable closure,
which changes nothing in characteristic $0$ and in general follows from the topological invariance
of étale cohomology. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Milne Theorem 12.1](../../../sources/height-decomposition-locators.md#milne-theorem-121)
