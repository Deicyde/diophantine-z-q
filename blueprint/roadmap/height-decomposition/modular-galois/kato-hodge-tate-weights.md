---
article_id: af_fd7881203a8c2c39e35944be
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves70.modularHTCoeff
---

# Hodge–Tate weights of the representation of a newform

The *Hodge–Tate weight statement* is the following assertion. Let $\ell$ be a prime,
$\iota_{\mathbb C}:\overline{\mathbb Q}\to\mathbb C$ and
$\iota_\ell:\overline{\mathbb Q}\to\overline{\mathbb Q}_\ell$ embeddings, and $f$ a newform of
weight $k\ge2$ and level $N$; $\ell$ may divide $N$. Then there are a finite extension $E$ of
$\mathbb Q_\ell$ inside $\overline{\mathbb Q}_\ell$ and a continuous representation
$\rho:G_{\mathbb Q}\to\mathrm{GL}_2(E)$, unramified at every prime $p\nmid N\ell$, for which one of
the following holds, where $V=E^2$ with $\rho$ restricted to $G_{\mathbb Q_\ell}$, and
$\mathbb C_\ell(w)$ is $\mathbb C_\ell$ with $\sigma$ acting as $\chi_\ell(\sigma)^w\sigma$ for the
cyclotomic character $\chi_\ell$: every arithmetic Frobenius at every prime $p\nmid N\ell$ has trace
$\iota_\ell\iota_{\mathbb C}^{-1}(a_p(f))$, and
$\dim_E(V\otimes_{\mathbb Q_\ell}\mathbb C_\ell(-w))^{G_{\mathbb Q_\ell}}$ is $1$ for
$w\in\{0,k-1\}$ and $0$ for every other integer $w$, that is, the Hodge–Tate weights are $0$ and
$k-1$ in the convention in which the cyclotomic character has weight $+1$; or every geometric
Frobenius at every such prime has trace $\iota_\ell\iota_{\mathbb C}^{-1}(a_p(f))$, and the same
holds with $\mathbb C_\ell(w)$ in place of $\mathbb C_\ell(-w)$, that is, the Hodge–Tate weights are
$0$ and $k-1$ in the convention in which the cyclotomic character has weight $-1$.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. The two alternatives are the two normalizations in
which the literature states the theorem. The representation is Deligne's and its Hodge–Tate weights
are due to Faltings, Saito and Kato; Kato constructs it over the completion of the coefficient
field, at every level. Gee's survey states the existence of the representations attached to regular
algebraic cuspidal automorphic representations as a fact, with geometric Frobenius and the
cyclotomic character of weight $-1$; reaching the statement from it takes the passage from a newform
to its automorphic representation and from de Rham to Hodge–Tate, and a matching of coefficients and
embeddings. The statement asks for the traces only. The project's earlier form, over
$\overline{\mathbb Q}_\ell$, is proved here from this one. A review of this statement is pending,
and no print of the existence form for newforms has been read. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Kato Hodge-Tate weights](../../../sources/height-decomposition-locators.md#kato-hodge-tate-weights)
