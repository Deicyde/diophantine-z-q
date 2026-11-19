---
article_id: af_664cfda47ff5d8f46cbb7512
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenAddedLeaves28.scholzeH1AbVar
---

# Scholze's comparison theorem for H¹ of an abelian variety

The *Scholze statement* is the following assertion. Let $F$ be a finite extension of $\mathbb Q_p$,
$A$ an abelian variety of dimension $g$ over $F$, and
$W=\mathbb Q_p\otimes_{\mathbb Z_p}H^1(A_{\overline F},\mathbb Z_p)$, where
$H^1(A_{\overline F},\mathbb Z_p)$ is the first pro-étale cohomology group of
$A_{\overline F}=A\times_F\overline F$ with coefficients in $\mathbb Z_p$, on which $G_F$ acts
through its action on $\overline F$. Let $G_F$ act on $B_{\rm dR}$ through the restriction map
$G_F\to G_{\mathbb Q_p}$ along an embedding of $\overline{\mathbb Q}_p$ in $\overline F$, put
$D_{\rm dR}=(B_{\rm dR}\otimes_{\mathbb Q_p}W)^{G_F}$, and for $j\ge0$ let
$\mathrm{Fil}^jD_{\rm dR}=D_{\rm dR}\cap(\mathfrak m^j\otimes_{\mathbb Q_p}W)$, where $\mathfrak m$
is the maximal ideal of $B_{\rm dR}^+$ and $\mathfrak m^0=B_{\rm dR}^+$. Then $W$ is
finite-dimensional over $\mathbb Q_p$ and de Rham, that is,
$\dim_{\mathbb Q_p}D_{\rm dR}=[F:\mathbb Q_p]\dim_{\mathbb Q_p}W$; the filtration has its jumps in
$\{0,1\}$, that is, $\mathrm{Fil}^0D_{\rm dR}=D_{\rm dR}$ and $\mathrm{Fil}^2D_{\rm dR}=0$; and
$\dim_{\mathbb Q_p}\mathrm{Fil}^1D_{\rm dR}=[F:\mathbb Q_p]\,g$.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. Scholze's Corollary 1.8 is about a proper smooth
rigid-analytic variety over a complete discretely valued extension of $\mathbb Q_p$ with perfect
residue field: its étale cohomology with coefficients $\mathbb Q_p$ is de Rham, with associated
filtered vector space its de Rham cohomology. The manuscript applies it to the analytification of
$A$ and returns to algebraic cohomology through his Theorems 9.1 and 9.3. The statement is made on
the étale side: under the filtered isomorphism $D_{\rm dR}\cong H^1_{\rm dR}(A/F)$ its last two
clauses say that the Hodge filtration of $H^1_{\rm dR}(A/F)$ has its jumps in $\{0,1\}$ and that
$\mathrm{Fil}^1H^1_{\rm dR}(A/F)=H^0(A,\Omega^1_A)$ has dimension $g$ over $F$. The manuscript's
lemma is about abelian surfaces, whose Hodge numbers $2,2$ it states without a citation; the
statement is for abelian varieties of every dimension. The cohomology here is pro-étale; its
agreement with the classical $p$-adic étale cohomology, the inverse limit of the groups with
coefficients $\mathbb Z/p^n$, is a further step not proved here. It is a hypothesis, not proved
here.

## Depends on

None.

## Sources

- [Scholze comparison](../../../sources/height-decomposition-locators.md#scholze-comparison)
