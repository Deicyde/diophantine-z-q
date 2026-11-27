---
article_id: af_9cbd8ac61840fd40f7210907
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenAddedLeaves30.colmez1992DeRhamAbVar
---

# Colmez's p-adic periods of an abelian variety

The *period statement* is the following assertion. Let $F$ be a finite extension of $\mathbb Q_p$,
$\overline F$ an algebraic closure of $F$, $G_F=\operatorname{Gal}(\overline F/F)$, $A$ an abelian
variety over $F$, $T_pA=\varprojlim_nA(\overline F)[p^n]$ its Tate module and
$V_pA=\mathbb Q_p\otimes_{\mathbb Z_p}T_pA$, on which $G_F$ acts through its action on the points of
$A$, and let $G_F$ act on $B_{\rm dR}$ through the restriction map $G_F\to G_{\mathbb Q_p}$ along an
embedding of $\overline{\mathbb Q}_p$ in $\overline F$. Then there are a set $H$ and, for each
$\omega\in H$, a $\mathbb Q_p$-linear map $P_\omega:V_pA\to B_{\rm dR}$ with the following
properties: every value $P_\omega(u)$ lies in $B_{\rm dR}^+$;
$P_\omega(\sigma u)=\sigma\bigl(P_\omega(u)\bigr)$ for every $\sigma\in G_F$ and $u\in V_pA$; and if
$x\in B_{\rm dR}\otimes_{\mathbb Q_p}V_pA$ is sent to $0$ by the $B_{\rm dR}$-linear extension
$b\otimes u\mapsto b\,P_\omega(u)$ of every $P_\omega$, then $x=0$.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. It is Théorème 5.2 (i)–(ii) of Colmez with $H$ the de
Rham cohomology $H^1_{\rm dR}(A/F)$ and $P_\omega(u)=\int_u\omega$, the $p$-adic period of $\omega$
along $u$, extended $\mathbb Q_p$-linearly from $T_pA$ to $V_pA$. Of the printed theorem the
statement keeps three clauses: the periods lie in $B_{\rm dR}^+$, they commute with the action of
$G_F$, and the pairing is non-degenerate on the side of $T_pA$ once the scalars are extended to
$B_{\rm dR}$. The extension to $V_pA$ uses the linearity in $u$, which the readings take from
"bilinéaire" and from the proof on p. 640. The statement drops the identification of $H$ with de
Rham cohomology, the linearity in $\omega$, the compatibility with the filtrations, part (iii) and
the functoriality. Colmez works with a proper model of $A$ over the integers of $F$, which exists,
and the periods do not depend on it. He builds $T_pA$ from the points of $A$ over $\mathbb C_p$; on
$p$-power torsion these are the points over $\overline F$, since $A[p^n]$ is finite over $F$, and
this identification, compatible with the action of $G_F$, is proved here. Reading Colmez's points
over $\mathbb C_p$, which he takes through the proper model, as the points of $A$ is a step of the
reading. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Colmez Theorem 5.2](../../../sources/height-decomposition-locators.md#colmez-theorem-52)
