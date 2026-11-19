---
article_id: af_7e950fc2887d029178474b25
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenAddedLeaves28.conradAppB
---

# Local algebraicity of Hodge–Tate characters

The *local algebraicity statement* is the following assertion. Let $E$ be a finite extension of
$\mathbb Q_p$ inside $\overline{\mathbb Q}_p$ and $\psi:G_{\mathbb Q_p}\to E^\times$ a continuous
character. Let $\chi$ be the $p$-adic cyclotomic character and
$\mathrm{Art}:\mathbb Q_p^\times\to G_{\mathbb Q_p}^{\rm ab}$ the local Artin map, normalized so
that uniformizers go to arithmetic Frobenius elements; thus $\chi(\mathrm{Art}(u))=u^{-1}$ for
$u\in\mathbb Z_p^\times$. Call $\psi$ *locally algebraic of exponent* $m\in\mathbb Z$ if there is
$k\ge0$ such that $\psi(\sigma)=u^m$ for every $u\in\mathbb Z_p^\times$ with $u\equiv1\pmod{p^k}$
and every $\sigma\in G_{\mathbb Q_p}$ whose image in $G_{\mathbb Q_p}^{\rm ab}$ is
$\mathrm{Art}(u)$. For $i\in\mathbb Z$ let $H_i(\psi)$ be the $\mathbb Q_p$-vector space of
$\mathbb Q_p$-linear maps $\phi:E\to\mathbb C_p$ with
$\phi(\psi(\sigma)x)=\chi(\sigma)^i\,\sigma(\phi(x))$ for all $\sigma\in G_{\mathbb Q_p}$ and
$x\in E$, and call the integer part of $\dim_{\mathbb Q_p}H_{-i}(\psi)/[E:\mathbb Q_p]$ the
multiplicity of $i$ as a Hodge–Tate weight of $\psi$ (the cyclotomic character has weight $-1$).
Then: (a) if some integer $w$ has multiplicity $1$ and every other integer has multiplicity $0$,
then $\psi$ is locally algebraic of some exponent; (b) if $\psi$ is locally algebraic of exponent
$-n$ for an integer $n$, then $\dim_{\mathbb Q_p}H_n(\psi)=[E:\mathbb Q_p]$.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. Part (a) is the direction "Hodge–Tate implies locally
algebraic" of the sentence after Conrad's Definition B.1, which he states for a finite extension $L$
of $\mathbb Q_p$ and credits to Tate through Serre's book, without proof; here $L=\mathbb Q_p$.
Reaching (a) from it takes two steps not proved here: multiplicity $1$ for $w$ gives
$\dim_{\mathbb Q_p}H_{-w}(\psi)\ge[E:\mathbb Q_p]$, which makes the underlying
$\mathbb Q_p$-representation Hodge–Tate by the inequality
$\sum_i\dim_{\mathbb Q_p}H_i(\psi)\le[E:\mathbb Q_p]$; and every homomorphism of tori
$\mathbb G_m\to R_{E/\mathbb Q_p}\mathbb G_m$ over $\mathbb Q_p$ is $x\mapsto x^n$. Part (b) is
Proposition B.3 at $L=\mathbb Q_p$, in Conrad's conventions: the arithmetic normalization, and the
cyclotomic character of weight $+1$. Proposition B.3 assumes $\psi$ Hodge–Tate, which for a locally
algebraic $\psi$ is the other direction of the same sentence; and passing from its conclusion,
$\mathbb C_p\otimes_{\mathbb Q_p}E\cong\mathbb C_p(n)^{[E:\mathbb Q_p]}$, to
$\dim_{\mathbb Q_p}H_n(\psi)=[E:\mathbb Q_p]$ takes linear algebra and the theorem of Ax, Sen and
Tate, which is proved here, while the passage itself is not. Conrad's appendix is in an unrefereed
author preprint, the version the manuscript cites; an AI reading of both pages found these
statements there. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Conrad Appendix B](../../../sources/height-decomposition-locators.md#conrad-appendix-b)
