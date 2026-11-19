---
article_id: af_01e9d0bac12cc3dd70538642
---

# p-adic Hodge theory

Let $p$ be a prime, $\overline{\mathbb Q}_p$ an algebraic closure of $\mathbb Q_p$, $\mathbb C_p$
its completion, and $G_K=\operatorname{Gal}(\overline{\mathbb Q}_p/K)$ for a finite extension $K$ of
$\mathbb Q_p$ inside $\overline{\mathbb Q}_p$. Let $\chi_p$ be the cyclotomic character and
$\mathbb C_p(w)$ the space $\mathbb C_p$ on which $\sigma$ acts as $\chi_p(\sigma)^w\sigma$.
Hodge–Tate weights are read off these twists, and the literature gives $\chi_p$ the weight $1$ or
$-1$; a statement that uses Hodge–Tate weights says which convention it takes. Let
$A_{\rm inf}=W(\mathcal O_{\mathbb C_p}^\flat)$, with Fontaine's map
$\theta:A_{\rm inf}\to\mathcal O_{\mathbb C_p}$; $B_{\rm dR}^+$ is the completion of
$A_{\rm inf}[1/p]$ along $\ker\theta$, and $B_{\rm dR}$ is $B_{\rm dR}^+$ with the generators of
$\ker\theta$ inverted. A representation $V$ of $G_K$ on a finite-dimensional $\mathbb Q_p$-vector
space is *de Rham* when
$\dim_{\mathbb Q_p}(B_{\rm dR}\otimes_{\mathbb Q_p}V)^{G_K}=[K:\mathbb Q_p]\dim_{\mathbb Q_p}V$, and
*potentially semistable* when
$\dim_{B_{\rm st}^{G_{K'}}}(B_{\rm st}\otimes_{\mathbb Q_p}V)^{G_{K'}}=\dim_{\mathbb Q_p}V$ for some
finite extension $K'$ of $K$ inside $\overline{\mathbb Q}_p$, where
$B_{\rm st}=B_{\rm cris}[\log[\tilde p]]$ is Fontaine's ring as Brinon and Conrad define it, taken
inside $B_{\rm dR}$ with $\log_p(p)=0$.

All four are consequences of published theorems; none is proved here.

- [Pan's Fontaine–Mazur theorem](pan-fontaine-mazur.md)
- [Berger's theorem: de Rham representations are potentially semistable](berger-de-rham-potentially-semistable.md)
- [Local algebraicity of Hodge–Tate characters](conrad-local-algebraicity.md)
- [Scholze's comparison theorem for H¹ of an abelian variety](scholze-de-rham-comparison.md)
