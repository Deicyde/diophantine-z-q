---
article_id: af_31d43031b0df878483ebd899
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves73.panPrintedF
---

# Pan's Fontaine–Mazur theorem

The *Fontaine–Mazur statement* is the following assertion. Let $p\ge5$ be a prime,
$\iota_p:\overline{\mathbb Q}_p\to\mathbb C$ an isomorphism of fields, and
$\rho:G_{\mathbb Q}\to\mathrm{GL}_2(\overline{\mathbb Q}_p)$ a continuous representation that is
irreducible over $\overline{\mathbb Q}_p$, unramified outside finitely many primes and odd
($\det\rho(c)=-1$ for every complex conjugation $c$), and whose restriction to $G_{\mathbb Q_p}$ is
potentially semistable in the sense of Fontaine and Hodge–Tate with two distinct Hodge–Tate weights.
Then $\rho$ comes from a cuspidal eigenform up to twist: there are a nonzero cusp form $g$ of some
weight on some $\Gamma_1(N)$, on which the diamond operators act through a character, that is an
eigenvector of every Hecke operator $T_n$ with $n$ prime to $N$, with eigenvalues $\lambda_n(g)$; a
continuous representation $\rho_g:G_{\mathbb Q}\to\mathrm{GL}_2(\overline{\mathbb Q}_p)$ attached to
$g$ through $\iota_p$, in the sense that for all but finitely many primes $q\nmid N$ it is
unramified at $q$ and every geometric Frobenius at $q$ has trace $\iota_p^{-1}(\lambda_q(g))$; a
continuous character $\psi:G_{\mathbb Q}\to\overline{\mathbb Q}_p^\times$; and a matrix
$P\in\mathrm{GL}_2(\overline{\mathbb Q}_p)$ with $\rho=\psi\cdot P\rho_gP^{-1}$. Each of the two
local conditions is asked on some model $V=E^2$ of $\rho|_{G_{\mathbb Q_p}}$ over a finite extension
$E$ of $\mathbb Q_p$ inside $\overline{\mathbb Q}_p$. *Hodge–Tate with two distinct weights* means
that $\dim_E(V\otimes_{\mathbb Q_p}\mathbb C_p(w))^{G_{\mathbb Q_p}}$ is $1$ for two distinct
integers $w$ and $0$ for every other $w$, where $\mathbb C_p(w)$ is $\mathbb C_p$ with $\sigma$
acting as $\chi_p(\sigma)^w\sigma$ for the cyclotomic character $\chi_p$, so that $\chi_p$ has
Hodge–Tate weight $-1$. *Potentially semistable* means that for some finite extension $K$ of
$\mathbb Q_p$ inside $\overline{\mathbb Q}_p$,
$\dim_{B_{\rm st}^{G_K}}(B_{\rm st}\otimes_{\mathbb Q_p}V)^{G_K}=\dim_{\mathbb Q_p}V$, where
$B_{\rm st}=B_{\rm cris}[\log[\tilde p]]$ is Fontaine's ring inside $B_{\rm dR}$, with
$B_{\rm cris}=A_{\rm cris}[1/t]$ and $\log_p(p)=0$.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. It is Theorem 1.0.4 of Pan, whose hypotheses are those
of his Conjecture 1.0.1, taken for $p\ge5$; the print also covers $p=3$ under a further condition. A
review checked every clause against the arXiv version that the manuscript cites, with Pan's
conventions: geometric Frobenius, Hodge–Tate weight $-1$ for the cyclotomic character, and a fixed
$\iota_p$. Potential semistability is Brinon and Conrad's notion, semistability over a finite
extension with admissibility in the form of the equality of dimensions; that it does not depend on
the model of $\rho$ is proved here, and so is the same for the Hodge–Tate condition. The review
rates the statement a consequence because Brinon and Conrad define $B_{\rm st}$ abstractly: the
statement uses its image in $B_{\rm dR}$, which is isomorphic to it by the injectivity in their
Theorem 9.2.10, not proved here, and it uses their description of the image of $A_{\rm cris}$ in
$B_{\rm dR}^+$, which they print without proof. The conclusion asks only for the traces at almost
every prime, which is weaker than the printed modularity. Pan obtains Theorem 1.0.4 by combining his
results with work of Skinner–Wiles, Kisin and Hu–Tan. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Pan Theorem 1.0.4](../../../sources/height-decomposition-locators.md#pan-theorem-104)
