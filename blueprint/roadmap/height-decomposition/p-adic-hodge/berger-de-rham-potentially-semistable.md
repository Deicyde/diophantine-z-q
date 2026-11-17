---
article_id: af_6b1091f7d1be24b3f05e830f
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves40.bergerPrintedV
---

# Berger's theorem: de Rham representations are potentially semistable

The *Berger statement* is the following assertion. Let $E$ be a finite extension of $\mathbb Q_p$
and $V$ a finite-dimensional $E$-vector space with a continuous linear action of $G_{\mathbb Q_p}$.
If $V$ is de Rham, that is,
$\dim_{\mathbb Q_p}(B_{\rm dR}\otimes_{\mathbb Q_p}V)^{G_{\mathbb Q_p}}=\dim_{\mathbb Q_p}V$, then
$V$ is potentially semistable: for some finite extension $K$ of $\mathbb Q_p$, the module
$(B_{\rm st}\otimes_{\mathbb Q_p}V)^{G_K}$ has dimension $\dim_{\mathbb Q_p}V$ over the field
$B_{\rm st}^{G_K}$.

The project classes it as a published statement; its reading against the print is still pending.
It is Théorème 0.7 of Berger (2002) over $\mathbb Q_p$. The ring $B_{\rm st}$ is Berger's
$B_{\max}[\log\tilde p]$, which the project builds inside the ring $B_{\rm dR}$ of Mathlib. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Pan and Berger](../../../sources/height-decomposition-locators.md#pan-and-berger)
