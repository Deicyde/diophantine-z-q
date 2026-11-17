---
article_id: af_31d43031b0df878483ebd899
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves40.panPrintedP
---

# Pan's Fontaine–Mazur theorem

The *Fontaine–Mazur statement* is the following assertion. Let $p\ge5$ be a prime and
$\rho:G_{\mathbb Q}\to\mathrm{GL}_2(\overline{\mathbb Q}_p)$ a continuous representation that is
irreducible, unramified outside finitely many primes, odd, and at $p$ potentially semistable with
distinct Hodge–Tate weights. Then $\rho$ comes from a cuspidal eigenform up to twist: there are a
cuspidal eigenform $g$, a continuous representation $\rho_g$ attached to $g$ (it is unramified, with
the trace of a geometric Frobenius equal to the Hecke eigenvalue of $g$, at almost every prime), a
continuous character $\psi$ of $G_{\mathbb Q}$ and a matrix $P$ such that
$\rho=\psi\cdot P\rho_gP^{-1}$.

The project classes it as a published statement; its reading against the print is still pending.
It is Theorem 1.0.4 of Pan (2022), taken for $p\ge5$; the print also covers $p=3$ under a further
condition. "Potentially semistable" is Fontaine's admissibility over the ring $B_{\rm st}$, which
the project builds, following Berger, inside the ring $B_{\rm dR}$ of Mathlib. The proof shows that
its representation is de Rham and passes to this statement through
[Berger's theorem](berger-de-rham-potentially-semistable.md). It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Pan and Berger](../../../sources/height-decomposition-locators.md#pan-and-berger)
