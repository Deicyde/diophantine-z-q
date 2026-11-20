---
article_id: af_70638693e5265599a45e25ae
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves73.carayolThmAFrob
---

# Carayol's theorem on the conductor

The *Carayol statement* is the following assertion. Let $f$ be a newform of weight $2$, level $N$
and character $\psi$, whose coefficient field $K_f$ is a number field, and $\lambda$ a place of
$K_f$ above a prime $\ell$. Then there is a continuous representation
$\rho:G_{\mathbb Q}\to\mathrm{GL}_2(K_{f,\lambda})$ on $V=K_{f,\lambda}^2$ that is irreducible over
$K_{f,\lambda}$; at every prime $p\nmid N\ell$ it is unramified, and every arithmetic Frobenius at
$p$ has trace $a_p(f)$ and determinant $p\,\psi(p)$, so characteristic polynomial
$X^2-a_p(f)X+p\,\psi(p)$; and at every prime $p\ne\ell$ the conductor exponent of its restriction to
a decomposition group, $\operatorname{codim}V^{I_p}+\int_0^\infty\operatorname{codim}V^{G_p^u}\,du$
in the upper numbering, equals $v_p(N)$.

It is a published statement: the printed theorem, or a direct instance of it that needs no argument.
Its reading against the print or its review is not complete, and until both are the project's strict
count does not count it as published. Darmon, Diamond and Taylor print the package as Theorem 3.1
(a)–(d) of their survey of Fermat's Last Theorem, with absolute irreducibility; an AI reading found
every clause printed there, the conductor as clause (d). The Frobenius clause is in the
normalization that the manuscript reads off Carayol's theorem, and oddness is proved here from the
determinant. Carayol's own statement, compatibility with the local Langlands correspondence, has no
Lean form; his §0.8 states the conductor only for newforms with rational coefficients on
$\Gamma_0(N)$. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Carayol conductor](../../../sources/height-decomposition-locators.md#carayol-conductor)
