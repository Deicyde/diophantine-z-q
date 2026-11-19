---
declaration: theorem
origin: cited
---

# Finite free models and the inner limit

Let $A$ be an Artin local ring and let a complex of flat $A$-modules, such as the continuous cochains with
finite free coefficients used here, have finite bounded residual cohomology. It admits a bounded finite free
model with actual inclusion, projection and contraction homotopy, and every fixed finite diagram of maps and
homotopies, including the duality and local-condition data, transports to these models.

For one fixed active support and binary family, retain a tuple of models whose ranks are bounded over the
finite coefficient stages. One fixed nonprincipal ultrafilter then gives a diagram over $\Lambda$ at all
coefficient precisions, preserving its matrix identities and retained homotopy inverses. No rank bound
uniform over all active supports is asserted.

**Proof sketch.** Over an Artin local ring a flat module is free, and continuous finite-coefficient
cochains are filtered unions of finite free modules. Split the residual complex into cohomology and disks,
lift graded bases, and write $d=d_0+\epsilon$ with $\epsilon$ in the maximal ideal. With the normalized
contraction $(i_0,p_0,h_0)$ of $d_0$, the finite geometric series
$$d_C=p_0\epsilon(1+h_0\epsilon)^{-1}i_0,\quad i=(1+h_0\epsilon)^{-1}i_0,\quad p=p_0(1+\epsilon h_0)^{-1},\quad h=h_0(1+\epsilon h_0)^{-1}$$
give $pi=1$ and $1-ip=dh+hd$. Maps transport by $f\mapsto p'fi$, and the identity $1-ip=dh+hd$ transports
their compatibility homotopies. With bounded ranks fixed on a set in the ultrafilter, each finite tuple of
matrix entries has a limit at every precision; polynomial identities survive, and homotopy inverses remain
homotopy inverses.

## Depends on

None.

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:limits-inner-limit` (L4390–4451)

## Manuscript check

Mapped by AI review; the perturbation formulas are the standard ones. The proof that retained homotopy
inverses survive the ultrafilter limit is not yet checked line by line.
