---
article_id: af_0efd22e26263ea03e3b608a6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Contrib.CloudB3RC53.ClearingComplex.galoisFullSES_shortExact, ZInQ.Contrib.CloudB3RC53.ClearingComplex.galoisFullSES
---

# (5.6): the support triangle

There are no inputs beyond the data: a number field $K$, sets of places $S\subseteq S'$ whose difference
is the set of new places, a coefficient module unramified at the new places through given
factorizations, and local conditions at the old places.

At augmentation, where every graph prime is unramified, the old-support subcomplex, the complex with
full conditions at the new places $Q$ of the family, and the singular local blocks form a triangle
$$C_{\rm old}\to(C_b)_0\to\bigoplus_{q\in Q}Q_q\to C_{\rm old}[1].\tag{5.6}$$
Lean states the short exact sequence behind it, for continuous Galois cochains: the sequence
$0\to C(\mathrm{ur})\to C(\mathrm{full})\to\bigoplus_qQ_q\to0$ of Selmer complexes, with unramified or full
conditions at the new places and $Q_q$ the singular quotient at $q$, is short exact.

The manuscript uses the triangle at augmentation of the final family, with $C_{\rm old}$ an actual
subcomplex of an upper triangular model; the Lean sequence is stated for any such coefficient module
and set of new places, possibly empty.

The reduction of Theorem 5.3 does not use this theorem. The field `PostLeaves.clearing_model` of [the
remaining hypotheses](../remaining-hypotheses.md) models (5.6) through this sequence, but its docstring
records that the deduction uses none of the comparison fields that refer to it.

**Proof sketch.** Restriction from $G_{K_q}$ to $\mathrm{Gal}(K_q^{\rm ur}/K_q)$ is surjective, so
inflation of cochains along it is injective, and the quotient of the full condition by the unramified
one is the singular block.

## Depends on

None.

## Sources

- [Section 9](../../../sources/manuscript.md#section-9)
