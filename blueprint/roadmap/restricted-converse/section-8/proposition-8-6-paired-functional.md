---
article_id: af_8c222c641f587ec6b38a1557
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Contrib.CloudB3RC53.PairedFunctional.pairedFunctionalSelmer_proof, ZInQ.Contrib.CloudB3RC53.PairedFunctional.PairedFunctionalSelmer, ZInQ.Contrib.CloudB3RC53.PairedFunctional.pairedFunctionalHeightOne_proof, ZInQ.Contrib.CloudB3RC53.PairedFunctional.PairedFunctionalHeightOne
---

# Proposition 8.6: the paired functional and its integral representatives

Assume, over a commutative ring $S$, Selmer complexes $C_U$ and $C_{U'}$ as cones of a global
restriction against local conditions, and a change of local conditions $f:U'\to U$ inducing the
comparison $j:C_{U'}\to C_U$. Assume that the cone of $f$ is homotopy equivalent to a finite direct sum of
shifted tame local models (4.4), each with its Frobenius operators $A,D$ units or its inertia operator
$C$ a unit (ELLIOT: the local computation at the active and moving places), and that the components of
the retained duality satisfy their Leibniz rules (GLUE, the kind the docstring gives the statement).

Let $z$ be a degree-one cocycle and $c$ the conjugate transport into $C_U$. Then there is a homotopy
equivalence with forward map $j$ and inverse $j^{-1}$ over $S$ itself such that:

1. $z^\perp=j^{-1}c(z)$ is a cocycle and $j(z^\perp)-c(z)$ is a boundary;
2. the functional $\lambda_z=\operatorname{PD}(-,z^\perp)$ is closed;
3. any other homotopy inverse changes $\lambda_z$ by a coboundary.

The representative is integral over $S$, so the exponent of the manuscript is $a=0$, as its proof
notes.

The manuscript states this for the retained inner-limit diagrams over $\mathscr O[G]$ and, for the
primitive scalar constituent, at every height-one prime $\mathfrak p\ne(2)$ of $\Lambda$; the Lean
statement is algebraic, over any $S$ and abstract complexes, so each localization is an instance in
which its cone hypothesis must be supplied. The genuine Galois Selmer complexes and the inner limit do
not enter. The height-one clause has its own theorem, `pairedFunctionalHeightOne_proof`: the same
conclusions over $\Lambda_{\mathfrak p}$ at every height-one prime $\mathfrak p\ne(2)$, for a cone homotopy
equivalent to a sum of base changes of tame local models at the places of the primitive constituent.

The reduction of Theorem 5.3 does not use `pairedFunctionalSelmer_proof`: the field `PostLeaves.base_zero`
of [the remaining hypotheses](../remaining-hypotheses.md) supplies the pairing, the chain map and the
cocycle, and the functional $\operatorname{PD}(-,\psi(cz))$ is proved closed directly (`baseLam_closed`)
for [Lemma 8.11](lemma-8-11-base-zero.md). It reaches `pairedFunctionalHeightOne_proof`: in
`rcSteps_of_leaves`, `primRegularityInputs_of_HPK` turns the field `PostLeaves.prim_regular` into
regularity inputs, which `heightOneTarget_of_inputs` consumes (for `RCSteps.height_one` and again inside
`baseZeroTarget_of_LF`), and their terminal step is `regularAtPrime_of_terminalPairedFunctional`, which
applies the theorem. At the level of terms this is a round trip: `primRegularityInputs_of_HPK` builds
those inputs from $u_{\rm prim}\in\Lambda[1/2]$, through `primRegularityInputs_iff`, and the theorem
recovers the same membership.

**Proof sketch.** Each tame local model is contractible: by $h^1(v,w)=A^{-1}v$, $h^2(u)=(0,D^{-1}u)$ when
$A,D$ are units, and by $h^1(v,w)=C^{-1}w$, $h^2(u)=(-C^{-1}u,0)$ when $C$ is, using $DC=CA$. A finite
sum of contractible complexes is contractible, so the cone of $f$ is, and the induced map $j$ of Selmer
cones is a homotopy equivalence over $S$. Then $z^\perp$ is a cocycle because $j^{-1}$ is a chain map,
$j(z^\perp)-c(z)$ is a boundary by the homotopy $jj^{-1}\simeq1$, $\lambda_z$ is closed by the Leibniz
rule, and two homotopy inverses differ by a homotopy, which changes $\lambda_z$ by a coboundary.

## Depends on

- [Section 8: actual classes, local conditions and central comparison](README.md)

## Sources

- [Section 8](../../../sources/manuscript.md#section-8)
