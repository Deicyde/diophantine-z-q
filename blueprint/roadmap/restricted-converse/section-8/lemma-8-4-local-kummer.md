---
article_id: af_f45129f45de08502d192ab01
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.KummerMaps.compKummerAnnihilator_adicCompletion, ZInQ.Contrib.CloudB3RC53.Duality.kummerAnnihilatorNodeCharZero_of_print
---

# Lemma 8.4: the derived Kummer condition is its own annihilator

Assume Milne's local Tate duality for elliptic curves over $p$-adic fields
(`MilneLocalTateDualityKummerCharZero`, PRINT: the Tate pairing $B(F)\times H^1(F,B)\to\mathbb Q/\mathbb Z$
is nondegenerate in the $H^1$ variable on $H^1(F,B)[m]$ and the Kummer map is adjoint to
$H^1(F,B[m])\to H^1(F,B)$), a printed result that is not an input of the reduction of Theorem 5.3.

Let $K$ be a number field, $v$ a finite place, $B$ an elliptic curve over $K_v$ and $i\ge0$. A continuous
$1$-cocycle $y$ of $G_{K_v}$ with values in $B[2^i]$ is cohomologous to a Kummer cocycle $\kappa_P$,
$P\in B(K_v)$, if and only if for every $P$ the cup product $\kappa_P\cup y$ through the Weil pairing is
a coboundary in $\mu_{2^i}$. That is, the Kummer image is its exact annihilator for local duality.

The manuscript's lemma also describes the derived condition $B(F)^\wedge_2[-1]\to R\Gamma(F,T_2B)$ and
its reductions modulo $2^a$, gives integral isotropy homotopies, and identifies the scalar and binary
conditions at $2N$; the Lean statements are the annihilator clause only, for any elliptic curve over a
$p$-adic field. Here the isotropy is stated on cocycles: Kummer cocycles cup to coboundaries
(`compKummerIsotropic`). The chain-level step of the proof is proved separately, over abstract two-term
models, for the truncated local target that Nekovář's construction uses (`derivedKummerStep_trunc`);
this matches the target $\mathbb Z_2[-2]$ of the manuscript's restricted cup map. Into the untruncated
target the null-homotopy can fail when the condition has $2$-torsion (`pairEx_not_nullHomotopic`).

The Selmer complex as a cone (4.3), from the lemma's proof, is a definition in Lean: the Selmer data
`ZInQ.Manuscript.RC.SelmerComplex.selData` of the global restriction and the local conditions, whose
complex is Nekovář's up to a sign convention.

The reduction of Theorem 5.3 does not use this theorem.

**Proof sketch.** By Milne's duality the Kummer map is adjoint to $H^1(F,B[2^i])\to H^1(F,B)[2^i]$,
whose kernel is the Kummer image. Nondegeneracy of the Tate pairing on $H^1(F,B)[2^i]$ makes the Kummer
image exactly the classes orthogonal to it.

## Depends on

- [Section 8: actual classes, local conditions and central comparison](README.md)

## Sources

- [Section 8](../../../sources/manuscript.md#section-8)
