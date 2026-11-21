---
article_id: af_bd374af12e6ae28ded882942
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.PoleS12.lemma54At_of_casselsTatePairing, ZInQ.Manuscript.PoleRC.Lemma54At
---

# Lemma 5.4 from the Cassels–Tate pairing

Assume the Cassels–Tate pairing on the curves $E_\ell:y^2=x(x-\ell)(x+3\ell)$. Let $\ell$ be a positive
squarefree integer with $\ell\equiv11\pmod{12}$. If the explicit 2-Selmer system of $E_\ell$ has eight
elements, that is dimension $3$, then $\operatorname{corank}_{\mathbb Z_2}\mathrm{Sel}_{2^\infty}(E_\ell/\mathbb Q)=1$.

The explicit 2-Selmer system is the set of pairs $(a,b)$ of squarefree integers whose class lies in the
local Kummer image of $E_\ell$ over $\mathbb R$ and over every $\mathbb Q_p$, in the coordinates
$(x+3\ell,x-\ell)$. The manuscript states Lemma 5.4 for every elliptic curve with full rational two-torsion;
the derivation uses it only at the curves $E_\ell$, which is what is proved here.

**Proof sketch.** $E_\ell$ has full rational two-torsion, with roots $0,\ell,-3\ell$, and $E_\ell(\mathbb Q)$
is finitely generated (both proved). The explicit system has as many elements as the cohomological
$\mathrm{Sel}_2(E_\ell/\mathbb Q)$ (the Kummer identification, proved). Write $r$ for the rank and
$Ш[2^\infty]\cong(\mathbb Q_2/\mathbb Z_2)^s\times F$ with $F$ finite. Then
$\dim\mathrm{Sel}_2=2+r+s+\dim F[2]$ and the corank is $r+s$. The alternating pairing is non-degenerate on
$F$, so $F[2]$ has square order and $\dim F[2]$ is even. Dimension $3$ leaves $r+s+\dim F[2]=1$, hence
$\dim F[2]=0$ and $r+s=1$.

## Depends on

- [The cited inputs: the Cassels–Tate pairing and Silverman's rank-one implication](cited-inputs.md)

## Sources

- [Lemma 5.4](../../sources/manuscript.md#lemma-54)
