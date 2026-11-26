---
article_id: af_ad3353ca27976f35b3a29b95
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.AppEK1.familyMap, ZInQ.Manuscript.RC.AppEK1.weightedMap, ZInQ.Manuscript.RC.AppEK1.weightedMap_invDeck, ZInQ.Manuscript.RC.AppEK1.specialize_familyMap, ZInQ.Manuscript.RC.AppEK1.weightedMap_fullWeight_single, ZInQ.Manuscript.RC.AppEK1.constituentWeight, ZInQ.Manuscript.RC.Even.coeffMap_equivariant
---

# (K10) and (E.2): the coefficient maps on group bases

Assume nothing: the Lean theorems take no named input.

Let $R$ be a commutative ring, $b:A\to B$ a homomorphism of groups and $\chi$ a character of $A$ with
values in $R^\times$. The *weighted map* $R[A]\to R[B]$ is the ring map with $[s]\mapsto\chi(s)[b(s)]$. For
$A=A_{F,n}=\operatorname{Gal}(\mathbb Q(\zeta_{F2^n})/\mathbb Q)$, the cyclotomic quotient $s\mapsto\bar s$
onto $\Gamma_n$, the homomorphism $\psi$ onto the binary group $G$ and the quadratic character $\chi_0$,
$$\Phi_n:[s]\longmapsto\chi_0(s)\,[\bar s]\,[\psi(s)]\in R[\Gamma_n\times G].\tag{K10}$$
If $\chi^2=1$, the weighted map satisfies $[g^{-1}]v\mapsto\chi(g)[b(g)]^{-1}\cdot(\text{image of }v)$ for every
$v\in R[A]$, so (K10) is equivariant for the inverse deck actions. Evaluating the $G$-coordinate at a
character $x$ of $G$ turns (K10) into the weighted map with weight $\chi_0\cdot(x\circ\psi)$, with no sign
projection. At a constituent of primitive conductor $2^ad$, on a level divisible by $2^a$ and $d$, the
weight $\chi_2\chi_{\rm odd}$ gives
$$[s]\longmapsto\chi_2(s)\,\chi_{\rm odd}(s)\,[s|_{\Gamma_n}],\qquad n\ge\max\{a,2\}.\tag{E.2}$$

In Lean these are maps of finite group rings over any coefficient ring, so they hold integrally and
modulo every power of two. Their application to Kato's classes after Shapiro's lemma is not
formalized: the comparison of Kato's classes with actual Galois cohomology is a named obligation with
no witness (`KatoFiniteComparison`).

**Proof sketch.** The weighted map is the lift of the multiplicative map $s\mapsto\chi(s)[b(s)]$. Composing
two weighted maps multiplies the weights, which gives the specialization; $\chi(g)^{-1}=\chi(g)$ gives the
equivariance.

In the Lean proof of Theorem 5.3 these theorems are not used: the coefficient maps live inside the
step `AppEFromKato` described in [the overview](README.md).

## Depends on

None.

## Sources

- [Appendix E](../../../sources/manuscript.md#appendix-e)
