---
article_id: af_545fa47957fb9dc881e81597
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Redei.chi, ZInQ.RouteK.Redei.chiBit, ZInQ.RouteK.Redei.chiBit_mk0, ZInQ.RouteK.Redei.chiBit_mul, ZInQ.RouteK.Redei.chi_mk0
---

# The genus characters

Let $n\ge1$, $\mathrm{Cl}$ the class group of the ring of integers $\mathcal O$ of
$\mathbb Q(\sqrt{-n})$, and $q$ a prime dividing $n$. For each class $c\in\mathrm{Cl}$ fix a
nonzero ideal $I_c\in c$ with $q\nmid N(I_c)$; one exists by the choice of representatives prime to
$q$. If $n$ is squarefree, the *genus character* $\chi_q:\mathrm{Cl}\to\mathbb F_2$ is
$$\chi_q(c)=[N(I_c)/q];$$
if $n$ is not squarefree, $\chi_q=0$.

For squarefree $n$ the value does not depend on the choice: $\chi_q([I])=[N(I)/q]$ for every
nonzero ideal $I$ of $\mathcal O$ with $q\nmid N(I)$. And $\chi_q$ is a homomorphism,
$\chi_q(cd)=\chi_q(c)+\chi_q(d)$, because for representatives $I\in c$ and $J\in d$ prime to $q$,
$IJ\in cd$ is prime to $q$ and $[N(IJ)/q]=[N(I)/q]+[N(J)/q]$.

## Depends on

- [Every class has a representative of norm prime to $q$](coprime-representatives.md)
- [The norm residue bit depends only on the class](norm-bit-class-invariant.md)
- [Residue bits](../../route-k/residue-bits.md)

## Sources

- [Step 4: genus characters](../../../sources/redei-locators.md#step-4-genus-characters)
- [The chosen route](../../../sources/redei-locators.md#the-chosen-route)
