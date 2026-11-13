---
article_id: af_14de3402fad9780ec021699d
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Rank.CertifiedRankTYZClRk
---

# The class-number hypothesis in positive-rank form

The hypothesis CR₃^TYZ_Cl,Rk is the following assertion. Let $d$ be a squarefree positive integer
with $d\equiv5\pmod8$ whose genus sum of class numbers
$$T^{\mathrm{Cl}}_{5b}(d)=\sum_\pi\prod_{B\in\pi}\#\bigl(2\,\mathrm{Cl}(\mathbb Q(\sqrt{-d_B}))\bigr)\pmod 2$$
is $1$. Here $\pi$ runs over the set partitions of the primes of $d$ with exactly one block with
$d_B\equiv7$, exactly one with $d_B\equiv3$, and all other blocks with $d_B\equiv1\pmod8$; $d_B$ is
the product of the primes in $B$, and $2\,\mathrm{Cl}(K)$ is the subgroup of squares of the class
group of the ring of integers of $K$. Then $C_d(\mathbb Q)$ has a point of infinite order.

This is Tian–Yuan–Zhang with their own genus class numbers (Theorem 3.5, first assertion, with
Theorem 3.3, Proposition 3.2, Lemmas 2.8, 3.16, 3.18, 3.21 and Proposition 2.3), as completed by
Proposition N (nt-tyz §4; an unpublished argument written for this project, with two automated
reviews and no human review): if $T^{\mathrm{Cl}}_{5b}(d)$ is odd then their invariant
$\mathcal L(d)$ is nonzero, and since the root number is $-1$, $L(C_d,s)$ vanishes to order exactly
one at $s=1$; followed by Gross–Zagier over an auxiliary imaginary quadratic field
(Bump–Friedberg–Hoffstein), which gives $\operatorname{rank}C_d(\mathbb Q)\ge1$. No Rédei formula
and no condition on $\mathrm{Sel}_2(C_d)$ enter. It follows from three statements about
$L(C_d,s)$ and $L(E,s)$: Tian–Yuan–Zhang's row 5b, which rests on the unrefereed Proposition N,
the vanishing of $L(C_d,s)$ at $s=1$, and the Gross–Zagier statement
([Row 5b, vanishing at the centre and Gross–Zagier give CR₃^TYZ_Cl,Rk](literature/certified-rank-tyz-cl-rk-of-literature.md)).
The vanishing in turn follows from the textbook functional equation, with root number $-1$, on the strip
$0<\operatorname{Re}s<2$
([the functional equation gives vanishing at the centre](literature/root-number-vanishing-of-functional-equation.md)).
Those statements are themselves hypotheses, so CR₃^TYZ_Cl,Rk is not proved here.

## Depends on

- [The genus sum of class numbers](../redei/class-number-genus-sum.md)

## Sources

- [The positive-rank form](../../sources/rank-locators.md#the-positive-rank-form)
- [The trust statement for CR3](../../sources/route-k-locators.md#the-trust-statement-for-cr3)
- [Tian-Yuan-Zhang](../../sources/rank-locators.md#tian-yuan-zhang)
- [Gross-Zagier](../../sources/rank-locators.md#gross-zagier)
