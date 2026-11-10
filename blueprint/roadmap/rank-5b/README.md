---
article_id: af_c38e410c645b4cd568ed5d2b
---

# The row-5b determinant

The certified rank hypothesis CR₃ rests, through Proposition 0, on the Selmer form CR₃^Sel:
for squarefree $n\equiv5\pmod8$ with $|\mathrm{Sel}_2(C_n)|=8$ and a Selmer class with
$|a|\equiv7\pmod8$, every 2-Selmer class of $C_n$ comes from a rational point. One published route
to CR₃^Sel goes through Tian, Yuan and Zhang, whose criterion for analytic rank one is a genus sum
$T_{5b}(n)$ of 4-ranks of class groups; row 5b of Smith's Table 2 writes that sum as the
determinant of an explicit matrix $M_{5b}$ in Legendre symbols. This chapter proves the
elementary step between the Selmer group and that determinant (tyz-5b §4): on a Selmer-minimal
curve, $\det M_{5b}$ is the parity of the number of primes $\equiv3\pmod4$ dividing the first
coordinate of a non-torsion Selmer class. So CR₃^Sel follows from CR₃^5b, the same hypothesis with
the 2-adic condition replaced by $\det M_{5b}=1$; CR₃^5b is a hypothesis, not proved here. The
identity $T_{5b}(n)=\det M_{5b}$ itself (tyz-5b §§2–3) is not formalized.

Throughout, $C_n$ is the congruent number curve $y^2=x^3-n^2x$, and the Selmer system and the
configuration of $n$ are those of the [Route K chapter](../route-k/README.md); the Selmer group is
that of the [Proposition 0 chapter](../selmer/README.md).

## The matrices

- [Smith's matrices $L$, $M_1$ and $M_{5b}$](smith-matrices.md)

## The Selmer group and the kernel of $M_1$

For product class $5$, the solutions of the Selmer system split into four torsion classes and a
subspace isomorphic to the kernel of $M_1$; through Proposition 0 this is a statement about
$\mathrm{Sel}_2(C_n)$.

- [The Selmer system of a class-5 configuration and the kernel of $M_1$](kernel-class-five.md)
- [The 2-Selmer group and the kernel of $M_1$ (Lemma 4.1)](lemma-4-1.md)

## The determinant

On a Selmer-minimal curve $M_1$ has corank one, and $M_{5b}$ is $M_1$ bordered by $(0,y)$.

- [The bordered determinant (Lemma 4.2)](lemma-4-2.md)
- [The rule of row 5b (Theorem 4.3)](theorem-4-3.md)
- [A first coordinate congruent to 7 forces $\det M_{5b}=1$ (Corollary 4.4)](corollary-4-4.md)
- [Two values of the row-5b determinant](cross-checks.md)

## The hypothesis in row-5b form

- [The certified rank hypothesis in row-5b form](certified-rank-5b.md)
- [CR₃^5b implies CR₃^Sel](certified-rank-sel-of-5b.md)
