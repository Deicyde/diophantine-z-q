---
article_id: af_f8c163ad59bd7bb4cae9e6d0
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.eight_le_card_quotient_two, ZInQ.RouteK.Rank.card_quotient_two_eq_card_ker, ZInQ.RouteK.Rank.nsmul_two_eq_zero_of_zmod_two, ZInQ.RouteK.Rank.finsupp_int_eq_zero_of_two_nsmul
---

# Counting $A/2A$

Let $A$ be a finitely generated abelian group whose $2$-torsion $A[2]$ has exactly $4$ elements
and which has an element of infinite order, and suppose that $A/2A$ is finite. Then $A/2A$ has at
least $8$ elements.

Along the way: for a finite abelian group $T$, $\#(T/2T)=\#T[2]$; $2z=0$ for every
$z\in\mathbb Z/2$; and $\mathbb Z^n$ has no nonzero element $v$ with $2v=0$.

**Proof sketch.** By the structure theorem $A\cong\mathbb Z^n\times T$ with $T$ finite, and
$n\ge1$ because $A$ has an element of infinite order. The map
$\rho:A\to\mathbb Z/2\times T/2T$, $(v,t)\mapsto(v_0\bmod2,\ t\bmod2T)$, is onto and kills $2A$, so
$\#(A/2A)\ge2\,\#(T/2T)$. For finite $T$, doubling has kernel and cokernel of the same size, so
$\#(T/2T)=\#T[2]$. Since $\mathbb Z^n$ is torsion-free, $A[2]$ injects into $T[2]$. Hence
$\#(A/2A)\ge2\cdot4=8$.

## Depends on

None.

## Sources

- [RK9](../../../sources/rank-locators.md#rk9)
