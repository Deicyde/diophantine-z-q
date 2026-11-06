---
article_id: af_17be38e8a9f33d942a4ac5d9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.mem_torsion_E_iff, ZInQ.card_torsion_E, ZInQ.genP0_not_isOfFinAddOrder, ZInQ.mem_torsion_C_iff, ZInQ.card_torsion_C
---

# The torsion of $E(K_0)$ is the full two-torsion

Every point of finite order in $E(K_0)$ lies in $E(K_0)[2]=\{O,(0,0),(d,0),(-d,0)\}$. Thus the
torsion subgroup of $E(K_0)$ is $E(K_0)[2]$, of order $4$ and isomorphic to
$(\mathbb Z/2\mathbb Z)^2$. The same holds for $C(K_0)$, whose torsion subgroup is
$C(K_0)[2]=\{O,(0,0),(\delta,0),(-\delta,0)\}$.

In particular $P_0$ has infinite order, since its ordinate is nonzero, so $P_0\notin E(K_0)[2]$.
This part of Proposition 3.1 does not use the Mordell-Weil hypothesis.

**Proof sketch.** Apply reduction with $(p,r,A)=(17,6,-d^2)$ and $(23,5,-d^2)$; by the point
counts both reductions are good, with $20$ and $24$ points. Let $T$ have finite order $n$.
If $17\mid n$, then $[n/17]T$ has order $17$, prime to $23$, so it injects into a group of
order $24$: impossible. Likewise $23\nmid n$, since $23\nmid20$. So $\langle T\rangle$ has order
prime to both primes and injects into both groups: $n\mid\gcd(20,24)=4$. If $n=4$, the
subgroup $\langle T\rangle+E(K_0)[2]$ has order $8$ (it contains the four two-torsion points
and $T\notin E(K_0)[2]$, while $[2]T\in E(K_0)[2]$); its order $8$ is prime to $17$, so it
injects into a group of order $20$, which is impossible since $8\nmid20$. Hence
$n\mid2$ and $T\in E(K_0)[2]$. The statement for $C$ follows through the isomorphism $\theta$.
Finally $y(P_0)\ne0$, while every point of $E(K_0)[2]$ is $O$ or has ordinate $0$.

## Depends on

- [The generator curve $E$](../field/generator-curve.md)
- [The change of variables to $C$](coordinate-change.md)
- [The point $P_0$](../field/generator-point.md)

## Proof depends on

- [Reduction is injective on prime-to-$p$ torsion](reduction-torsion.md)
- [Point counts at $(17,s-6)$ and $(23,s-5)$](reduction-point-counts.md)
- [The coordinates of $P_0$ satisfy the curve equation](../field/generator-point-equation.md)

## Sources

- [Torsion bound](../../../sources/model-locators.md#torsion-bound)
