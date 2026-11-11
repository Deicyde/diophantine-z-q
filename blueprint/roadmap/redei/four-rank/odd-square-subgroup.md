---
article_id: af_3d593d4291ee7b232eaf24bb
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.odd_card_range_sq_iff, ZInQ.RouteK.Redei.card_ker_sq_mul_card_range_sq
---

# When the subgroup of squares has odd order

Let $G$ be a finite commutative group, $G^2=\{x^2:x\in G\}$ its subgroup of squares and
$G[2]=\{x\in G:x^2=1\}$ its 2-torsion. Then $|G^2|$ is odd if and only if $G[2]\cap G^2=1$.

Moreover every commutative group $G$ satisfies $|G[2]|\cdot|G^2|=|G|$, where an infinite group is
given order $0$.

**Proof sketch.** If $|G^2|$ is odd, an element of $G[2]\cap G^2$ has order dividing $2$ and, as an
element of $G^2$, dividing $|G^2|$, so it is trivial. If $|G^2|$ is even, Cauchy's theorem gives an
element of order $2$ in $G^2$, and it lies in $G[2]\cap G^2$. The identity is the first isomorphism
theorem for the homomorphism $x\mapsto x^2$, whose kernel is $G[2]$ and whose image is $G^2$.

## Depends on

None.

## Sources

- [Step 6: the 4-rank](../../../sources/redei-locators.md#step-6-the-4-rank)
