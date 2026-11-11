---
article_id: af_1264d0c7b6b5c43ed275aece
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.finiteIndex_two_points
---

# The weak Mordell–Weil theorem for $C_n$

Let $n$ be a positive integer. Then $2C_n(\mathbb Q)$ has finite index in $C_n(\mathbb Q)$.

**Proof sketch.** $C_n=E_{-n^2}$, and the isogenous curve is
$E_{-4\cdot(-n^2)}=E_{4n^2}=C'_n:y^2=x^3+4n^2x$. Since $n\ne0$, the curves $C_n$, $C'_n$ and
$E_{16\cdot(-n^2)}=E_{-16n^2}$ are elliptic over $\mathbb Q$. The Kummer images
$\alpha_{-n^2}(C_n(\mathbb Q))$ and $\alpha_{4n^2}(C'_n(\mathbb Q))$ are finite, by the finiteness
of the Kummer image over $\mathbb Q$ for the nonzero integers $c=-n^2$ and $c=4n^2$. The index
theorem with $b=-n^2$ then shows that $2C_n(\mathbb Q)$ has finite index.

## Depends on

None.

## Proof depends on

- [The two-torsion of $C_n(\mathbb Q)$](two-torsion.md)
- [The index of $2E_b(K)$ from the two Kummer images](index-from-kummer-images.md)
- [The Kummer image over $\mathbb Q$ is finite](kummer-image-finite.md)

## Sources

- [Silverman-Tate](../../../sources/rank-locators.md#silverman-tate)
- [Mordell-Weil for the congruent number curves](../../../sources/rank-locators.md#mordell-weil-for-the-congruent-number-curves)
