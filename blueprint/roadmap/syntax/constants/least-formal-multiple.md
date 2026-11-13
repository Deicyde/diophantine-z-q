---
article_id: af_c26aaf8501755e9781b1c2c3
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.normalizedRep, ZInQ.Syntax.xi, ZInQ.Syntax.FormalCondition, ZInQ.Syntax.leastFormalMultiple
---

# The least formal multiple

Every $u\in K_0$ has a unique normalized representation $u=(a+bs)/c$ with
$a,b,c\in\mathbb Z$, $c>0$ and $\gcd(a,b,c)=1$ (for $u=0$ this is $(0,0,1)$). For a point $Q$
of $E(K_0)$ put $\xi(Q)=1/x(Q)$ if $Q\ne O$ and $x(Q)\ne0$, and $\xi(Q)=0$ otherwise.

For an integer $N\ge1$, the least formal multiple $\mathrm{LFM}(N)$ is the least $m\ge1$
such that the normalized representation $(a,b,c)$ of $\xi([m]P_0)$ satisfies
$$N^4\mid a,\qquad N^4\mid b,\qquad \gcd(c,N)=1 .$$
If no such $m$ exists, $\mathrm{LFM}(N)=0$; this convention only makes the definition
total, and the existence of a successful index for the fixed $N_s$ is proved with the
cutoff in Section 12. The fixed constant $M_0=\mathrm{LFM}(N_s)$ is never evaluated.

Since $P_0$ has infinite order, $[m]P_0$ is never $O$ or a point of order two for $m\ge1$,
so the conventions for $\xi$ at those points are never used for $P_0$; they match the
specification's rule that the identity has inverse abscissa zero.

This is a definition.

## Depends on

- [The codes of multiples of the generator](../../model/point-codes.md)

## Sources

- [Section 2.2](../../../sources/syntax-locators.md#section-22-catalogue-and-formal-multiple)
- [Appendix C.1](../../../sources/syntax-locators.md#appendix-c1-scalar-nodes)
