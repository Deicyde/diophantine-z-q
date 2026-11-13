---
article_id: af_2cba4169bc3dc7a1dde3a9ae
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.AlphaPower.alphaZ_large_odd
---

# Odd alpha values are unbounded

Let $b>3$ and $a\in\mathbb N$. There is $k>0$ such that $u=\alpha_b(k)$ is odd and $u>2a$;
moreover $t=\alpha_b(k+1)$ satisfies $u<t$ and $u^2+t^2=1+but$.

**Proof sketch.** Of the adjacent terms $\alpha_b(2a+1)$ and $\alpha_b(2a+2)$ at least one is
odd (adjacent terms are not both even), and both exceed $2a$ since $\alpha_b(n)\ge n$. Take
$k$ the corresponding index. The last two claims are strict growth and the quadratic
identity.

## Depends on

- [The alpha sequence](alpha-sequence.md)

## Proof depends on

- [Growth of the alpha sequence](alpha-growth.md)
- [Matrix powers and the quadratic identity](alpha-matrix.md)

## Sources

- [Section 10.2 alpha completeness](../../../../sources/compiler-natural-locators.md#section-102-alpha-completeness)
