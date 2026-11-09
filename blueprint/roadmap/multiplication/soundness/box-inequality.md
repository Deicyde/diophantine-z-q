---
article_id: af_4e7474540df5310d4643573e
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.box_inequality
---

# The final inequality of the finite-box deduction

Let $A\ge1$ be real and $N\ge0$ an integer with
$$N^2<24A\,N^{48/25}+10 .$$
Then $N<(48A)^{13}$.

**Proof sketch.** If $N\le4$, then $N<48\le(48A)^{13}$. Let $N\ge5$ and suppose
$N^{2/25}\ge48A$. Then $24AN^{48/25}\le\tfrac12N^{2/25}N^{48/25}=\tfrac12N^2$, so
$N^2<\tfrac12N^2+10$ and $N^2<20$, contradicting $N\ge5$. Hence $N^{2/25}<48A$, so
$N<(48A)^{25/2}\le(48A)^{13}$ because $48A\ge1$.

## Depends on

None.

## Sources

- [Finite-box deduction](../../../sources/multiplication-locators.md#finite-box-deduction)
