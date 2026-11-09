---
article_id: af_1fbe0479e46d3b2016d732ae
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.rel_member_iff_iota, ZInQ.rel_member_iff_existsUnique_iota
---

# Accepted inputs have unique indices

For every $p\in\mathbb Q^5$,
$$\mathrm{Rel}_{\mathtt{member}}(p)\iff\exists n\in\mathbb Z:\ p=\iota(n),$$
and the integer $n$ is then unique. In words, the canonical point codes form exactly the
infinite cyclic group $2E(K_0)=\mathbb ZP_0$, and the membership polynomial types arbitrary
inputs.

**Proof sketch.** Combine polynomial membership with the generator certificate:
$2E(K_0)=\{[n]P_0:n\in\mathbb Z\}$, so the codes of points of $2E(K_0)$ are exactly the
$\iota(n)$; uniqueness of $n$ is injectivity of $\iota$.

## Depends on

- [The membership template](../syntax/template-member.md)
- [Point codes](point-codes.md)

## Proof depends on

- [Polynomial membership in the doubled group](membership.md)
- [The generator certificate](generator.md)

## Sources

- [Membership and addition](../../sources/model-locators.md#membership-and-addition)
- [Generator certificate statement](../../sources/model-locators.md#generator-certificate-statement)
