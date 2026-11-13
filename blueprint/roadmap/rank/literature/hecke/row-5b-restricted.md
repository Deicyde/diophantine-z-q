---
article_id: af_c75f388c3db2dda2301ca2f3
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.tyzRow5b_of_readingA_five
---

# Row 5b from reading A and Hecke's continuation for $d\equiv5\pmod8$

[Tian–Yuan–Zhang's Theorem 3.5(2) in reading A](../tyz-reading-a.md) and
[Hecke's continuation for $d\equiv5\pmod8$](continuation-of-deuring.md) together imply
[Tian–Yuan–Zhang's row 5b](../tyz-row-5b.md).

This is [row 5b from reading A and Hecke's continuation](../tyz-row-5b-of-reading-a.md) with
Hecke's continuation for every $d\ne0$ replaced by its case $d\equiv5\pmod8$ squarefree, the only
case row 5b uses.

**Proof sketch.** Let $d$ be a squarefree natural number with $d\equiv5\pmod8$ and
$T^{\rm Cl}_{5b}(d)=1$. Hecke's continuation for $d\equiv5\pmod8$ gives an entire continuation $F$
of $L(C_d,s)$; take it. If its order of vanishing at $s=1$ were not at most $1$, it would be at
least $2$, and reading A would give $T^{\rm Cl}_{5b}(d)=0$, contradicting $T^{\rm Cl}_{5b}(d)=1$.

## Depends on

- [Tian–Yuan–Zhang's Theorem 3.5(2) in reading A](../tyz-reading-a.md)
- [The continuation of $L(C_d,s)$ from Deuring's identity](continuation-of-deuring.md)
- [Tian–Yuan–Zhang's row 5b](../tyz-row-5b.md)

## Sources

- [Reading A of Tian-Yuan-Zhang](../../../../sources/rank-locators.md#reading-a-of-tian-yuan-zhang)
