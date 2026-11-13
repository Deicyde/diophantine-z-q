---
article_id: af_fbdb4e2025a4a24c1c8e30be
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Literature.tyzRow5b_of_readingA
---

# Row 5b from reading A and Hecke's continuation

Tian–Yuan–Zhang's Theorem 3.5(2) in reading A and Hecke's continuation together imply
Tian–Yuan–Zhang's row 5b.

**Proof sketch.** Let $d$ be a squarefree natural number with $d\equiv5\pmod8$ and
$T^{\rm Cl}_{5b}(d)=1$. Then $d\ne0$, so Hecke's continuation gives an entire continuation $F$ of
$L(C_d,s)$; take it. If its order of vanishing at $s=1$ were not at most $1$, it would be at
least $2$, and reading A would give $T^{\rm Cl}_{5b}(d)=0$, contradicting $T^{\rm Cl}_{5b}(d)=1$.
Only the row-5b half of reading A is used.

## Depends on

- [Tian–Yuan–Zhang's Theorem 3.5(2) in reading A](tyz-reading-a.md)
- [Hecke's continuation of $L(C_d,s)$](hecke-continuation.md)
- [Tian–Yuan–Zhang's row 5b](tyz-row-5b.md)

## Sources

- [Reading A of Tian-Yuan-Zhang](../../../sources/rank-locators.md#reading-a-of-tian-yuan-zhang)
