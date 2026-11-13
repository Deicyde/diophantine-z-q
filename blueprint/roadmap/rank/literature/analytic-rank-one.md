---
article_id: af_e1f9458e005305102bbe0f3d
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Literature.analyticOrder_eq_one
---

# Analytic rank one for the curves of row 5b

Assume Tian–Yuan–Zhang's row 5b and vanishing at the centre. Let $d$ be a natural number with
$d\equiv5\pmod8$, $d$ squarefree and $T^{\rm Cl}_{5b}(d)=1$. Then $L(C_d,s)$ has an entire
continuation whose order of vanishing at $s=1$ is exactly $1$.

**Proof sketch.** Row 5b gives an entire continuation $F$ of $L(C_d,s)$ whose order of vanishing
at $1$ is at most $1$. Since $F$ is entire it is analytic at $1$, and $F(1)=0$ by vanishing at the
centre, so its order of vanishing at $1$ is not $0$. An order at most $1$ and not $0$ is $1$.

## Depends on

- [Tian–Yuan–Zhang's row 5b](tyz-row-5b.md)
- [Vanishing at the centre for $d\equiv5\pmod8$](root-number-vanishing.md)

## Sources

- [The literature form of CR3](../../../sources/rank-locators.md#the-literature-form-of-cr3)
