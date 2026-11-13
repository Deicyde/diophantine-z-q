---
article_id: af_5daacdcd02624e3eaafe4f86
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.certifiedRankTYZClRk_of_elementary, ZInQ.Contrib.HeckeFE.certifiedRankTYZClRk_of_gaussPointCount
---

# CR₃^TYZ_Cl,Rk from reading A, Gross–Zagier and Gauss's point count

1. Assume [Tian–Yuan–Zhang's Theorem 3.5(2) in reading A](../tyz-reading-a.md), the
   [Gross–Zagier statement](../gross-zagier.md), [Gauss's point count](gauss/gauss-point-count.md),
   and, for every squarefree $d\equiv5\pmod8$, that the Hecke coefficients are
   [multiplicative](gaussian/hecke-multiplicative.md) and satisfy
   [the Hecke relation at the split primes](gaussian/hecke-split-recursion.md). Then the
   [class-number hypothesis in positive-rank form](../../certified-rank-tyz-cl-rk.md)
   CR₃^TYZ_Cl,Rk holds.
2. Reading A, the Gross–Zagier statement and Gauss's point count imply CR₃^TYZ_Cl,Rk.

Neither Hecke's continuation nor the functional equation is assumed.

**Proof sketch.** (1) [Hecke's continuation for $d\equiv5\pmod8$ and the functional equation](both-from-gauss-count.md)
(1) gives both statements. Hecke's continuation for $d\equiv5\pmod8$ with reading A gives row 5b
([row 5b from the restricted continuation](row-5b-restricted.md)); the functional equation gives
[vanishing at the centre](../root-number-vanishing-of-functional-equation.md); and row 5b, vanishing
at the centre and Gross–Zagier give CR₃^TYZ_Cl,Rk
([their combination](../certified-rank-tyz-cl-rk-of-literature.md)).

(2) Multiplicativity and the Hecke relation at the split primes hold for every $d$
([multiplicativity](gaussian/hecke-multiplicative.md),
[the Hecke relation](gaussian/hecke-split-recursion.md) (1)); apply (1).

## Depends on

- [Tian–Yuan–Zhang's Theorem 3.5(2) in reading A](../tyz-reading-a.md)
- [Gross–Zagier: a simple zero gives a point of infinite order](../gross-zagier.md)
- [Gauss's point count on $y^2=x^3-x$](gauss/gauss-point-count.md)
- [The Hecke coefficients are multiplicative](gaussian/hecke-multiplicative.md)
- [The Hecke relation at prime powers](gaussian/hecke-split-recursion.md)
- [The class-number hypothesis in positive-rank form](../../certified-rank-tyz-cl-rk.md)

## Proof depends on

- [Hecke's continuation for $d\equiv5\pmod8$ and the functional equation from Gauss's point count](both-from-gauss-count.md)
- [Row 5b from reading A and Hecke's continuation for $d\equiv5\pmod8$](row-5b-restricted.md)
- [The functional equation gives vanishing at the centre](../root-number-vanishing-of-functional-equation.md)
- [Row 5b, vanishing at the centre and Gross–Zagier give CR₃^TYZ_Cl,Rk](../certified-rank-tyz-cl-rk-of-literature.md)

## Sources

- [The literature form of CR3](../../../../sources/rank-locators.md#the-literature-form-of-cr3)
- [Reading A of Tian-Yuan-Zhang](../../../../sources/rank-locators.md#reading-a-of-tian-yuan-zhang)
