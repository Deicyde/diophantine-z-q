---
article_id: af_a9fe4b0787e2eeac99834093
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Literature.certifiedRankTYZClRk_of_literature
---

# Row 5b, vanishing at the centre and Gross–Zagier give CR₃^TYZ_Cl,Rk

Tian–Yuan–Zhang's row 5b, vanishing at the centre and the Gross–Zagier statement together imply
the [class-number hypothesis in positive-rank form](../certified-rank-tyz-cl-rk.md)
CR₃^TYZ_Cl,Rk: for every natural number $d$ with $d\equiv5\pmod8$, $d$ squarefree and
$T^{\rm Cl}_{5b}(d)=1$, the curve $C_d$ has a rational point of infinite order.

The hypothesis taken here is vanishing at the centre. Combined with
[the functional equation gives vanishing at the centre](root-number-vanishing-of-functional-equation.md),
the functional equation on the critical strip may be assumed in its place; that combination is
the one used by
[the main theorem from the $j$-form and the L-series statements](../../main/main-theorem-literature.md).

**Proof sketch.** Let $d$ be as above. Analytic rank one gives an entire continuation $F$ of
$L(C_d,s)$ whose order of vanishing at $s=1$ is exactly $1$. Since $d\equiv5\pmod8$, $d\ne0$, so
$-d^2\ne0$ and the discriminant $-64(-d^2)^3=64d^6$ of $C_d$ is nonzero: $C_d$ is an elliptic
curve. The Gross–Zagier statement applied to $C_d$ and $F$ gives a point of infinite order in
$C_d(\mathbb Q)$.

## Depends on

- [Tian–Yuan–Zhang's row 5b](tyz-row-5b.md)
- [Vanishing at the centre for $d\equiv5\pmod8$](root-number-vanishing.md)
- [Gross–Zagier: a simple zero gives a point of infinite order](gross-zagier.md)
- [The class-number hypothesis in positive-rank form](../certified-rank-tyz-cl-rk.md)

## Proof depends on

- [Analytic rank one for the curves of row 5b](analytic-rank-one.md)

## Sources

- [The literature form of CR3](../../../sources/rank-locators.md#the-literature-form-of-cr3)
