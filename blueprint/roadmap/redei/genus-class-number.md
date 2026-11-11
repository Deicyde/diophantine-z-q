---
article_id: af_a0ae73f7c6e778d1cb6682ec
declaration: def
origin: cited
statement: formalized
lean: ZInQ.RouteK.Rank5b.gCl, ZInQ.RouteK.Rank5b.QNeg, ZInQ.RouteK.Rank5b.QNeg.factNotIsSquare, ZInQ.RouteK.Rank5b.QNeg.numberField
---

# The genus class number

For a natural number $n$ let $\mathbb Q(\sqrt{-n})$ be the quadratic algebra
$\mathbb Q[\omega]/(\omega^2+n)$. For $n\ge1$ the number $-n$ is not a square in $\mathbb Q$, so
$\mathbb Q(\sqrt{-n})$ is a field, and a number field. For $n\ge1$ let $\mathrm{Cl}$ be the class
group of the ring of integers of $\mathbb Q(\sqrt{-n})$. The *genus class number* of $n$ is
$$g(n)=\bigl|\mathrm{Cl}^2\bigr|,$$
the order of the subgroup of squares $\mathrm{Cl}^2=\{c^2:c\in\mathrm{Cl}\}$ of the class group.

This is the number $g(n)=\#2\mathrm{Cl}(\mathbb Q(\sqrt{-n}))$ of Tian, Yuan and Zhang, who write
the class group additively; it is the order of the subgroup of squares, not of the 2-torsion. A
finite commutative group has a subgroup of squares of odd order exactly when that subgroup has no
element of order $2$ ([when the subgroup of squares has odd order](four-rank/odd-square-subgroup.md)),
so $g(n)$ is odd exactly when no element of order $2$ of $\mathrm{Cl}$ is a square, that is, when
$\mathrm{Cl}[2]\cap\mathrm{Cl}^2=1$.

## Depends on

None.

## Sources

- [The target](../../sources/redei-locators.md#the-target)
- [Tian-Yuan-Zhang](../../sources/redei-locators.md#tian-yuan-zhang)
