---
article_id: af_73996e7fa0da3a35d8aff0b9
declaration: theorem
origin: bridged
---

# Mordell–Weil for the congruent number curves

> **The congruent-number route.** This page belongs to the congruent-number route to pole completeness, through Tian–Yuan–Zhang and Gross–Zagier. [Elliot's route](../../main/main-theorem.md) is the other route to the same theorem. This page's Lean declarations are not on this fork's main (fork issue #77); the route's Lean is kept at the tag `route-k-final` and pinned upstream in elliotglazer/diophantine-z-q.

Let $n$ be a positive integer. The group $C_n(\mathbb Q)$ of rational points of
$C_n:y^2=x^3-n^2x$ is finitely generated.

In the form used by the positive-rank chapter: for every natural number $d\ne0$, the group
$C_d(\mathbb Q)$ is finitely generated.

**Proof sketch.** (Silverman, Theorem VIII.3.1 and Section VIII.6; Silverman–Tate,
Chapter III.) $C_n$ is an elliptic curve over $\mathbb Q$. Let $h$ be the naive height: $h(O)=0$, and
$h((x,y))=\sum_v\log\max(1,|x|_v)$ over the places of $\mathbb Q$, which is $\log\max(|r|,|s|)$
for $x=r/s$ in lowest terms. Then:

- $h\ge0$;
- there is a constant $c$ with $|h(P+Q)+h(P-Q)-2h(P)-2h(Q)|\le c$ for all $P,Q$ (the approximate
  parallelogram law);
- for every bound $B$ only finitely many $P$ have $h(P)\le B$ (Northcott's property for
  $\mathbb Q$, since each abscissa determines at most two points).

The descent theorem says that an abelian group $G$ with such a height, in which $2G$ has finite
index, is finitely generated. By the weak Mordell–Weil theorem, $2C_n(\mathbb Q)$ has finite
index in $C_n(\mathbb Q)$. The second form is the first with $n=d$.

## Depends on

None.

## Proof depends on

- [The two-torsion of $C_n(\mathbb Q)$](two-torsion.md)
- [The weak Mordell–Weil theorem for $C_n$](weak-mordell-weil.md)

## Sources

- [Mordell-Weil for the congruent number curves](../../../sources/rank-locators.md#mordell-weil-for-the-congruent-number-curves)
- [Silverman: descent and heights](../../../sources/rank-locators.md#silverman-descent-and-heights)
- [Silverman-Tate](../../../sources/rank-locators.md#silverman-tate)
