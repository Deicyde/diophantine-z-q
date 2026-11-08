---
article_id: af_4072501e0104210161b82c54
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.Qsqrt.torsionOrder_le_six, ZInQ.Progressions.torsionOrder_le_six_of_finrank_eq_two, ZInQ.Progressions.le_six_of_totient_le_two
---

# Roots of unity in a quadratic field

Let $K$ be a number field of degree $2$, for example $K=\mathbb Q(\sqrt d)$ with $d$ an integer
that is not the square of a rational number. The group of roots of unity of $K$ has order
$w_K\le6$.

**Proof sketch.** The roots of unity of $K$ form a finite cyclic group, so $K$ contains a
primitive root of unity $\zeta$ of order $w_K$. Then $\mathbb Q(\zeta)\subseteq K$ has degree
$\varphi(w_K)\le2$. By induction over prime powers and coprime products, $\varphi(n)\le2$
forces $n\mid12$, and then $n\in\{1,2,3,4,6\}$, so $w_K\le6$.

## Depends on

- [The quadratic field $\mathbb Q(\sqrt d)$](quadratic-field.md)

## Sources

- [Marcus, Chapter 5](../../../sources/progressions-locators.md#marcus-chapter-5)
