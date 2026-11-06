---
article_id: af_059168e8d9ee374cfb46e263
declaration: def
origin: cited
statement: formalized
lean: ZInQ.hK0, ZInQ.hx
---

# The $x$-height on $C(K_0)$

For $x\in K_0$ let $h(x)$ be the absolute logarithmic Weil height,
$$h(x)=\frac1{[K_0:\mathbb Q]}\sum_{v}n_v\log\max(1,|x|_v)
=\frac12\sum_v n_v\log\max(1,|x|_v),$$
the sum over the places $v$ of $K_0$ (the two real places and the finite places), with
$|\cdot|_v$ extending the usual absolute value of $\mathbb Q$ and local degrees $n_v$. For a
point $T\in C(K_0)$ put
$$h_x(T)=h(x(T))\ \ (T\ne O),\qquad h_x(O)=0 .$$
For $x\in\mathbb Q$ this is the height $\log\max(|a|,b)$ of a reduced fraction $a/b$.

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](../field/quadratic-field.md)
- [The change of variables to $C$](../descent/coordinate-change.md)

## Sources

- [Duplication bounds](../../../sources/model-locators.md#duplication-bounds)
- [Height comparison](../../../sources/model-locators.md#height-comparison)
