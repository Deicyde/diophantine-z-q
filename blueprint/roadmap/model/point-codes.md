---
article_id: af_5b8f9b0bc47edf814405a99e
declaration: def
origin: cited
statement: formalized
lean: ZInQ.pointCode, ZInQ.iota
---

# Point codes

The *code* of a point of $E(K_0)$ is the element of $\mathbb Q^5$
$$\operatorname{code}(O)=(1,0,0,0,0),\qquad
\operatorname{code}(x,y)=(0,x_0,x_1,y_0,y_1)\quad\text{where }x=x_0+x_1s,\ y=y_0+y_1s,$$
with $x_0,x_1,y_0,y_1\in\mathbb Q$ the components of the coordinates. For $n\in\mathbb Z$,
$$\iota(n)=\operatorname{code}([n]P_0)\in\mathbb Q^5 .$$
A *canonical code* is the code of a point of $E(K_0)$; a code of a point of $2E(K_0)$ is a
code of a point of the carrier $D=2E(K_0)$.

The integer index $n$ and the five rational coordinates of $\iota(n)$ play different roles:
the index is what the later chapters compute with, the coordinates are what the polynomial
sees. Since $P_0$ has infinite order, distinct indices have distinct codes.

## Depends on

- [The point $P_0$](field/generator-point.md)

## Sources

- [Model setup](../../sources/model-locators.md#model-setup)
- [Point references and fixed point codes](../../sources/model-locators.md#point-references-and-fixed-point-codes)
