---
article_id: af_c6f0b214ab1f42a429e679b4
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.field_height_bounds
---

# Height bounds in $K_0$

Let $h$ be the absolute logarithmic height on $K_0$ and $\epsilon=1+s$. For all $x,y\in K_0$ and
$x_0,x_1\in\mathbb Q$:

1. $h(xy)\le h(x)+h(y)$ and $h(x+y)\le h(x)+h(y)+\log2$;
2. $h(s)=\tfrac12\log2$ and $h(\epsilon)=\tfrac12\log(1+\sqrt2)$; hence
   $h(\epsilon^4x)\le h(x)+2\log(1+\sqrt2)$;
3. $h(x_0+x_1s)\le h(x_0)+h(x_1)+\tfrac32\log2$, where on $\mathbb Q$ the height $h$ is the
   rational height $\log\max(|a|,b)$.

These are the "fixed coordinate change" estimates of the finite-box deduction.

**Proof sketch.** Place by place, $\max(1,|xy|_v)\le\max(1,|x|_v)\max(1,|y|_v)$, and
$\max(1,|x+y|_v)$ is at most $\max(1,|x|_v)\max(1,|y|_v)$ at finite places and twice that at the
two real places; dividing $\sum_vn_v\log(\cdot)$ by $[K_0:\mathbb Q]=2$ gives (1). For $s$, both
real embeddings have absolute value $\sqrt2$ and $|s|_v\le1$ at finite places. $\epsilon$ is a
unit with embeddings $1+\sqrt2>1$ and $|1-\sqrt2|<1$, so $h(\epsilon)=\tfrac12\log(1+\sqrt2)$ and
$h(\epsilon^4x)\le4h(\epsilon)+h(x)$. (3) follows from (1), (2) and the agreement of $h$ with the
rational height on $\mathbb Q$.

## Depends on

- [The $x$-height on $C(K_0)$](../../model/heights/x-height.md)

## Proof depends on

- [The height of a fraction in $\mathbb Z[\sqrt2]$](../../model/heights/x-height-formula.md)

## Sources

- [Finite-box deduction](../../../sources/multiplication-locators.md#finite-box-deduction)
