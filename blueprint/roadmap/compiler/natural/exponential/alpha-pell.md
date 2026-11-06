---
article_id: af_41accc1f091097e574203c6c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.AlphaPower.alphaZ_pell_unordered, ZInQ.AlphaPower.alphaZ_pell_ordered, ZInQ.AlphaPower.alphaZ_pell_converse
---

# Natural solutions of the alpha Pell equation

1. (Unordered) Let $b>2$ and $x,y\in\mathbb N$ with $x^2+y^2=1+bxy$. Then there is
   $n\in\mathbb N$ with $\{x,y\}=\{\alpha_b(n),\alpha_b(n+1)\}$; in particular $x=\alpha_b(n')$
   for some $n'\in\mathbb N$.
2. (Ordered) Let $b$ be any natural number and $r<s$ natural numbers with
   $s^2+r^2=1+bsr$. Then there is $m>0$ with $r=\alpha_b(m-1)$ and $s=\alpha_b(m)$.
3. Conversely, for $b\ge2$ every pair $(\alpha_b(n),\alpha_b(n+1))$ consists of natural
   numbers, satisfies the equation, and has $\alpha_b(n)<\alpha_b(n+1)$.

No ordering assumption on the pair in item 1 is needed.

**Proof sketch.** In item 1, $x\ne y$, since $2x^2=1+bx^2$ is impossible for $b\ge2$; order
the pair as $X>Y$. Item 2 is proved by strong induction on the smaller entry $Y=r$: if
$Y=0$ then $X^2=1$ and $(X,Y)=(1,0)=(U_1,U_0)$. Otherwise put $Z=bY-X\in\mathbb Z$. Vieta's
relation for the quadratic in $X$ gives $XZ=Y^2-1$; hence $Z\ge0$ (as $Y\ge1$) and $Z<Y$ (as
$X>Y$), and $(Y,Z)$ satisfies the same equation with $Y>Z$. By induction
$(Z,Y)=(U_{m-1},U_m)$ for some $m>0$, and then $X=bY-Z=U_{m+1}$. Item 1 follows from item
2 applied to the ordered pair. Item 3 is the growth lemma and the quadratic identity.

## Depends on

- [The alpha sequence](alpha-sequence.md)

## Proof depends on

- [Matrix powers and the quadratic identity](alpha-matrix.md)
- [Growth of the alpha sequence](alpha-growth.md)

## Sources

- [Section 10.2 Pell classification](../../../../sources/compiler-natural-locators.md#section-102-pell-classification)
