---
article_id: af_550250f71b3e965cff620c96
declaration: lemma
origin: cited
---

# Capped arithmetic

For $L\in\mathbb N$ put $\sigma_L(x)=\min(x,L+1)$ on $\mathbb N$. Then for all $x,y,k\in\mathbb N$:

1. $\sigma_L(x+y)=\sigma_L(\sigma_Lx+\sigma_Ly)$, $\sigma_L(xy)=\sigma_L(\sigma_Lx\cdot\sigma_Ly)$ and
   $\sigma_L(\max(x,y))=\max(\sigma_Lx,\sigma_Ly)$;
2. if $L\ge1$, then $\sigma_L(x^k)=\sigma_L\bigl((\sigma_Lx)^{\sigma_Lk}\bigr)$; the cases $x=0$, $x=1$ and
   $k=0$ are immediate, and for $x\ge2$ an exponent $k>L$ already gives $x^k>L$;
3. $\sigma_L(k!)$ is the capped product $\sigma_L(\cdots\sigma_L(\sigma_L(1\cdot2)\cdot3)\cdots k)$;
4. $x\le L\iff\sigma_Lx\le L$.

Consequently, for an integer expression built from literals, addition, multiplication,
nonnegative powers, maximum and factorial, evaluating it with every operation followed by
$\sigma_L$ yields exactly $\sigma_L$ of its value, and every intermediate value is at most
$\max(L+1,\text{the literals})$; with the multiplication guard of the capped evaluator
($a>\lfloor L/b\rfloor$ signals overflow) and binary exponentiation with early overflow exit,
this is a terminating computation. Finally, for natural $U,V\ge1$ and $B\in\mathbb N$,
$$4\cdot\tfrac UV<4^{-B}\iff4^B\le\Bigl\lfloor\frac{V-1}{4U}\Bigr\rfloor ,$$
and for $L=\lfloor(V-1)/(4U)\rfloor$ this holds iff $\sigma_L(4^{\sigma_L B})\le L$. So the precision
test is decided from $\sigma_L$ of the astronomically large exponent, which is never evaluated
in full.

**Proof sketch.** Items 1 and 4 by cases on $x,y\le L+1$. Item 2: for $x\ge2$ and $k\ge L+1$,
$x^k\ge2^{L+1}>L$, so both sides are $L+1$; otherwise reduce to item 1 by induction on $k$.
Item 3 by item 1 and induction. The threshold: $4U\cdot4^B<V\iff4U\cdot4^B\le V-1\iff
4^B\le\lfloor(V-1)/(4U)\rfloor$; then apply items 2 and 4 with base $4$.

## Depends on

None.

## Sources

- [Section 10 opening](../../../../sources/compiler-translation-locators.md#section-10-opening)
- [Section 10.3 precision IR](../../../../sources/compiler-translation-locators.md#section-103-precision-ir)
