---
article_id: af_2f869f448416e81630918759
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Precision.saturatedArithmetic
---

# Saturated arithmetic

For $L\in\mathbb N$ let $\sigma_L(x)=\min(x,L+1)$ on $\mathbb N$. For all natural $x,y,n$:

1. $\sigma_L(x)\le L\iff x\le L$, and more generally $\sigma_L(x)\le k\iff x\le k$ for $k\le L$;
   $\sigma_L(\sigma_L(x))=\sigma_L(x)$; $\sigma_L(0)=0$, $\sigma_L(1)=1$;
2. $\sigma_L(\sigma_L(x)+\sigma_L(y))=\sigma_L(x+y)$,
   $\sigma_L(\sigma_L(x)\cdot\sigma_L(y))=\sigma_L(xy)$ and
   $\sigma_L(\max(\sigma_L(x),\sigma_L(y)))=\sigma_L(\max(x,y))$;
3. $\sigma_L(\sigma_L(x)^n)=\sigma_L(x^n)$;
4. if $L\ge1$, then $\sigma_L(x^{\sigma_L(n)})=\sigma_L(x^n)$, hence
   $\sigma_L(\sigma_L(x)^{\sigma_L(n)})=\sigma_L(x^n)$;
5. $\sigma_L((n+1)!)=\sigma_L(\sigma_L(n!)\cdot(n+1))$, so factorials are computed exactly by
   iterating saturated multiplication.

Item 4 is where bases zero and one and exponent zero are separate cases: for $x\ge2$ an
exponent above $L$ already gives $x^n>L$.

**Proof sketch.** Items 1-3 and 5 by cases on whether the arguments exceed $L$: if
$x\ge L+1$ and $y\ge1$ then $xy\ge L+1$, and $\sigma_L(x)\cdot y\ge L+1$; if $y=0$ both sides
are $0$; item 3 by induction on $n$ from item 2. Item 4: if $n\le L+1$ nothing changes;
otherwise $\sigma_L(n)=L+1$ and, for $x=0$, $0^n=0^{L+1}=0$ (both exponents positive), for
$x=1$ both powers are $1$, and for $x\ge2$ both $x^n$ and $x^{L+1}$ exceed $L$ because
$x^e>e$ for $e\ge0$.

## Depends on

None.

## Sources

- [Section 10 saturation](../../../../sources/compiler-natural-locators.md#section-10-saturation)
