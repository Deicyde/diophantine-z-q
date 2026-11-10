---
article_id: af_181d4d375eb36f52e97b453c
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.GreenTaoDense.exists_prime_modulus_of_frequently_window, ZInQ.GreenTaoDense.exists_prime_scale_near, ZInQ.GreenTaoDense.card_window_le_card_quarter
---

# Choosing the prime modulus

Let $A$ be a set of natural numbers and $c_1>0$ such that
$\#(A\cap(\lfloor Z/2\rfloor,Z])\ge c_1Z/\log Z$ for infinitely many $Z$. Then for every $W>0$ and
every bound $Q_0$ there is a prime $q\ge Q_0$ such that $X=W\lfloor q/8\rfloor$ satisfies $X\ge Q_0$
and
$$\#\bigl(A\cap(\lfloor X/4\rfloor,X]\bigr)\ge\frac{c_1}{6}\cdot\frac{X}{\log X}.$$

The scale $X=W\lfloor q/8\rfloor$ and the window $(X/4,X]$ are those that the W-trick of the
Green–Tao proof samples in the cyclic group of order $q$.

**Proof sketch.** *Bertrand.* For any $Z$ put $m=\lfloor Z/W\rfloor+1$; Bertrand's postulate gives a
prime $q$ with $8m<q\le16m$, so $m\le\lfloor q/8\rfloor\le2m$, hence $q>8\lfloor Z/W\rfloor$ and
$Z\le W\lfloor q/8\rfloor\le2Z+2W$. *Window transfer.* For $Z\le X\le2Z+2W$, the window
$(\lfloor Z/2\rfloor,Z]$ lies in $(\lfloor X/4\rfloor,X]$ up to the at most $W/2+1$ integers of
$(\lfloor Z/2\rfloor,\lfloor X/4\rfloor]$. Now take a good $Z$ so large that
$\log Z\le c_1Z/(2(W+1))$ and $Z\ge Q_0W+2W+Q_0+3$. Then $q\ge Q_0$, $X\ge Z\ge Q_0$, $X\le3Z$, and
$c_1Z/\log Z\ge2(W+1)$, so $A$ has at least $\frac12c_1Z/\log Z\ge\frac{c_1}6X/\log X$ elements in
$(\lfloor X/4\rfloor,X]$, using $X\le3Z$ and $\log Z\le\log X$.

## Depends on

None.

## Sources

- [The proof for a dense set](../../sources/green-tao-locators.md#the-proof-for-a-dense-set)
- [The Lean statements](../../sources/green-tao-locators.md#the-lean-statements)
