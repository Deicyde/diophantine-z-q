---
article_id: af_c97bcef08b65a490cd31b1a6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.Maj.mono, ZInQ.Size.Maj.X, ZInQ.Size.Maj.C, ZInQ.Size.Maj.add, ZInQ.Size.Maj.mul, ZInQ.Size.Maj.bind₁, ZInQ.Size.Maj.constructor, ZInQ.Size.Maj.rename, ZInQ.Size.Maj.bind₁_of_maj_zero, ZInQ.Size.Maj.sum_sq, ZInQ.Size.Maj.prod
---

# Closure rules for the height majorant

Let $B\ge2^{20}$ be an integer and write $\mathrm{Maj}(h,P)$ for $\mathrm{Maj}_B(h,P)$.

0. *Monotonicity and atoms.* $\mathrm{Maj}(h,P)$ and $h\le h'$ imply $\mathrm{Maj}(h',P)$. Every
   variable satisfies $\mathrm{Maj}(0,X_i)$, and every integer constant $c$ with $|c|\le2^{B^8}$
   satisfies $\mathrm{Maj}(1,c)$.
1. *Operations.* $\mathrm{Maj}(h_1,P)$ and $\mathrm{Maj}(h_2,Q)$ imply
   $\mathrm{Maj}(1+\max(h_1,h_2),P+Q)$ and $\mathrm{Maj}(1+\max(h_1,h_2),PQ)$.
2. *Substitution.* If $\mathrm{Maj}(H,P)$ and $\mathrm{Maj}(k,Q_i)$ for every $i$ such that $X_i$
   occurs in $P$, then $\mathrm{Maj}(H+k+1,P(Q))$.
3. *Constructors.* If $\deg C\le B^4$, $\|C\|_1\le2^{B^8}$ and $\mathrm{Maj}(k,Q_i)$ for all
   arguments, then $\mathrm{Maj}(k+1,C(Q))$.
4. *Renaming.* $\mathrm{Maj}(h,P)$ implies $\mathrm{Maj}(h,P(Y_\sigma))$ for every map $\sigma$ of
   variables.
5. *Sums of squares.* If $1\le m\le B$ and $\mathrm{Maj}(h,c_i)$ for $i=1,\dots,m$, then
   $\mathrm{Maj}(h+2,\sum_ic_i^2)$.
6. *Products.* If $1\le m\le B$ and $\mathrm{Maj}(h,c_i)$ for $i=1,\dots,m$, then
   $\mathrm{Maj}(h+1,\prod_ic_i)$.

**Proof sketch.** Throughout, $B^{8h}\ge B\ge2^{20}$ for $h\ge1$, and the height-zero case has
norm at most $1$. (1) Degrees: $\max\le B^{8m}$ and $2B^{8m}\le B^{8m+8}$ for $m=\max(h_1,h_2)$
(for $m=0$, $\deg\le2\le B^8$). Norms: $\|P+Q\|_1\le2\cdot2^{B^{8m}}$ and $\|PQ\|_1\le2^{2B^{8m}}$, both at
most $2^{B^{8m+8}}$. (2) By the substitution bounds with $d=B^{8k}$ (or $1$) and
$M=2^{B^{8k}}$ (or $1$ when $k=0$): $\deg\le B^{8H}B^{8k}\le B^{8(H+k+1)}$ and
$\log_2\|P(Q)\|_1\le B^{8H}+B^{8H}B^{8k}\le B^{8(H+k+1)}$; for $k=0$ simply $\|P(Q)\|_1\le\|P\|_1$.
(3) Likewise $\deg\le B^4B^{8k}\le B^{8k+8}$ and $\log_2\|C(Q)\|_1\le B^8+B^4B^{8k}\le B^{8k+8}$ for
$k\ge1$; for $k=0$ the arguments have norm at most $1$ and $\log_2\|C(Q)\|_1\le B^8$. (4) By the
renaming bound. (5) $\deg\le2B^{8h}$ and $\|\sum c_i^2\|_1\le m\,2^{2B^{8h}}\le2^{B+2B^{8h}}\le2^{B^{8h+16}}$.
(6) $\deg\le mB^{8h}\le B^{8h+8}$ and $\|\prod c_i\|_1\le2^{mB^{8h}}\le2^{B^{8h+8}}$ (for $h=0$:
degree at most $m\le B^8$, norm at most $1$).

These are the manuscript's rules: positive height $h$ gives degree and logarithmic norm at
most $B^{8h}$; a call charges one level beyond the callee and argument heights; and a
renaming retains the callee's height.

## Depends on

- [Syntax heights](syntax-height.md)

## Proof depends on

- [Elementary estimates for the coefficient norm](../norms/l1-norm-estimates.md)
- [Substitution and renaming bounds](../norms/substitution-bounds.md)

## Sources

- [Section 12.1 syntax heights](../../../sources/size-locators.md#section-121-syntax-heights)
- [Companion size proof](../../../sources/size-locators.md#companion-size-proof)
