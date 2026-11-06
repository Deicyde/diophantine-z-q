---
article_id: af_a5a84518db63b1f5d63fe70b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Packed.packed_masks
---

# Digits of masked histories

Let $c>0$, $K=2^c$, $B=4K$, $q\in\mathbb N$, $T=B^q$, and let $F,D\in\mathbb N$ satisfy
$BF+1=F+BT$ and $D+F=KF$. Then:

1. $F=F_q=\sum_{t=0}^qB^t$ and $D=(K-1)F_q=\sum_{t=0}^q(K-1)B^t$;
2. a natural number $R$ is masked by $D$ and satisfies $R<T$ if and only if
   $R=\sum_{t=0}^q\rho_tB^t$ with $\rho_t<K$ for all $t$ and $\rho_q=0$;
3. a natural number $S$ is masked by $F_q$ if and only if $S=\sum_{t=0}^q\sigma_tB^t$ with
   $\sigma_t\in\{0,1\}$.

In words: register digits are below $K$, the terminal register digit is zero, and state
digits are zero or one. The digit sequences are unique.

**Proof sketch.** (1) $B\ge8$, so $BF+1=F+BT$ gives $(B-1)F=B^{q+1}-1$, hence
$F=\sum_{t\le q}B^t$; then $D=KF-F$. (2), (3) $B=2^{c+2}$, so the binary expansion of a
number splits into base-$B$ slots of $c+2$ bits. $D$ has, in each slot $t\le q$, the bits
$0,\dots,c-1$ set (value $K-1$) and nothing above slot $q$; $F_q$ has bit $0$ of each slot
$t\le q$. Masking by $D$ (resp. $F_q$) therefore says exactly that every slot digit is below
$K$ (resp. at most $1$) and that the slots above $q$ vanish. Finally $R<B^q$ is equivalent
to $\rho_q=0$ given the other slots vanish.

## Depends on

- [Lucas's criterion for bit inclusion and disjointness](../exponential/lucas-bits.md)

## Sources

- [Section 10.1 packed histories](../../../../sources/compiler-natural-locators.md#section-101-packed-histories)
- [Compiler specification](../../../../sources/compiler-natural-locators.md#compiler-specification)
