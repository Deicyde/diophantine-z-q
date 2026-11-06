---
article_id: af_b89f2bc94e8c196fd92d41d1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Packed.nonzero_indicator
---

# The packed nonzero indicator

Let $c>0$, $K=2^c$, $B=4K$, $F_q$, $D=(K-1)F_q$ be as in the masked-digit statement and
$R=\sum_{t=0}^q\rho_tB^t$ with all $\rho_t<K$. Then
$$(R+D)\mathbin{\mathrm{AND}}(KF_q)=K\cdot\sum_{t=0}^q[\rho_t>0]\,B^t .$$
Consequently, for $N\in\mathbb N$, $KN=(R+D)\mathbin{\mathrm{AND}}(KF_q)$ holds if and only if
$N=\sum_{t\le q}[\rho_t>0]B^t$, the packed nonzero indicator of $R$; no separate mask
condition on $N$ is needed.

**Proof sketch.** $R+D=\sum_t(\rho_t+K-1)B^t$, and each slot digit satisfies
$\rho_t+K-1\le2K-2<2K<B$, so the sum has no carries. $KF_q$ has exactly bit $c$ of each slot
$t\le q$. The bit $c$ (value $K$) of the slot digit $\rho_t+K-1\in[K-1,2K-2]$ is set
exactly when $\rho_t+K-1\ge K$, that is when $\rho_t>0$. Cancel the factor $K=2^c$.

## Depends on

- [Digits of masked histories](packed-masks.md)

## Sources

- [Section 10.1 nonzero and branch masks](../../../../sources/compiler-natural-locators.md#section-101-nonzero-and-branch-masks)
