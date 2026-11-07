---
article_id: af_9bd131a247c2073fbc6ed0ea
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Packed.packed_register_iff, ZInQ.Compiler.Packed.packed_state_iff
---

# Decoding the transition equations

Let $K<B$ be natural numbers and $q\in\mathbb N$.

1. (Registers) Let $\rho_t<K$, $\alpha_t\le1$, $\gamma_t\le1$ for $t\le q$, let $\iota<K$, and
   put $R=\sum_{t\le q}\rho_tB^t$, $A=\sum_{t\le q}\alpha_tB^t$, $C=\sum_{t\le q}\gamma_tB^t$. Then
   $$R+BC=\iota+BR+BA$$
   holds if and only if $\rho_0=\iota$, $\rho_{t+1}+\gamma_t=\rho_t+\alpha_t$ for all $t<q$, and
   $\gamma_q=\rho_q+\alpha_q$.
2. (States) Suppose $B\ge2$. Let $\sigma_t\le1$ and $\eta_t\le1$ for $t\le q$,
   $S=\sum_{t\le q}\sigma_tB^t$, $I=\sum_{t\le q}\eta_tB^t$ and $e\in\{0,1\}$. Then $S=e+BI$
   holds if and only if $\sigma_0=e$, $\sigma_{t+1}=\eta_t$ for $t<q$, and $\eta_q=0$.

**Proof sketch.** Compare base-$B$ digits. In item 1 the slot-$0$ digits are $\rho_0$ and
$\iota$, the slot-$(t+1)$ digits are $\rho_{t+1}+\gamma_t\le K$ and $\rho_t+\alpha_t\le K$ for
$t<q$, and the slot-$(q+1)$ digits are $\gamma_q$ and $\rho_q+\alpha_q\le K$; every digit on
either side is at most $K<B$, so uniqueness of base-$B$ expansions (with an unbounded top
part) gives digitwise equality, and conversely. Item 2 is the same with digits at most
$1<B$.

## Depends on

None.

## Sources

- [Section 10.1 transition equations](../../../../sources/compiler-natural-locators.md#section-101-transition-equations)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
