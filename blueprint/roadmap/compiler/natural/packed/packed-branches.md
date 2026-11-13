---
article_id: af_231603786793f419307aa3d5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Packed.branch_split, ZInQ.Compiler.Packed.indicator_digits
---

# Branch histories and indicator digits

Let $B\ge2$, $q\in\mathbb N$, $S=\sum_{t\le q}\sigma_tB^t$ and $N=\sum_{t\le q}\nu_tB^t$ with
$\sigma_t,\nu_t\in\{0,1\}$, $B$ a power of two.

1. $V=S\mathbin{\mathrm{AND}}N$ and $S=V+W$ hold (for natural $V,W$) if and only if
   $V=\sum_t\sigma_t\nu_tB^t$ and $W=\sum_t\sigma_t(1-\nu_t)B^t$.
2. In the setting of the packed-history construction, suppose that in every slot $t\le q$
   exactly one state digit $\sigma_i(t)$ is $1$ and that the halt state has no outgoing
   instruction. Then the packed indicators $A_j$, $C_j$ and $I_i$ of items 6 and 7 of the
   construction have all slot digits in $\{0,1\}$; precisely, writing $i_t$ for the active
   state at time $t$, the slot-$t$ digit of $A_j$ is $[p_{i_t}=\mathrm{inc}(j,\cdot)]$, that of
   $C_j$ is $[p_{i_t}=\mathrm{dec}(j,\cdot,\cdot)]\,\nu_j(t)$, and that of $I_i$ is $1$ exactly when
   the instruction at $i_t$ takes, at time $t$, a branch to $i$ (the nonzero branch of a
   sub instruction if $\nu_j(t)=1$, its zero branch otherwise).

**Proof sketch.** (1) Both $S$ and $N$ have zero-one digits in distinct bit positions, so
$S\mathbin{\mathrm{AND}}N$ is computed slotwise; $W=S-V$ slotwise. (2) A sum of packed numbers
with zero-one digits is computed slotwise as long as the slot sums stay below $B$; at time
$t$ only the instruction at $i_t$ contributes, through $S_{i_t}$, $V_{i_t}$ or $W_{i_t}$, and
for a sub instruction exactly one of $V_{i_t},W_{i_t}$ has digit $1$ by (1); this holds even
if two branches of the program have the same target, since only one branch is taken at a
time.

## Depends on

- [The packed-history construction](packed-compiler.md)

## Proof depends on

- [Digits of masked histories](packed-masks.md)

## Sources

- [Section 10.1 nonzero and branch masks](../../../../sources/compiler-natural-locators.md#section-101-nonzero-and-branch-masks)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
