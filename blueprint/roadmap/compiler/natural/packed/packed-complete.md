---
article_id: af_fed5f50978e36b1cd93a1d06
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Packed.packed_complete
---

# Completeness of the packed-history construction

Let $p$ be valid for $r$ registers with $m$ instructions, $1\le k\le r$ and
$a\in\mathbb N^k$. If $p$ accepts $a$, then the formula of the packed-history construction
of $p$ holds for some natural values of its fresh variables, with every macro read as its
relation.

**Proof sketch.** Let the accepting run have $q$ steps, configurations $(i_t,\rho(t))$ for
$t\le q$, with $i_q=m-1$ and $\rho(q)=0$. Choose $c\ge1$ with $2^c$ larger than every input,
every register value $\rho_j(t)$, and with $4\cdot2^c>m$; put $K=2^c$, $B=4K$, $T=B^q$,
$F=\sum_{t\le q}B^t$, $D=(K-1)F$, $R_j=\sum_t\rho_j(t)B^t$, $S_i=\sum_t[i_t=i]B^t$,
$N_j=\sum_t[\rho_j(t)>0]B^t$, and for each sub instruction $i$ on register $j$,
$V_i=\sum_t[i_t=i][\rho_j(t)>0]B^t$, $W_i=S_i-V_i$. Every equation of items 1, 2 holds by
construction; the masks, the bounds $R_j<T$ and the bitAnd conditions hold by the
masked-digit, nonzero-indicator and branch statements read backwards; the register and
state equations hold by the transition statement read backwards, since consecutive
configurations obey the one-step rule, the run starts at state $0$ with the initial file,
halt has no outgoing branch and $\rho(q)=0$.

## Depends on

- [The packed-history construction](packed-compiler.md)
- [Register machines](../programs/register-machine.md)

## Proof depends on

- [Digits of masked histories](packed-masks.md)
- [One active state per time slot](packed-state-selection.md)
- [The packed nonzero indicator](packed-nonzero-indicator.md)
- [Branch histories and indicator digits](packed-branches.md)
- [Decoding the transition equations](packed-transitions.md)

## Sources

- [Section 10.1 transition equations](../../../../sources/compiler-natural-locators.md#section-101-transition-equations)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
