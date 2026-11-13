---
article_id: af_414a58cc5df869ecd9b96c07
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Packed.packed_sound, ZInQ.Compiler.Packed.packed_sound_accepts
---

# Soundness of the packed-history construction

Let $p$ be valid for $r$ registers with $m$ instructions, $1\le k\le r$ and
$a\in\mathbb N^k$. If the formula of the packed-history construction of $p$ holds for some
natural values of its fresh variables, with every macro read as its relation (masks as bit
inclusion, bitAnd as bitwise conjunction, power as exponentiation, lt as strict
inequality), then $p$ accepts $a$, and its accepting run has exactly $q$ steps.

**Proof sketch.** From $c>0$, $K=2^c$, $B=4K$, $T=B^q$ and the two equations for $F,D$, the
masked-digit statement decodes $R_j=\sum_{t\le q}\rho_j(t)B^t$ with $\rho_j(t)<K$,
$\rho_j(q)=0$, and $S_i=\sum_{t\le q}\sigma_i(t)B^t$ with zero-one digits; $m<B$ and the state
equations give one active state $i_t$ per slot with the halt state $m-1$ active exactly at
$t=q$. The nonzero indicator gives $N_j$ with digits $\nu_j(t)=[\rho_j(t)>0]$, and the branch
statement gives $V_i,W_i$ and the indicator digits. Define the configuration at time
$t\le q$ as $(i_t,\rho(t))$. The state equations (decoded with $e=[i=0]$) give $i_0=0$ and
$i_{t+1}=$ the branch target taken at time $t$; the register equations (decoded with
$\iota_j=a_j<K$ or $0$) give $\rho_j(0)=\iota_j$ and $\rho_j(t+1)=\rho_j(t)+\alpha_j(t)-\gamma_j(t)$,
which is exactly the effect of the instruction at $i_t$ (a decrement happens only when
$\nu_j(t)=1$, that is when $\rho_j(t)>0$). Since the halt state is active only at $t=q$, the
configurations form the run of $p$ from the initial file, it reaches the final state at
time $q$, and there $\rho_j(q)=0$ for all $j$. The extra slot $q+1$ of the register equation,
$\gamma_j(q)=\rho_j(q)+\alpha_j(q)$, is $0=0$ because halt has no outgoing instruction, and the
extra slot of the state equation says $\eta_i(q)=0$ for the same reason. If $q=0$ the state
$0$ is the halt state (so $m=1$) and every input vanishes.

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

- [Section 10.1 packed histories](../../../../sources/compiler-natural-locators.md#section-101-packed-histories)
- [Section 10.1 transition equations](../../../../sources/compiler-natural-locators.md#section-101-transition-equations)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
