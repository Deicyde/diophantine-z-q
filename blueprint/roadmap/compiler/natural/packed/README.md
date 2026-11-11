---
article_id: af_09a9eac70b552e067c9193a7
---

# The packed-history compiler

A primitive program with $m$ instructions over $r$ registers is compiled by packing a run of
length $q$ into base-$B$ integers, with $K=2^c$, $B=4K>m$, $T=B^q$, $F_q=1+B+\dots+B^q$ and
$D=(K-1)F_q$, every input being below $K$.

- [The packed-history construction](packed-compiler.md)

Masks by $D$ and $F_q$ and the bound $R_j<T$ make register digits smaller than $K$ with a zero
final digit, and state digits zero or one; since $B>m$ the state sum selects exactly one
state at each time.

- [Digits of masked histories](packed-masks.md)
- [One active state per time slot](packed-state-selection.md)

The nonzero indicator is read off one bit per slot of $R_j+D$, and a sub instruction splits
its state history into nonzero and zero branch histories; the increment, decrement and
incoming indicators then have zero-one digits.

- [The packed nonzero indicator](packed-nonzero-indicator.md)
- [Branch histories and indicator digits](packed-branches.md)

The register and state equations have all coefficients below $B$, so uniqueness of base-$B$
digits turns them into the initial conditions and the exact transitions, the extra final
slot vanishing.

- [Decoding the transition equations](packed-transitions.md)

Every solution decodes to an accepting run, and every accepting run fits once $c$ is large.
The compiled circuit therefore has a natural zero exactly at the accepted inputs.

- [Soundness of the packed-history construction](packed-sound.md)
- [Completeness of the packed-history construction](packed-complete.md)
- [The compiled circuit of a register machine](register-machine-polynomial.md)

The numbers of explicit variables and power calls are linear in $m$, $r$, the number of sub
instructions and the number of inputs.

- [Variable and gadget counts of the packed construction](packed-counts.md)
