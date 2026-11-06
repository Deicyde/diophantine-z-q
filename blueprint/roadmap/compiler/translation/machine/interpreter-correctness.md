---
article_id: af_e22821da89135f1eed147ccf
declaration: theorem
origin: cited
---

# Correctness of the universal interpreter

For all $e,n\in\mathbb N$,
$$U\text{ accepts }(e,n)\iff\text{the decoded program of }e\text{ halts on }n .$$
The final registers of the simulated program are not required to be zero: the all-zero halt
of $U$ is equivalent to virtual halting of the decoded program.

**Proof sketch.** By the lowering theorem, $U$ accepts $(e,n)$ iff $\mathcal I$ accepts $(e,n)$.
If $w=0$, the decoded program halts at once and $\mathcal I$ accepts in step 1. Let $w\ge1$. The
initial tape $\langle n\rangle$ represents the initial registers $R$ with $R_0=n$. If the decoded
program halts after $t$ steps, induction on $t$ with the one-step lemma shows that $\mathcal I$
reaches the main loop with the configuration after $t$ steps and then accepts. Conversely, an
accepting execution of $\mathcal I$ runs the main loop finitely often; by the one-step lemma
each iteration simulates one decoded step and the accepting iteration reads a halting
configuration, so the decoded program halts. $\mathcal I$ never rejects, so an infinite
simulation is a divergence of $\mathcal I$, and $U$ never reaches its cleanup.

## Depends on

- [The universal interpreter](universal-interpreter.md)
- [The universal program numbering](program-numbering.md)

## Proof depends on

- [One interpreter loop is one decoded step](interpreter-step.md)
- [The lowered machine halts exactly on acceptance](lowering-correctness.md)

## Sources

- [Section 10.3 interpreter](../../../../sources/compiler-translation-locators.md#section-103-interpreter)
- [Machine artifacts](../../../../sources/compiler-translation-locators.md#machine-artifacts)
