---
article_id: af_78597754145c35c23b6e471c
declaration: def
origin: cited
---

# The universal program numbering

Every $e\in\mathbb N$ is written uniquely as $e+1=2^w(2D+1)$ with $w,D\in\mathbb N$. Put $B=2^w$ and,
for $w\ge1$, let $d_i=\lfloor D/B^i\rfloor\bmod B$ be the $i$-th base-$B$ digit of $D$ ($d_i=0$
for $B^i>D$). The *decoded program* of $e$ is the transition function $\delta_e$ on
configurations $(p,R)$ defined as follows.

- If $w=0$, every configuration is halting.
- If $w\ge1$, read $(o,j,k,k')=(d_{4p},d_{4p+1},d_{4p+2},d_{4p+3})$ at state $p$. If $o=1$, the
  step is that of $\mathrm{inc}(j,k)$; if $o=2$, that of $\mathrm{decb}(j,k,k')$; for every other
  opcode $o$ the configuration is halting.

The decoded program of $e$ *halts on $n$* when iterating $\delta_e$ from $(0,R)$ with $R_0=n$
and $R_i=0$ for $i\ge1$ reaches a halting configuration.

*Encoding.* For a primitive register program $\Pi=(I_0,\dots,I_{m-1})$ let $w\ge1$ be least
with $2^w>2$ and $2^w$ greater than every register index and target of $\Pi$, and $B=2^w$. Give
$I_p$ the digits $(1,j,k,0)$ for $\mathrm{inc}(j,k)$, $(2,j,k,k')$ for $\mathrm{decb}(j,k,k')$ and
$(0,0,0,0)$ for $\mathrm{halt}$, put $D=\sum_{p<m}\sum_{i<4}(\text{digit }i\text{ of }I_p)\,B^{4p+i}$ and
$$\operatorname{code}(\Pi)=2^w(2D+1)-1 .$$

Decoding is total: missing digits are zero, so every state of every $e$ has a defined
transition or halts. This is a definition.

## Depends on

- [Primitive register programs](register-programs.md)

## Sources

- [Section 10.3 program numbering](../../../../sources/compiler-translation-locators.md#section-103-program-numbering)
- [Machine artifacts](../../../../sources/compiler-translation-locators.md#machine-artifacts)
