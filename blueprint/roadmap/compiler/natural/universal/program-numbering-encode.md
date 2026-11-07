---
article_id: af_053ece06eb96df2e342e81a5
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Universal.decodeMachine_code, ZInQ.Compiler.Universal.halts_code_iff, ZInQ.Compiler.Universal.code_lt, ZInQ.Compiler.Universal.code_ge
---

# Codes of primitive programs

Let $p$ be a primitive program with $m$ instructions, valid for $r$ registers. Then
$\mu_{\operatorname{code}(p)}(i)=p_i$ for every $i<m$ and $\mu_{\operatorname{code}(p)}(i)=\mathrm{halt}$ for
$i\ge m$. Consequently, for every $n\in\mathbb N$,
$$\operatorname{halts}(\operatorname{code}(p),n)\iff p\text{ halts on the one input }n .$$
Moreover $\operatorname{code}(p)<2^{w(p)(4m+1)+1}$, and if $m\ge2$ then
$\operatorname{code}(p)+1\ge2^{w(p)(4m-7)+1}$.

**Proof sketch.** $\operatorname{code}(p)+1=2^{w}(2D+1)$ with $2D+1$ odd, so decoding recovers
$w=w(p)\ge2$ and $D=D(p)$. All fields are below $2^w$, so the base-$2^w$ digits of $D$ are
exactly the fields, and digits beyond position $4m$ are zero. The opcode fields $1,2,0$ decode
to $\mathrm{inc}$, $\mathrm{dec}$, $\mathrm{halt}$ with the same register and targets (note $2<2^w$ as
$w\ge2$). Hence the two machines agree, and since every target of $p$ is below $m$ the runs
agree and halt at the same time (only at state $m-1$). The bounds: $D<2^{4wm}$, and for $m\ge2$ the instruction $p_{m-2}$ is not a halt, so its
opcode digit at position $4(m-2)$ is at least $1$ and $D\ge2^{4w(m-2)}$.

## Depends on

- [The universal program numbering](program-numbering.md)
- [Register machines](../programs/register-machine.md)

## Sources

- [Section 10.3 numbering](../../../../sources/compiler-natural-locators.md#section-103-numbering)
