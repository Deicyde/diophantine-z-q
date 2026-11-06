---
article_id: af_baffc1518498e1c1e1c81649
declaration: lemma
origin: cited
---

# Decoding a program code

For every primitive register program $\Pi=(I_0,\dots,I_{m-1})$ and every configuration $(p,R)$,
the decoded program of $\operatorname{code}(\Pi)$ has the same transition at $(p,R)$ as $\Pi$:
both are halting, or both step to the same configuration. Consequently, for every $n\in\mathbb N$,
the decoded program of $\operatorname{code}(\Pi)$ halts on $n$ if and only if $\Pi$ halts on the
one-register input $n$, the two runs being identical. Moreover $\operatorname{code}(\Pi)\ge1$,
$\operatorname{code}(\Pi)\ge5$ when $\Pi$ has an instruction other than $\mathrm{halt}$, and
$$\operatorname{code}(\Pi)<2^{\,w(4m+1)+1},$$
where $2^w$ is the base chosen by the encoding.

**Proof sketch.** $\operatorname{code}(\Pi)+1=2^w(2D+1)$ with $2D+1$ odd, so the decomposition of
the numbering returns this $w\ge1$ and $D$ (uniqueness of the $2$-adic factorization). Every
digit of every instruction is below $B=2^w$, so by uniqueness of base-$B$ expansions the digits
$d_i$ of $D$ are exactly the instruction digits at positions $i<4m$ and $0$ at positions
$i\ge4m$. Hence at $p<m$ the decoded opcode, register and targets are those of $I_p$ (opcode
$0$ halts, like $\mathrm{halt}$), and at $p\ge m$ the opcode is $0$ and both programs halt.
Finally $w\ge1$ gives $\operatorname{code}(\Pi)\ge1$, and a nonzero opcode gives $D\ge1$, so
$\operatorname{code}(\Pi)\ge2\cdot3-1$. For the upper bound, every digit is at most $B-1$, so
$D\le B^{4m}-1$, $2D+1<2\cdot2^{4mw}$ and $\operatorname{code}(\Pi)<2^w\cdot2^{4mw+1}$.

## Depends on

- [The universal program numbering](program-numbering.md)

## Sources

- [Section 10.3 program numbering](../../../../sources/compiler-translation-locators.md#section-103-program-numbering)
