---
article_id: af_28bd6f1629a42460f407e8c5
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Compiler.Universal.split2, ZInQ.Compiler.Universal.decodeInstr, ZInQ.Compiler.Universal.decodeMachine, ZInQ.Compiler.Universal.halts, ZInQ.Compiler.Universal.width, ZInQ.Compiler.Universal.code
---

# The universal program numbering

**Decoding.** Every $e\in\mathbb N$ is uniquely $e+1=2^w(2D+1)$ with $w,D\in\mathbb N$. The
machine $\mu_e$ numbered by $e$ is: if $w=0$, $\mu_e(i)=\mathrm{halt}$ for every $i$. Otherwise,
with $\beta=2^w$ and $d_t=\lfloor D/\beta^t\rfloor\bmod\beta$ the base-$\beta$ digits of $D$ (zero
beyond its length), state $i$ reads $(o,j,x,y)=(d_{4i},d_{4i+1},d_{4i+2},d_{4i+3})$ and
$$\mu_e(i)=\mathrm{inc}(j,x)\text{ if }o=1,\qquad\mu_e(i)=\mathrm{dec}(j,x,y)\text{ if }o=2,\qquad
\mu_e(i)=\mathrm{halt}\text{ otherwise}.$$
Decoding is total. *The program numbered $e$ halts on input $n$*, written
$\operatorname{halts}(e,n)$, if the run of $\mu_e$ from state $0$ with $n$ in register $0$ and
all other registers zero halts.

**Encoding.** For a primitive program $p=(p_0,\dots,p_{m-1})$ valid for $r$ registers, let
$w(p)$ be the least $w\ge2$ such that every register index and every target of $p$ is
below $2^w$, let the fields of an instruction be $(1,j,x,0)$ for $\mathrm{inc}(j,x)$,
$(2,j,x,y)$ for $\mathrm{dec}(j,x,y)$ and $(0,0,0,0)$ for the final halt, and put
$$D(p)=\sum_{i<m}\sum_{t<4}f_{i,t}\,2^{w(p)(4i+t)},\qquad
\operatorname{code}(p)=2^{w(p)}\bigl(2D(p)+1\bigr)-1,$$
where $f_{i,0},\dots,f_{i,3}$ are the fields of $p_i$.

This is a definition. The interpreter's numbering is the one specified by the universal
interpreter of the manuscript; the encoding is the canonical choice of $w$ (the
manuscript only requires $w$ large enough for all fields).

## Depends on

- [Register machines](../programs/register-machine.md)

## Sources

- [Section 10.3 numbering](../../../../sources/compiler-natural-locators.md#section-103-numbering)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
