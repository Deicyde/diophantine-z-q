---
article_id: af_8eff9af34f8715b871d4c584
declaration: lemma
origin: cited
---

# One interpreter loop is one decoded step

Let $e+1=2^w(2D+1)$ with $w\ge1$ and $B=2^w$. Consider the main-loop body of the interpreter
started in registers holding $D$, $B$, a state $\mathrm{pc}=p$ and a tape code representing the
registers $R$ of the simulated program (scratch registers arbitrary). Then the body
terminates, and

- if the configuration $(p,R)$ is halting for the decoded program of $e$, the body accepts;
- otherwise the body continues with $D$ and $B$ unchanged, $\mathrm{pc}=p'$ and a tape code
  representing $R'$, where $(p',R')=\delta_e(p,R)$ is the decoded step.

**Proof sketch.** Repeated division by $B$ returns the digits $d_{4p},\dots,d_{4p+3}$ of $D$
(zero beyond its length), since division maintains $x=q\,y+r$ with $0\le r<y$ and $B\ge2$.
The opcode test admits exactly $1$ and $2$. By the list-code lemma, $\operatorname{get}$ returns
$R_j$ and $\operatorname{set}$ produces a code representing $R[j\mapsto v]$, so the two branches
implement $\mathrm{inc}(j,k)$ and $\mathrm{decb}(j,k,k')$. Every loop inside the body (division,
halving, the walks of $\operatorname{get}$ and $\operatorname{set}$) strictly decreases a counter, so the
work is finite.

## Depends on

- [The universal interpreter](universal-interpreter.md)
- [The universal program numbering](program-numbering.md)

## Proof depends on

- [List codes for the interpreter tape](list-codes.md)

## Sources

- [Section 10.3 interpreter](../../../../sources/compiler-translation-locators.md#section-103-interpreter)
