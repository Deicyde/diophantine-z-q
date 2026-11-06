---
article_id: af_d5ce94cef1e9aab84e6a994e
declaration: def
origin: cited
---

# Primitive register programs

A *primitive register program* is a finite list $\Pi=(I_0,\dots,I_{m-1})$ of instructions, each
of one of the forms

- $\mathrm{inc}(j,k)$: increment register $j$ and go to state $k$;
- $\mathrm{decb}(j,k,k')$: if register $j$ is positive, decrement it and go to $k$; otherwise go
  to $k'$;
- $\mathrm{halt}$,

with register indices $j$ and targets $k,k'$ in $\mathbb N$. A *configuration* is a pair $(p,R)$ of a
state $p\in\mathbb N$ and registers $R:\mathbb N\to\mathbb N$ of finite support. The *step* of $\Pi$ sends
$(p,R)$ with $p<m$ and $I_p=\mathrm{inc}(j,k)$ to $(k,R[j\mapsto R_j+1])$, and with
$I_p=\mathrm{decb}(j,k,k')$ to $(k,R[j\mapsto R_j-1])$ if $R_j>0$ and to $(k',R)$ if $R_j=0$. A
configuration with $p\ge m$ or $I_p=\mathrm{halt}$ is *halting* and has no step.

For $\mathbf x=(x_0,\dots,x_{t-1})\in\mathbb N^t$ the *run on $\mathbf x$* starts at $(0,R^{\mathbf x})$ with
$R^{\mathbf x}_i=x_i$ for $i<t$ and $R^{\mathbf x}_i=0$ otherwise, and applies the step as long as it is
defined. $\Pi$ *halts on $\mathbf x$* when the run reaches a halting configuration (after finitely
many steps). $\Pi$ is in *final-halt form* when $I_{m-1}=\mathrm{halt}$ is its only halt
instruction and all its targets are below $m$; such a $\Pi$ *accepts $\mathbf x$* when the run
reaches $(m-1,0)$, the unique final halt with all registers zero. This is the acceptance
convention of the packed-history compiler of the natural chapter; halting at any halt
instruction, with arbitrary final registers, is *virtual halting*.

This is a definition.

## Depends on

None.

## Sources

- [Section 10.1 acceptance](../../../../sources/compiler-translation-locators.md#section-101-cantor-wrapper-and-acceptance)
- [Section 10.3 interpreter](../../../../sources/compiler-translation-locators.md#section-103-interpreter)
- [Machine artifacts](../../../../sources/compiler-translation-locators.md#machine-artifacts)
