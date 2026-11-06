---
article_id: af_baf48f90ae4938958835028b
declaration: def
origin: bridged
---

# Structured register programs

A *structured register program* $S$ acts on registers $R:\mathbb N\to\mathbb N$ of finite support. Its
statements are

- the primitive statements $r:=0$, $r:=r+1$, $r:=r\mathbin{\dot-}1$ (saturating decrement),
  $r:=r'$, $r:=r'+r''$, $r:=r'\mathbin{\dot-}r''$ (natural subtraction), $r:=r'\cdot r''$ and the
  guarded division $(q,m):=\operatorname{divmod}(r',r'')$;
- sequencing $S_1;S_2$, the tests $\mathbf{if}\ r=0\ \mathbf{then}\ S_1\ \mathbf{else}\ S_2$ and
  $\mathbf{if}\ r<r'\ \mathbf{then}\ S_1\ \mathbf{else}\ S_2$, and the loop
  $\mathbf{while}\ r\ne0\ \mathbf{do}\ S_1$;
- $\mathbf{accept}$ and $\mathbf{reject}$.

The right-hand side of a primitive statement is evaluated in the old registers before the
destination is written, so a destination may coincide with a source. The division sets
$q=\lfloor R_{r'}/R_{r''}\rfloor$ and $m=R_{r'}\bmod R_{r''}$ when $R_{r''}\ge1$ and behaves as
$\mathbf{reject}$ when $R_{r''}=0$ (every variable division is guarded).

*Semantics.* The big-step relation $S,R\Downarrow o$ has outcomes $o=\mathrm{cont}(R')$,
$\mathrm{acc}(R')$ and $\mathrm{rej}(R')$, defined by the usual rules: primitive statements continue
with the updated registers, $\mathbf{accept}$ and $\mathbf{reject}$ stop, a sequence or loop
propagates a stop outcome, and $\mathbf{while}$ repeats its body while the tested register is
positive. A terminating execution is a finite derivation; no derivation means divergence.
$S$ *accepts* $\mathbf x\in\mathbb N^t$ when $S,R^{\mathbf x}\Downarrow\mathrm{acc}(R')$ for some $R'$, and
*rejects* $\mathbf x$ when it ends with $\mathrm{rej}$ or $\mathrm{cont}$ (falling off the end is
rejection). $S$ is *total* when every input has an outcome. The registers of $S$ are the
indices it mentions; $N_S$ denotes one more than the largest of them.

This is a definition. It is the ideal register intermediate representation of the
manuscript, in which both the precision program and the universal interpreter are written.

## Depends on

- [Primitive register programs](register-programs.md)

## Sources

- [Section 10.3 lowering](../../../../sources/compiler-translation-locators.md#section-103-lowering)
- [Section 10.3 interpreter](../../../../sources/compiler-translation-locators.md#section-103-interpreter)
- [Section 10 opening](../../../../sources/compiler-translation-locators.md#section-10-opening)
