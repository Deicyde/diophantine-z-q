---
article_id: af_c4ce10ea32ac26d1c470d7bf
declaration: def
origin: cited
---

# The universal interpreter

The *interpreter* $\mathcal I$ is the structured register program with inputs $e$ (register $0$)
and $n$ (register $1$) that runs as follows.

1. Compute $w$ and $D$ with $e+1=2^w(2D+1)$ by halving $e+1$ while it is even (divisions by
   $2$), and then $D=((e+1)/2^w-1)/2$. If $w=0$, accept.
2. Put $B=2^w$, $\mathrm{tape}=\langle n\rangle=\operatorname{cons}(n,0)$ and $\mathrm{pc}=0$.
3. Main loop: extract the base-$B$ digits $(o,j,k,k')=(d_{4\mathrm{pc}},\dots,d_{4\mathrm{pc}+3})$ of $D$
   by repeated division by $B$ (missing digits come out as $0$). If $o=1$, replace entry $j$ of
   the tape by $\operatorname{get}(\mathrm{tape},j)+1$ and set $\mathrm{pc}=k$. If $o=2$, read
   $v=\operatorname{get}(\mathrm{tape},j)$; if $v>0$ replace entry $j$ by $v-1$ and set $\mathrm{pc}=k$,
   otherwise set $\mathrm{pc}=k'$. For every other $o$, accept. Repeat.

Tape reads and updates use the halving decoder and the reversed-prefix procedure for list
codes. All divisions of $\mathcal I$ are by $2$ or by $B\ge2$, and $\mathcal I$ contains no
$\mathbf{reject}$.

The *universal interpreter* is $U=\operatorname{lower}(\mathcal I)$, a primitive register program in
final-halt form; *$U$ accepts $(e,n)$* means that its run on the two-register input $(e,n)$
reaches the final halt with all registers zero. In the manuscript's construction $U$ has
$1399$ states and $204$ registers; the natural chapter compiles $U$ into the universal halting
polynomial. This is a definition.

## Depends on

- [Structured register programs](structured-programs.md)
- [Lowering to a primitive program](lowering.md)
- [List codes for the interpreter tape](list-codes.md)
- [The universal program numbering](program-numbering.md)

## Sources

- [Section 10.3 interpreter](../../../../sources/compiler-translation-locators.md#section-103-interpreter)
- [Section 10.3 program numbering](../../../../sources/compiler-translation-locators.md#section-103-program-numbering)
- [Machine artifacts](../../../../sources/compiler-translation-locators.md#machine-artifacts)
