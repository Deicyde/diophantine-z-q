---
article_id: af_384081d5fc94326347f96838
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Compiler.Universal.interpreter
---

# The universal interpreter

The *universal interpreter* $\mathcal U$ is a primitive program with $2$ inputs ($e$ in
register $0$, $n$ in register $1$), reserved jump register $2$, valid for $204$ registers,
assembled from the arithmetic and list blocks. It performs:

1. *Decode the number.* Compute $w$ and $D$ with $e+1=2^w(2D+1)$ by repeated halving of
   $e+1$. If $w=0$, go to cleanup. Otherwise set $\beta=2^w$.
2. *Initialize.* Set the tape to $\operatorname{cons}(n,\operatorname{nil})$ (the virtual file
   with $n$ in register $0$) and the virtual state $\mathrm{pc}=0$.
3. *Main loop.* Extract the base-$\beta$ digits $o,j,x,y$ of $D$ at positions
   $4\mathrm{pc},\dots,4\mathrm{pc}+3$ by repeated division. If $o=1$: replace entry $j$ of the
   tape by its successor and set $\mathrm{pc}=x$. If $o=2$: read $v=\operatorname{get}(\text{tape},j)$;
   if $v>0$ write $v-1$ and set $\mathrm{pc}=x$, else write $v=0$ back and set $\mathrm{pc}=y$
   (the entry is always written with setList, which may pad the tape with zeros). Otherwise
   leave the loop (a simulated halt). Return to the start of the loop.
4. *Cleanup.* Clear all $204$ registers and reach the final halt.

Its shape, recorded in the interpreter-shape statement, is $1{,}399$ instructions
($1{,}022$ sub instructions, $376$ add instructions and the final halt) over $204$ registers.
The manuscript's interpreter is pinned only through its compiled polynomial; its program
is recoverable from the saved universal circuit (state and register histories carry their
indices), and the Lean definition is required to reproduce it exactly, so that the counts
of the compiled circuit are those of the specification.

This is a definition.

## Depends on

- [Register machines](../programs/register-machine.md)
- [The universal program numbering](program-numbering.md)
- [Tape lists](tape-lists.md)

## Sources

- [Section 10.3 interpreter](../../../../sources/compiler-natural-locators.md#section-103-interpreter)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
- [Saved precision polynomial](../../../../sources/compiler-natural-locators.md#saved-precision-polynomial)
