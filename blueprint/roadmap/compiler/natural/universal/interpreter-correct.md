---
article_id: af_a2cb0a59a5bbc0318db98e86
declaration: theorem
origin: cited
---

# Correctness of the universal interpreter

For all $e,n\in\mathbb N$:
$$\mathcal U\text{ accepts }(e,n)\iff\operatorname{halts}(e,n).$$
That is, the interpreter reaches its final halt with all $204$ registers zero exactly when
the program numbered $e$ halts on $n$; the virtual final tape need not be zero.

**Proof sketch.** If $w=0$, both sides hold (the decoding step goes to cleanup; $\mu_e$ halts
at once). Let $w\ge1$. After decoding and initialization, the run is coherent with the
initial virtual configuration. ($\Leftarrow$) If the virtual run halts after $t$ steps, $t$
applications of the step statement reach a configuration coherent with a halting virtual
state, from which cleanup is reached; cleanup clears every register and halts.
($\Rightarrow$) The final halt is reachable only through cleanup, which is entered only from
the decoding step with $w=0$ or from a simulated halt (items 3 and 4 of the shape check:
the cleanup stage is a straight run of clearing loops ending at the final halt, entered only
at its first state, and only from the three exit states); by the step statement, if the
virtual run never halts the interpreter returns to the main loop forever and never
enters cleanup. Hence acceptance implies virtual halting.

## Depends on

- [The universal interpreter](universal-interpreter.md)
- [The universal program numbering](program-numbering.md)
- [Register machines](../programs/register-machine.md)

## Proof depends on

- [One interpreter loop simulates one instruction](interpreter-step.md)
- [Arithmetic blocks of the interpreter](interpreter-primitives.md)
- [List blocks of the interpreter](interpreter-list-primitives.md)
- [Shape of the universal interpreter](interpreter-shape.md)

## Sources

- [Section 10.3 interpreter](../../../../sources/compiler-natural-locators.md#section-103-interpreter)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
