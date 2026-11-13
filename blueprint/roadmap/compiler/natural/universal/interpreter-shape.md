---
article_id: af_a945a7f11fab24d207628760
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Universal.interpreter_shape
---

# Shape of the universal interpreter

The universal interpreter $\mathcal U$ satisfies the following closed decidable statements:

1. it is valid for $204$ registers: it has $m=1{,}399$ instructions, its final instruction
   (state $1398$) is its only halt, every register index is below $204$ and every target is
   below $1{,}399$;
2. it has $s=1{,}022$ sub instructions and $376$ add instructions;
3. its *cleanup stage* is the block of states $1194,\dots,1398$: for $0\le j<204$ the
   instruction at state $1194+j$ is $\mathrm{dec}(j,\,1194+j,\,1195+j)$, and state $1398$ is
   the final halt;
4. the states below $1194$ having a target at least $1194$ are exactly $69$, $587$ and
   $593$, and each of them is $\mathrm{dec}(2,1194,1194)$ (an unconditional jump to the first
   cleanup state through the jump register $2$).

In the structured definition of $\mathcal U$, state $69$ is the exit of the decoding step on
$w=0$ and states $587$, $593$ are the exits of the main loop on a simulated halt; items 3
and 4 are what the correctness proof uses to say that the final halt is reached only
through cleanup. The numbers are those of the manuscript's interpreter, recovered from the
saved universal circuit (its state and register histories carry their indices); the Lean
definition is required to reproduce them.

This is a finite computation on the explicit $1{,}399$-instruction program.

## Depends on

- [The universal interpreter](universal-interpreter.md)
- [Register machines](../programs/register-machine.md)

## Sources

- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
- [Saved precision polynomial](../../../../sources/compiler-natural-locators.md#saved-precision-polynomial)
