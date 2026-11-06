---
article_id: af_2b2e723387ed825e28336723
declaration: theorem
origin: cited
---

# Capped arithmetic routines

Fix a register holding a cap $L\ge1$. There are statements of the ideal register language
computing, on natural operands, the saturated sum $\sigma_L(x+y)$, the capped product
$\mathrm{cmul}_L$, the saturated maximum, the capped power $\mathrm{cpow}_L$ (binary
exponentiation loop), the saturated factorial $\sigma_L(n!)$ (a loop of $n$ capped
multiplications), the capped value $\langle e_A\rangle_L$ of the precision height constant, the capped bound $\beta$ of the
capped precision test, and the division-by-four loop with its final test. Each terminates
normally with the value prescribed by the corresponding mathematical definition and leaves
every other register unchanged.

**Proof sketch.** Each statement is a direct transcription of its definition; loops are
verified by their invariants (binary exponentiation by the accumulator invariant, the
factorial loop by induction on the counter, the division loop by $x_i=\lfloor L/4^i\rfloor$),
with termination by the halving exponent, the decreasing counter and the step count at
most $L+1$.

## Depends on

- [The ideal register language](structured-programs.md)
- [Capped multiplication and binary exponentiation](../precision/capped-power.md)
- [The capped precision test](../precision/capped-height-test.md)

## Sources

- [Section 10.3 precision IR](../../../../sources/compiler-natural-locators.md#section-103-precision-ir)
- [Section 10 saturation](../../../../sources/compiler-natural-locators.md#section-10-saturation)
