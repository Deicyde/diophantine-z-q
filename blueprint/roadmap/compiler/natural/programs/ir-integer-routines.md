---
article_id: af_23bb5ec991f934818f3efb30
declaration: theorem
origin: cited
---

# Signed integer routines

An integer $z$ is *represented* by a pair of registers $(\sigma,\mu)$ when $\mu=|z|$ and
$\sigma=[z<0]$; the representation is *normalized*: zero has $\sigma=0$, so each integer has
exactly one representation. There are statements of the ideal register language,
parameterized by the registers of their operands, results and temporaries, for:
decoding a natural $c$ into the representation of $\operatorname{dec}(c)$ ($\sigma=c\bmod2$,
$\mu=\lfloor(c+\sigma)/2\rfloor$); negation; absolute value; addition; subtraction;
multiplication; multiplication by a constant; the tests $z_1<z_2$, $z_1=z_2$ and $z=0$
(as branches); and multiplication of two naturals into a signed result. For each of them:
started from any file in which the operand pairs represent integers $z_1,z_2$ and the
temporaries are distinct from operands and results, the statement terminates normally,
the result pair represents the corresponding integer ($-z_1$, $|z_1|$, $z_1+z_2$, $z_1-z_2$,
$z_1z_2$, ...), the branch taken is the true one, and every register other than results and
temporaries is unchanged. Results may alias operands.

**Proof sketch.** Each routine is a case split on the signs with natural arithmetic on the
magnitudes: for addition, equal signs add magnitudes, opposite signs subtract the smaller
magnitude from the larger and take the sign of the larger, and a zero result gets
$\sigma=0$; multiplication multiplies magnitudes and sets $\sigma=\sigma_1\oplus\sigma_2$ unless the
product is zero. Each case is verified by the big-step rules and arithmetic in $\mathbb Z$;
aliasing is handled by computing into temporaries first.

## Depends on

- [The ideal register language](structured-programs.md)
- [The signed encoding of integers](../precision/signed-encoding.md)

## Sources

- [Section 10.3 precision IR](../../../../sources/compiler-natural-locators.md#section-103-precision-ir)
- [Section 10 reference program and IR](../../../../sources/compiler-natural-locators.md#section-10-reference-program-and-ir)
