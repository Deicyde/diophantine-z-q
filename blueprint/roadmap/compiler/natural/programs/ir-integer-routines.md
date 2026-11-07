---
article_id: af_23bb5ec991f934818f3efb30
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.IR.SInt, ZInQ.Compiler.IR.ReprInt, ZInQ.Compiler.IR.sConst, ZInQ.Compiler.IR.sCopy, ZInQ.Compiler.IR.sNeg, ZInQ.Compiler.IR.sAbs, ZInQ.Compiler.IR.sAdd, ZInQ.Compiler.IR.sSub, ZInQ.Compiler.IR.sMul, ZInQ.Compiler.IR.sDiv, ZInQ.Compiler.IR.sMod, ZInQ.Compiler.IR.sLtFlag, ZInQ.Compiler.IR.sEqFlag, ZInQ.Compiler.IR.SContract
---

# Signed integer routines

An integer $z$ is *represented* by a pair of registers $(\sigma,\mu)$ when $\mu=|z|$ and
$\sigma=[z<0]$; the representation is *normalized*: zero has $\sigma=0$, so each integer has
exactly one representation. There are statements of the ideal register language,
parameterized by the registers of their operands and results and by a temporary base $t$
(they use the registers $t,t+1,\dots$ as temporaries), for: decoding a natural $c$ into the
representation of $\operatorname{dec}(c)$ ($\sigma=c\bmod2$, $\mu=\lfloor(c+\sigma)/2\rfloor$); an
integer constant; copying; negation; absolute value; addition; subtraction;
multiplication; the natural quotient $\lfloor|z_1|/|z_2|\rfloor$ and remainder
$|z_1|\bmod|z_2|$; an assignment with natural value (such as $|z_1|\cdot|z_2|$) written into
a signed result; and the flags $[z_1<z_2]$ and $[z_1=z_2]$. For each routine with a signed
result: if the operand and result registers lie below $t$, the two result registers are
distinct, and in the starting file the operand pairs represent integers $z_1,z_2$, the
statement terminates normally, the result pair represents the corresponding integer
($\operatorname{dec}(c)$, $z_1$, $-z_1$, $|z_1|$, $z_1+z_2$, $z_1-z_2$, $z_1z_2$, ...), and every
register below $t$ other than the two result registers is unchanged. Results may alias
operands. For the flags: if the flag register differs from the operand registers, the
statement terminates normally with the flag equal to $1$ if the relation holds and $0$
otherwise, and every other register unchanged.

These routines compile statements over integer variables (assignments of the operations
above, conditionals on $z_1<z_2$ or $z_1=z_2$, which compute the flag into a temporary and
branch on it, conditionals on $|z_1|<|z_2|$ or $|z_1|=|z_2|$, which branch on the magnitude
registers, loops while $|z_1|<|z_2|$, $\mathbf{accept}$ and $\mathbf{reject}$), integer variable
$k$ being held in the pair $(o+2k,o+2k+1)$ for an offset $o$: if every variable occurring
is below $K$ and $o+2K\le t$, and the pairs of the variables below $K$ represent an integer
environment, the compiled statement has the outcome of the integer statement, and on
normal termination the pairs represent the final environment.

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
