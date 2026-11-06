---
article_id: af_9167b2d205b1fb00057ec7ea
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Precision.cappedArithmetic
---

# Capped multiplication and binary exponentiation

For $L\in\mathbb N$ define capped multiplication by $\mathrm{cmul}_L(a,b)=0$ if $a=0$ or
$b=0$, $L+1$ if $a>\lfloor L/b\rfloor$, and $ab$ otherwise; and capped binary exponentiation
$\mathrm{cpow}_L(x,e)$ by: $1$ if $e=0$; $x$ if $x\le1$; otherwise run the loop with state
$(\beta,e,\pi)$ starting from $(x,e,1)$: if $e=0$ return $\pi$; if $\beta>L$ return $L+1$; put
$\pi'=\mathrm{cmul}_L(\pi,\beta)$ if $e$ is odd and $\pi'=\pi$ otherwise; if $e$ is odd and
$\pi'=L+1$ return $L+1$; if $\lfloor e/2\rfloor=0$ return $\pi'$; else continue with
$(\mathrm{cmul}_L(\beta,\beta),\lfloor e/2\rfloor,\pi')$. Then for all natural $L,a,b,x,e$:
$$\mathrm{cmul}_L(a,b)=\sigma_L(ab),\qquad\mathrm{cpow}_L(x,e)=\sigma_L(x^e),$$
and $\mathrm{cpow}_L(x,e)\le L\iff x^e\le L$. The loop terminates because $e$ halves.

**Proof sketch.** For $b>0$, $a>\lfloor L/b\rfloor\iff ab>L$. For the loop, prove by strong
induction on $e$ the invariant $\mathrm{loop}(\beta,e,\pi)=\sigma_L(\pi\beta^e)$ for $\beta\ge1$,
$1\le\pi\le L+1$, using $\beta^e=\beta^{e\bmod2}(\beta^2)^{\lfloor e/2\rfloor}$ and the
saturation identities; the early returns are justified because $\beta>L$ or $\pi'=L+1$ force
$\sigma_L(\pi\beta^e)=L+1$. The initial cases are $x^0=1$, $0^e=0$, $1^e=1$ for $e>0$.

## Depends on

- [Saturated arithmetic](saturated-arithmetic.md)

## Sources

- [Section 10 saturation](../../../../sources/compiler-natural-locators.md#section-10-saturation)
- [Section 10.3 precision IR](../../../../sources/compiler-natural-locators.md#section-103-precision-ir)
