---
article_id: af_9b7e4028733f6fe75bad7238
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Precision.NExpr.capped_eq, ZInQ.Compiler.Precision.cappedBound_eq, ZInQ.Compiler.Precision.precision_test_iff
---

# The capped precision test

*Expressions.* Natural-number expressions are built from natural literals with $+$, $\cdot$,
$\max$, powers $e_1^{e_2}$ and factorials $e!$; $[\![e]\!]\in\mathbb N$ is the value. For
$L\in\mathbb N$ the *capped value* $\langle e\rangle_L$ is defined by recursion on $e$:
$\langle c\rangle_L=\sigma_L(c)$ for a literal $c$;
$\langle e_1+e_2\rangle_L=\sigma_L(\langle e_1\rangle_L+\langle e_2\rangle_L)$;
$\langle e_1\cdot e_2\rangle_L=\mathrm{cmul}_L(\langle e_1\rangle_L,\langle e_2\rangle_L)$;
$\langle\max(e_1,e_2)\rangle_L=\sigma_L(\max(\langle e_1\rangle_L,\langle e_2\rangle_L))$;
$\langle e_1^{e_2}\rangle_L=\mathrm{cpow}_L(\langle e_1\rangle_L,\langle e_2\rangle_L)$; and
$\langle e!\rangle_L=f_L(\langle e\rangle_L)$, where $f_L(0)=1$ and
$f_L(n+1)=\mathrm{cmul}_L(f_L(n),\sigma_L(n+1))$ (a loop of $n$ capped multiplications).

*The precision expressions.* Let $e_A$ be the expression of the precision height constant
written with the literals displayed there:
$e_{F_0}=324!$, $e_D=e_{F_0}\cdot3^{256\cdot e_{F_0}^4}$, $e_{G_0}=116064000000$,
$e_{E_0}=10\cdot(e_D\cdot e_{G_0})^2$, $e_{Q_0}=e_D^{\,e_D\cdot e_{E_0}}$,
$e_{B}=e_D^2\cdot3^{21000\cdot e_D^2}+1$, $e_{C}=2\cdot e_B+4096\cdot(1028+5\cdot e_D+84000\cdot e_D^2)$ and
$e_A=2\cdot10^{13}\cdot\max(1,\max(e_C,e_{Q_0}^{17}))$ (here $10^{13}$ is the literal
$10000000000000$). So $[\![e_A]\!]=A^{(0)}_{\rm ht}$.

Let $L\ge1$ and $M\in\mathbb N$. Put
$$\beta=\mathrm{cmul}_L\bigl(\langle e_A\rangle_L,\ \mathrm{cpow}_L(\sigma_L(M),24)\bigr)$$
and run the *division-by-four loop*: $x_0=L$, $x_{i+1}=\lfloor x_i/4\rfloor$, stopping after
$\beta$ steps. Then:

1. $\langle e\rangle_L=\sigma_L([\![e]\!])$ for every expression $e$; in particular
   $\langle e_A\rangle_L=\sigma_L(A^{(0)}_{\rm ht})$;
2. $\beta=\sigma_L(A^{(0)}_{\rm ht}M^{24})$;
3. $x_\beta=\lfloor L/4^\beta\rfloor$, and $x_\beta\ge1\iff4^{A^{(0)}_{\rm ht}M^{24}}\le L$.

Moreover $\beta\le L+1$, so the loop takes at most $L+1$ steps, and every capped value
$\langle e\rangle_L$ is at most $L+1$: nothing astronomically large is computed.

**Proof sketch.** (1) Induction on $e$. Literals by definition. For $+$, $\max$: the
saturation identities $\sigma_L(\sigma_L(x)+\sigma_L(y))=\sigma_L(x+y)$ and the same for
$\max$. For $\cdot$: $\mathrm{cmul}_L(a,b)=\sigma_L(ab)$, then
$\sigma_L(\sigma_L(x)\sigma_L(y))=\sigma_L(xy)$. For powers:
$\mathrm{cpow}_L(a,b)=\sigma_L(a^b)$ and $\sigma_L(\sigma_L(x)^{\sigma_L(n)})=\sigma_L(x^n)$, which
needs $L\ge1$. For factorials: by induction on $n$, $f_L(n)=\sigma_L(n!)$ (item 5 of the
saturation statement), and $f_L(\sigma_L(n))=\sigma_L(n!)$ because for $n\ge L+1$ both
$n!$ and $(L+1)!$ are at least $L+1$. (2) By (1), the capped power and the capped product,
$\beta=\sigma_L(\sigma_L(A^{(0)}_{\rm ht})\cdot\sigma_L(M^{24}))=\sigma_L(A^{(0)}_{\rm ht}M^{24})$.
(3) $\lfloor\lfloor x/4\rfloor/4^i\rfloor=\lfloor x/4^{i+1}\rfloor$ gives
$x_i=\lfloor L/4^i\rfloor$, and $\lfloor L/4^\beta\rfloor\ge1\iff4^\beta\le L$. Put
$B=A^{(0)}_{\rm ht}M^{24}$. If $B\le L$ then $\beta=B$. Otherwise $\beta=L+1$, and both
$4^{L+1}\le L$ and $4^B\le L$ are false, since $4^x>x$ for every $x$ and $B>L$.

## Depends on

- [The precision height constant](precision-height-constant.md)
- [Saturated arithmetic](saturated-arithmetic.md)
- [Capped multiplication and binary exponentiation](capped-power.md)

## Sources

- [Section 10 saturation](../../../../sources/compiler-natural-locators.md#section-10-saturation)
- [Section 10 reference program and IR](../../../../sources/compiler-natural-locators.md#section-10-reference-program-and-ir)
- [Section 10.3 precision IR](../../../../sources/compiler-natural-locators.md#section-103-precision-ir)
