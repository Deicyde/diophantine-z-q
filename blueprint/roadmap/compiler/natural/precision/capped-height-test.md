---
article_id: af_9b7e4028733f6fe75bad7238
declaration: theorem
origin: bridged
---

# The capped precision test

Let $L\ge1$ and $M\in\mathbb N$. Define the *capped constant* $\langle A\rangle_L$ by evaluating
the defining expressions of the precision height constant with every operation saturated:
$$\begin{aligned}
\langle F_0\rangle&=\sigma_L(324!)\ \text{(iterated saturated products)},&
\langle D\rangle&=\sigma_L\bigl(\langle F_0\rangle\cdot\mathrm{cpow}_L(3,\sigma_L(256\cdot\mathrm{cpow}_L(\langle F_0\rangle,4)))\bigr),
\end{aligned}$$
and likewise $\langle E_0\rangle$, $\langle Q_0\rangle=\mathrm{cpow}_L(\langle D\rangle,\sigma_L(\langle D\rangle\langle E_0\rangle))$,
$\langle B_{\rm cm}\rangle$, $\langle C_{\rm cm}\rangle$ and
$\langle A\rangle_L=\sigma_L\bigl(\sigma_L(2\cdot10^{13})\cdot\max(1,\langle C_{\rm cm}\rangle,\mathrm{cpow}_L(\langle Q_0\rangle,17))\bigr)$,
where each sum, product and maximum is followed by $\sigma_L$. Put
$\beta=\sigma_L\bigl(\langle A\rangle_L\cdot\mathrm{cpow}_L(\sigma_L(M),24)\bigr)$ and run the
*division-by-four loop*: $x_0=L$, $x_{i+1}=\lfloor x_i/4\rfloor$, stopping after $\beta$ steps.
Then
$$\langle A\rangle_L=\sigma_L(A^{(0)}_{\rm ht}),\qquad\beta=\sigma_L(A^{(0)}_{\rm ht}M^{24}),\qquad
x_\beta\ge1\iff4^{A^{(0)}_{\rm ht}M^{24}}\le L .$$
The loop takes at most $L+1$ steps; nothing astronomically large is computed.

**Proof sketch.** Each capped expression equals $\sigma_L$ of the exact one by the
saturation identities (sums, products, maxima, powers with capped base and exponent, which
needs $L\ge1$, and factorials), applied inductively along the expression; capped
exponentiation is exact by the binary-exponentiation statement. For the loop,
$x_i=\lfloor L/4^i\rfloor$, so $x_\beta\ge1\iff4^\beta\le L$. If
$B:=A^{(0)}_{\rm ht}M^{24}\le L$ then $\beta=B$. Otherwise $\beta=L+1$, and both
$4^{L+1}\le L$ and $4^B\le L$ are false.

## Depends on

- [The precision height constant](precision-height-constant.md)
- [Saturated arithmetic](saturated-arithmetic.md)
- [Capped multiplication and binary exponentiation](capped-power.md)

## Sources

- [Section 10 saturation](../../../../sources/compiler-natural-locators.md#section-10-saturation)
- [Section 10 reference program and IR](../../../../sources/compiler-natural-locators.md#section-10-reference-program-and-ir)
- [Section 10.3 precision IR](../../../../sources/compiler-natural-locators.md#section-103-precision-ir)
