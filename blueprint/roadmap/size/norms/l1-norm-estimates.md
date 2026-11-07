---
article_id: af_4d9990ab76ff6b53fb0dc78e
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Size.l1_estimates
---

# Elementary estimates for the coefficient norm

For $f,g\in\mathbb Z[X_i:i\in I]$, $c\in\mathbb Z$, $i\in I$ and $k\in\mathbb N$:

1. $|[X^\alpha]f|\le\|f\|_1$ for every monomial $X^\alpha$, and $\|f\|_1=0$ only for $f=0$;
2. $\|c\|_1=|c|$ for the constant $c$, $\|X_i\|_1=1$, $\|-f\|_1=\|f\|_1$, $\|cf\|_1=|c|\,\|f\|_1$;
3. $\|f+g\|_1\le\|f\|_1+\|g\|_1$ and $\|fg\|_1\le\|f\|_1\|g\|_1$, hence
   $\|f^k\|_1\le\|f\|_1^k$, and the same for finite sums and products;
4. $\deg(f+g)\le\max(\deg f,\deg g)$, $\deg(fg)\le\deg f+\deg g$, $\deg f^k\le k\deg f$,
   $\deg c=0$ and $\deg X_i\le1$.

**Proof sketch.** (1)-(2) from the definition. For the product, the coefficient of
$X^\gamma$ in $fg$ is $\sum_{\alpha+\beta=\gamma}a_\alpha b_\beta$, so
$\|fg\|_1\le\sum_\gamma\sum_{\alpha+\beta=\gamma}|a_\alpha||b_\beta|=\|f\|_1\|g\|_1$. Degrees are
standard.

## Depends on

- [Coefficient norms and degrees](l1-norm.md)

## Sources

- [Section 12.1 norms and division polynomials](../../../sources/size-locators.md#section-121-norms-and-division-polynomials)
