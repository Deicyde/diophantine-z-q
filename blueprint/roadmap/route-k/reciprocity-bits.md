---
article_id: af_cca9419705159051a93f64eb
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.legBit_reciprocity, ZInQ.RouteK.lamBit_eq, ZInQ.RouteK.muBit_eq, ZInQ.RouteK.legBit_mul, ZInQ.RouteK.legBit_prod, ZInQ.RouteK.legBit_eq_zero_iff, ZInQ.RouteK.legBit_symm_of_one_mod_four, ZInQ.RouteK.legBit_symm_of_three_mod_four, ZInQ.RouteK.legBit_eq_iff_legendreSym, ZInQ.RouteK.natCast_zmod_ne_zero_of_prime_ne
---

# Quadratic reciprocity in residue bits

Let $p\ne q$ be odd primes. Then
$$[q/p]+[p/q]=\lambda_p\lambda_q,\qquad\lambda_p=[p\equiv3\pmod4],\qquad
\mu_p=[p\equiv3,5\pmod8],$$
and $[ab/p]=[a/p]+[b/p]$ for integers $a,b$ prime to $p$ (so the bit of a finite product of
integers prime to $p$ is the sum of their bits). For $a$ prime to $p$, $[a/p]=0$ if and only if
$(a/p)=1$; more generally, for $b\in\mathbb F_2$, $[a/p]=b$ if and only if $(a/p)=(-1)^b$. A prime
$q\ne p$ is prime to $p$.

These are quadratic reciprocity, its two supplementary laws and the multiplicativity of the
Legendre symbol, rewritten in $\mathbb F_2$. In particular, for a prime $r\equiv1\pmod4$ the bits
are symmetric, $[y/r]=[r/y]$, and for $q\equiv3\pmod4$, $[y/q]=[q/y]+\lambda_y$.

**Proof sketch.** Quadratic reciprocity gives $(q/p)(p/q)=(-1)^{\frac{p-1}2\frac{q-1}2}$, the
first supplement $(-1/p)=(-1)^{(p-1)/2}$ and the second $(2/p)=1$ exactly when
$p\equiv\pm1\pmod8$. Taking the bits of these $\pm1$ identities turns products into sums.

## Depends on

- [Residue bits](residue-bits.md)

## Sources

- [Slots](../../sources/route-k-locators.md#slots)
