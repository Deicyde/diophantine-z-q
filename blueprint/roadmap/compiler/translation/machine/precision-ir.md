---
article_id: af_30bb31bcffb71755576076b3
declaration: def
origin: cited
---

# The precision program

The *precision program* $\mathcal R$ is a total structured register program with the five
inputs $c_0,\dots,c_4$ in registers $0,\dots,4$. It represents a signed integer by a normalized
pair (a sign bit and a magnitude, zero carrying the positive sign), an element of
$\mathbb Z[s]\subset K_0$ by a pair of signed integers over the basis $1,\sqrt2$, and a rational
number by a signed numerator and a positive denominator; the arithmetic of these
representations (sum, difference, product, absolute value, comparison, conjugation, norm) is
written with the primitive statements. It runs as follows; every rejection is final.

1. *Decoding.* Compute $(n,\kappa,a,l,j)=(\operatorname{enc}^{-1}c_0,\dots,\operatorname{enc}^{-1}c_4)$ by
   division by $2$.
2. *Early rejections.* Reject if $n\in\mathcal C$ (six comparisons), $\kappa=0$, $a\le0$, $l\le0$
   or $j\ne na$.
3. *Scalar multiplication.* For $m\in\{l,a,|j|\}$ compute a Jacobian triple of $[m]P_0$ over
   $\mathbb Z[s]$ by the binary method from the fixed triple of $P_0$: keep an accumulator and a
   base, and while the remaining count $k$ is positive, add the base to the accumulator when $k$
   is odd, halve $k$, and double the base when $k$ is still positive. Additions and doublings
   use the Jacobian formulas with their case splits (identity operands, equal abscissas
   splitting into doubling and opposite points, zero ordinate doubling to the identity). If
   $j<0$, negate the ordinate of the triple for $|j|$.
4. *Guards.* Reject unless each of the three triples has $Z\ne0$, $X\ne0$ and $Y\ne0$, each
   tested exactly through the norm of the element of $\mathbb Z[s]$.
5. *Exact values.* From $z=-X Z/Y=-XZ\,\overline Y/\operatorname N(Y)$ compute $u_l,v_l$ and
   $\epsilon_l=U/V$ with natural $U,V\ge1$, and $r(a,j)=\tfrac12\operatorname{Tr}(z_j\overline{z_a})/\operatorname N(z_a)$
   as a fraction; every division is preceded by the exact nonzero test of its denominator.
6. *First test.* Reject unless $|r(a,j)-n|<\epsilon_l$, compared after multiplying by the positive
   denominators.
7. *Second test.* Put $L=\lfloor(V-1)/(4U)\rfloor$. Compute $\beta=\sigma_L\bigl(A^{(0)}_{\rm ht}\,|\kappa F(n)|^{24}\bigr)$ by
   capped evaluation of the defining expression of $A^{(0)}_{\rm ht}$ (factorial, powers, products,
   sums and maximum, each followed by $\sigma_L$) and of the capped power. Then the precision loop
   divides a remainder, initially $L$, by four $\beta$ times, stopping early at zero; accept iff the
   final remainder is positive, and reject otherwise.

The scalar loop halves its count, the precision loop runs at most $L+1$ times, and the capped
evaluation has a fixed number of operations with intermediate values at most $L+1$ or a
literal. This is a definition.

## Depends on

- [Structured register programs](structured-programs.md)
- [The precision predicate](precision-predicate.md)
- [Jacobian formulas for the group law](jacobian-formulas.md)
- [The fixed Jacobian triple of the generator](projective-generator.md)

## Sources

- [Section 10.3 precision IR](../../../../sources/compiler-translation-locators.md#section-103-precision-ir)
- [Section 10 opening](../../../../sources/compiler-translation-locators.md#section-10-opening)
- [Machine artifacts](../../../../sources/compiler-translation-locators.md#machine-artifacts)
