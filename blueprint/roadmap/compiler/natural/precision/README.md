---
article_id: af_6aa68df1fcbe2b34b58c29f2
---

# The exact precision computation

The five natural inputs of the precision computation are signed encodings, decoded in the
fixed order $(n,\kappa,a,l,j)$.

- [The signed encoding of integers](signed-encoding.md)
- [The signed encoding is a bijection](signed-encoding-bijection.md)

The local parameter $z=-x/y$ is defined at multiples of $P_0$ that are affine with nonzero
ordinate; at such an index $k$ it gives the components $u_k,v_k$, the size
$\epsilon_k=|u_k|+|v_k|$, and the trace ratio $r(a,j)$.

- [The local parameter z on multiples of the generator](z-coordinate.md)

The precision exponent uses the six-contact constant for the primes up to $324$, written as
an explicit natural-number expression; it is never evaluated.

- [The precision height constant](precision-height-constant.md)
- [The precision constant is the six-contact constant](precision-height-constant-value.md)

The relation itself consists of the early tests, admissibility, and two strict tests. Given
that $P_0$ has infinite order, admissibility follows from the early tests; the model chapter
proves this unconditionally ([nonzero multiples of the generator](../../../model/descent/nonzero-multiples.md)).

- [The precision relation](precision-relation.md)
- [Admissibility of nonzero indices](precision-guards.md)

## Exact evaluation

The second strict test compares $\epsilon_l=U/V$ with $4^{-\mathcal B}$; it becomes an integer
comparison with the finite cap $L=\lfloor(V-1)/(4U)\rfloor$. Saturating every operation at
$L+1$ computes the comparison exactly without evaluating $\mathcal B$.

- [The precision threshold as an integer comparison](precision-threshold.md)
- [Saturated arithmetic](saturated-arithmetic.md)
- [Capped multiplication and binary exponentiation](capped-power.md)
- [The capped precision test](capped-height-test.md)

Field divisions are guarded by the norm, which vanishes only at zero. Points are handled in
Jacobian coordinates over $\mathbb Z[s]$, with explicit identities for doubling and addition
and their exceptional branches, and a finite check that the fixed projective point is $P_0$; scalar multiplication halves
its counter.

- [Elements of norm zero](norm-zero.md)
- [Jacobian formulas on the weighted model](jacobian-formulas.md)
- [The fixed Jacobian point](jacobian-generator.md)
- [Scalar multiplication by halving](jacobian-scalar-multiplication.md)

The decision program assembles these steps, and it computes the relation on every input.

- [The exact decision program](decision-program.md)
- [Correctness of the decision program](decision-program-correct.md)
