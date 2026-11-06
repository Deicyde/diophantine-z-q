---
article_id: af_4ca91aea1e2ffc6180633888
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Precision.rat_eq_zero_of_sq_sub_two_sq, ZInQ.Compiler.Precision.intNorm_ne_zero
---

# Elements of norm zero

For $u,v\in\mathbb Q$, if $u^2-2v^2=0$ then $u=v=0$. Equivalently, an element $z$ of
$K_0$ with $\operatorname N(z)=0$ is zero, and for $Y\in\mathbb Z[s]$ with $Y\ne0$ the integer
$\operatorname N(Y)=Y\bar Y$ is nonzero. Hence every division by an element of $K_0$ in the
precision computation can be guarded by the exact test $\operatorname N\ne0$ on integer
components.

**Proof sketch.** If $v\ne0$ then $(u/v)^2=2$, contradicting the irrationality of $\sqrt2$.
Equivalently, after clearing denominators a primitive integer solution of $a^2=2b^2$ has
$a$ even, then $b$ even, a contradiction. So $v=0$ and then $u=0$.

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](../../../model/field/quadratic-field.md)

## Sources

- [Section 10.3 precision IR](../../../../sources/compiler-natural-locators.md#section-103-precision-ir)
