---
article_id: af_ea552c7c4f84feb0d25907e0
declaration: theorem
origin: cited
---

# Quadratic-field routines

An element $\alpha=g+hs\in\mathbb Z[s]$ is *represented* by two signed integer pairs (four
registers) representing $g$ and $h$. There are statements of the ideal register language
for addition, subtraction, negation, multiplication
$(g+hs)(g'+h's)=(gg'+2hh')+(gh'+hg')s$, multiplication by an integer, conjugation
$g+hs\mapsto g-hs$, the norm $\operatorname N(g+hs)=g^2-2h^2$ (into a signed pair), the
rational component $g$, the test $\alpha=0$, and the comparison of two rational numbers
$\theta_1/\delta_1$, $\theta_2/\delta_2$ with nonzero integer denominators (by
cross-multiplication with the signs of the denominators). Each, started with operands
represented and temporaries distinct, terminates normally with the exact result
represented, and leaves every other register unchanged.

**Proof sketch.** Compositions of the signed integer routines, verified componentwise. The
comparison uses $\theta_1/\delta_1<\theta_2/\delta_2\iff\theta_1\delta_2\,\mathrm{sgn}(\delta_1\delta_2)<\theta_2\delta_1\,\mathrm{sgn}(\delta_1\delta_2)$.

## Depends on

- [Signed integer routines](ir-integer-routines.md)
- [The field $K_0=\mathbb Q(\sqrt2)$](../../../model/field/quadratic-field.md)

## Sources

- [Section 10.3 precision IR](../../../../sources/compiler-natural-locators.md#section-103-precision-ir)
