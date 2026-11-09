---
article_id: af_35191227637cf52e54f17182
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.Qsqrt.regulator_of_neg
---

# The regulator of an imaginary quadratic field

Let $d<0$ be an integer (so $d$ is not the square of a rational number) and
$K=\mathbb Q(\sqrt d)$. Then the regulator of $K$ is $R_K=1$.

**Proof sketch.** By the signature, $r_1+r_2-1=0$. So the unit group of $\mathcal O_K$ has
rank $0$, and the regulator is the determinant of an empty matrix, which is $1$.

## Depends on

- [The quadratic field $\mathbb Q(\sqrt d)$](quadratic-field.md)

## Proof depends on

- [The signature of $\mathbb Q(\sqrt d)$](signature.md)

## Sources

- [Marcus, Chapter 5](../../../sources/progressions-locators.md#marcus-chapter-5)
