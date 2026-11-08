---
article_id: af_62005a99b7d7ae05446f0c9c
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.Qsqrt.regulator_ge_of_pos, ZInQ.Progressions.Qsqrt.unit_quadratic, ZInQ.Progressions.golden_le_of_quadratic, ZInQ.Progressions.log_golden_le_abs_log
---

# The regulator of a real quadratic field

Let $d>0$ be an integer that is not the square of a rational number and
$K=\mathbb Q(\sqrt d)$. The regulator of $K$ satisfies
$$R_K\ge\log\frac{1+\sqrt5}{2}.$$

**Proof sketch.** By the signature, the unit rank is $1$, and $R_K=|\log|\sigma(\varepsilon_0)||$
for a fundamental unit $\varepsilon_0$ and a real embedding $\sigma$, with
$|\sigma(\varepsilon_0)|\ne1$ because $R_K>0$. For a unit $u$, the trace $t=u+u'$ and the norm
$n=uu'$ are rational integers, with $n=\pm1$, so $y=\sigma(u)$ satisfies $y^2-ty+n=0$.
Suppose $|y|>1$. If $n=-1$, then $|t|=|y-1/y|>0$, so $|t|\ge1$; since $t\mapsto t-1/t$ is
increasing and equals $1$ at $\phi=(1+\sqrt5)/2$, $|y|\ge\phi$. If $n=1$, then
$|t|=|y+1/y|>2$, so $|t|\ge3$ and $|y|\ge(3+\sqrt5)/2=\phi^2>\phi$. If $|y|<1$, the same
argument applies to $1/y$. In all cases $|\log|y||\ge\log\phi$.

## Depends on

- [The quadratic field $\mathbb Q(\sqrt d)$](quadratic-field.md)

## Proof depends on

- [The signature of $\mathbb Q(\sqrt d)$](signature.md)

## Sources

- [Marcus, Chapter 5](../../../sources/progressions-locators.md#marcus-chapter-5)
