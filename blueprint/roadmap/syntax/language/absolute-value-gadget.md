---
article_id: af_aa6fe39f20d62ada0f3e3403
declaration: theorem
origin: cited
---

# Absolute value by four squares

For all $a,x\in\mathbb Q$,
$$a=|x|\iff\exists\,z_1,z_2,z_3,z_4\in\mathbb Q,\quad a=z_1^2+z_2^2+z_3^2+z_4^2\ \text{ and }\ a^2=x^2 .$$

**Proof sketch.** If $a$ is a sum of squares then $a\ge0$, and $a^2=x^2$ gives $a=\pm x$,
hence $a=|x|$. Conversely write $|x|=u/v$ with $u\ge0$, $v>0$ integers; by Lagrange's
theorem $uv=\sum_i n_i^2$, so $|x|=\sum_i(n_i/v)^2$, and $|x|^2=x^2$. The manuscript states the
equivalence without proof; the converse direction is the step supplied here.

## Depends on

- [Formulas and their polynomial compilation](formula-compilation.md)

## Sources

- [Section 2.1](../../../sources/syntax-locators.md#section-21-positivity-and-absolute-value)
