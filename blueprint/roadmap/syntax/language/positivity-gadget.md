---
article_id: af_453946222099634f806d1483
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Syntax.pos_iff_four_squares, ZInQ.Syntax.exists_blockUpdate_posFormula_iff
---

# Strict positivity by four squares

For every $s\in\mathbb Q$,
$$s>0\iff\exists\,z_1,z_2,z_3,z_4\in\mathbb Q,\quad s\,(z_1^2+z_2^2+z_3^2+z_4^2)=1 .$$
Hence the gadget $\mathrm{POS}(a)$ is satisfiable by a choice of its four fresh variables
exactly when $a>0$.

**Proof sketch.** If $s>0$ write $1/s=a/b$ with integers $a,b>0$. By Lagrange's four-square
theorem $ab=n_1^2+n_2^2+n_3^2+n_4^2$ with $n_i\in\mathbb Z$; put $z_i=n_i/b$, so that
$\sum z_i^2=ab/b^2=1/s$. Conversely a sum of squares is nonnegative, so $s\sum z_i^2=1$
forces $\sum z_i^2>0$ and then $s=1/\sum z_i^2>0$.

## Depends on

- [Formulas and their polynomial compilation](formula-compilation.md)

## Sources

- [Section 2.1](../../../sources/syntax-locators.md#section-21-positivity-and-absolute-value)
