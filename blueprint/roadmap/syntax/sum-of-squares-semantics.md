---
article_id: af_f29d6a710dbd8b2ce25878e4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Syntax.Formula.ev_compile_eq_zero_iff, ZInQ.Syntax.ev_sum_sq_eq_zero_iff, ZInQ.Syntax.ev_prod_eq_zero_iff
---

# Sums of squares and products over the rationals

For every formula $\varphi$ and every $x:\mathbb N\to\mathbb Q$,
$$\kappa(\varphi)(x)=0\iff\varphi\text{ holds at }x .$$
In particular, for polynomials $f_1,\dots,f_k$,
$\sum_i f_i(x)^2=0\iff f_1(x)=\dots=f_k(x)=0$ and
$\prod_i f_i(x)=0\iff f_i(x)=0$ for some $i$.

**Proof sketch.** Induction on $\varphi$. For an atom, $\kappa(a\doteq b)(x)=a(x)-b(x)$. For a
conjunction, each square is a nonnegative rational, so a finite sum of squares vanishes
exactly when every square vanishes, and $t^2=0\iff t=0$; the empty sum is $0$ and the empty
conjunction is true. For a disjunction, $\mathbb Q$ has no zero divisors, so a finite product
vanishes exactly when a factor does; the empty product is $1\ne0$ and the empty
disjunction is false.

## Depends on

- [Formulas and their polynomial compilation](language/formula-compilation.md)

## Sources

- [Section 2.1](../../sources/syntax-locators.md#section-21-literal-operations)
