---
article_id: af_6be0e41450e8ab551da48152
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Syntax.ev_globals_eq_zero_iff, ZInQ.Syntax.generator_values
---

# Rational constants by global equations

Let a template be constructed with formula $\varphi$ and rational constants
$u_1/q_1,\dots,u_r/q_r$ ($q_i\ge2$) held in variables $X_{c_1},\dots,X_{c_r}$, so that its
polynomial is $\kappa(\bigwedge(q_1X_{c_1}\doteq u_1,\dots,q_rX_{c_r}\doteq u_r,\varphi))$. Then for
every $x:\mathbb N\to\mathbb Q$ this polynomial vanishes at $x$ exactly when
$x_{c_i}=u_i/q_i$ for every $i$ and $\varphi$ holds at $x$. The equations are conjuncts of the
whole template, outside every disjunction of $\varphi$, so they constrain every branch.

For the cached coordinates of the generator, the three equations
$$8g_0=1641,\qquad 4g_1=-15465,\qquad 32g_2=87483$$
hold exactly when $(g_0,g_1,g_2)=(1641/8,\,-15465/4,\,87483/32)$, and then
$(0,g_0,-145,g_1,g_2)$ has $x$-coordinate $1641/8-145s=(1641-1160s)/8$ and $y$-coordinate
$-15465/4+(87483/32)s=(-123720+87483s)/32$, the coordinates of $P_0$.

**Proof sketch.** By the compilation theorem the polynomial vanishes exactly when every
conjunct holds; $q_ix_{c_i}=u_i$ with $q_i\ne0$ means $x_{c_i}=u_i/q_i$. The generator
values are the arithmetic $1641/8-145s=(1641-1160s)/8$ and
$-15465/4=-123720/32$.

## Depends on

- [Formulas and their polynomial compilation](formula-compilation.md)

## Proof depends on

- [Sums of squares and products over the rationals](../sum-of-squares-semantics.md)

## Sources

- [Section 2.1](../../../sources/syntax-locators.md#section-21-literal-operations)
- [Section 3](../../../sources/syntax-locators.md#section-3-point-codes)
