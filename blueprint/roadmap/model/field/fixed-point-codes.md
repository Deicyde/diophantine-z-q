---
article_id: af_c6d2fe5c039199bb2ade26a6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.iota_eq_psi_unconditional, ZInQ.iota_eq_psi
---

# Fixed point codes by division polynomials

For every integer $n\ge1$, $\psi_n(P_0)\ne0$ and
$$\iota(n)=\bigl(0,\ \operatorname{re}x_n,\ \operatorname{im}x_n,\ \operatorname{re}y_n,\
\operatorname{im}y_n\bigr),\qquad
x_n=x(P_0)-\frac{\psi_{n+1}(P_0)\psi_{n-1}(P_0)}{\psi_n(P_0)^2},\quad
y_n=\frac{\psi_{2n}(P_0)}{2\psi_n(P_0)^4},$$
where $\operatorname{re}(u+vs)=u$, $\operatorname{im}(u+vs)=v$ and the $\psi_k$ are the division
polynomials of $E$ ($A=-11243+7950s$). For $n\ge1$, $\iota(-n)$ is obtained from $\iota(n)$
by negating its last two coordinates, and $\iota(0)=(1,0,0,0,0)$.

These are the fixed point codes of the specification: for any fixed $n$ they are explicit
elements of $\mathbb Q^5$, but $n$ may be astronomically large, and the statement is used
only symbolically.

**Proof sketch.** $P_0$ has infinite order (by the nonzero-multiples lemma, from the torsion
theorem; the Mordell-Weil theorem is not needed), so $[n]P_0\ne O$ for $n\ge1$; by part 1 of the division-polynomial theorem $\psi_n(P_0)\ne0$, and part 2 gives
the coordinates of $[n]P_0$. The negative indices follow from
$[-n]P_0=-[n]P_0$ and the code of a negative.

## Depends on

- [Point codes](../point-codes.md)
- [Normalized division polynomials and their components](../../syntax/division-polynomials.md)

## Proof depends on

- [Nonzero multiples of the generator](../descent/nonzero-multiples.md)
- [Division polynomials compute multiples](division-polynomial-multiples.md)
- [Elementary properties of codes](point-code-properties.md)

## Sources

- [Point references and fixed point codes](../../../sources/model-locators.md#point-references-and-fixed-point-codes)
- [Division polynomials](../../../sources/model-locators.md#division-polynomials)
