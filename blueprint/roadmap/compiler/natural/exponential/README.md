---
article_id: af_393f448e6d2767f86dbde8a0
---

# The alpha and power formulas

The alpha sequence $U_n=\alpha_b(n)$ satisfies $U_0=0$, $U_1=1$, $U_{n+2}=bU_{n+1}-U_n$. It
grows for $b\ge2$, its matrix powers have determinant one, and it is congruent in its
parameter, with $\alpha_2(n)=n$.

- [The alpha sequence](alpha-sequence.md)
- [Growth of the alpha sequence](alpha-growth.md)
- [Matrix powers and the quadratic identity](alpha-matrix.md)
- [Parameter congruence of the alpha sequence](alpha-parameter-congruence.md)

Natural solutions of $x^2+y^2=1+bxy$ are adjacent pairs, by descent. Divisibility of alpha
values follows divisibility of indices, with the square refinement (C.1). Modulo the
companion $v=U_{m+1}-U_{m-1}$ the sequence is periodic up to sign and reflection. Odd
values are unbounded.

- [Natural solutions of the alpha Pell equation](alpha-pell.md)
- [Divisibility of alpha values](alpha-divisibility.md)
- [Period and reflection modulo the companion](alpha-period.md)
- [Odd alpha values are unbounded](alpha-large-odd.md)

The alpha formula (C.2) has eight witnesses and fifteen conditions; it holds exactly when
$b>3$ and $X=\alpha_b(N)$.

- [The alpha formula](alpha-equations.md)
- [Soundness of the alpha formula](alpha-equations-sound.md)
- [Completeness of the alpha formula](alpha-equations-complete.md)

The power formula (C.3) separates the base zero and expresses $P=Q^R$ through three alpha
formulas and one congruence.

- [The power formula](power-equations.md)
- [The power formula expresses exponentiation](power-equations-correct.md)

Binomial coefficients are base-$2^{N+1}$ digits of a power, odd binomial coefficients
detect bit inclusion and disjointness, and three disjointness conditions express the
bitwise AND.

- [Binomial coefficients as base-B digits](binomial-digit.md)
- [Lucas's criterion for bit inclusion and disjointness](lucas-bits.md)
- [The bitwise AND gadget](bit-and.md)
