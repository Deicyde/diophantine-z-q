---
declaration: theorem
origin: cited
---

# The partitionable even upper estimate (3.3b)

Fix one even coefficient source, its signed unit filter and its depth. If a parameter $d$ in that filter has
a nonempty partitionable prime list and $E^{(d)}$ has $2^\infty$-Selmer corank zero, then
$$L_*(d)\ne0,\qquad v_2L_*(d)-2\omega(d)-s(d)\le C_1.\tag{3.3b}$$
The constant depends only on the fixed source, not on the number or sizes of the primes of $d$ or on later
finite exclusions.

**Proof sketch.** A unit of the even symbol at a parameter $d$ gives
$$L_*(d)\ne0,\qquad v_2L_*(d)\le2\omega(d)+C_0,\tag{3.3a}$$
by the coefficient-square formula of the even form and its normalization, which uses the lower bound from
(3.2). For a partitionable $d$, the contraction certificate makes the terminal polynomial nonzero. Keep all
primes of $d$ stationary: the one-symbol address construction gives binary cubes of any dimension based at
$d$, with no old prime removed, whose other addresses are units and so satisfy (3.3a). The even scalar of
(3.2) has one uniformly cleared denominator on every such cube. Choose a $2$-adic precision above the
nonzero-address valuation bound and the clearing exponent. Each bit of the sign-evaluation coefficients is a
Boolean function of bounded degree, so a cube of large enough dimension has a nonzero address congruent to
the base at that precision. If the base scalar were zero, or of larger valuation than the bound, so would be
that address, a contradiction. The corank-zero comparison in (3.2) then gives (3.3b). The cube dimension
may depend on $d$; the bound does not.

## Depends on

- [Finite realization, unit seeds and contraction certificates](seeds.md)
- [An actual even form with rational normalized phase](../coefficient-sources/even-form.md)

## Proof depends on

- [The fixed-form even scalar (3.2)](../coefficient-sources/even-scalar.md)
- [The address constructions](address-constructions.md)
- [Bit degrees of sign-value functions and cube parity](boolean-degree.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:sec7-even-upper` (L2295–2342)

## Manuscript check

Read by AI review as part of the step map of Section 7 and not yet checked line by line. The review
checked that this cyclotomic missing-address argument on the Kato scalar uses from Section 9 only the
Boolean-degree lemma, which is self-contained, so the forward reference is not circular.
