---
article_id: af_f8094d38409076c12ef5e49c
declaration: def
origin: background
statement: formalized
lean: ZInQ.DivisionPolynomialMultiplication
---

# The multiplication-by-n formulas

This article states, as a proposition, the classical formulas for multiplication by $n$
on $E:y^2=x^3-d^2x$ over $K_0$ (so $A=-d^2=-11243+7950s$). The proposition asserts: for every
affine point $P=(x,y)\in E(K_0)$ and every integer $n\ne0$,

1. $[n]P=O$ if and only if $\psi_n(x,y)=0$;
2. if $[n]P\ne O$, then
$$x([n]P)=x-\frac{\psi_{n+1}(x,y)\,\psi_{n-1}(x,y)}{\psi_n(x,y)^2},\qquad
y([n]P)=\frac{\psi_{2n}(x,y)}{2\,\psi_n(x,y)^4}.$$

Equivalently $x([n]P)=\phi_n/\psi_n^2$ and $y([n]P)=\omega_n/\psi_n^3$ with
$\phi_n=x\psi_n^2-\psi_{n+1}\psi_{n-1}$,
$\omega_n=(\psi_{n+2}\psi_{n-1}^2-\psi_{n-2}\psi_{n+1}^2)/(4y)$ and $\psi_{2n}=2\psi_n\omega_n$; the
second formula is the fixed-scalar ordinate equation $2y([n]P)\psi_n(P)^4=\psi_{2n}(P)$.

This is classical (Sutherland §§5.5-5.6, Lemmas 5.20 and 5.24 and Theorem 5.21;
Silverman, Exercise 3.7; Washington, Theorem 9.33) for every elliptic curve in short
Weierstrass form over a field of characteristic $0$. It enters the proof only through the
fixed-scalar templates. This article fixes the statement as a proposition; the
elliptic-model chapter proves it as a background theorem, and the fixed-scalar semantics
uses that theorem. Its formal proof is a substantial project independent of this
manuscript.

## Depends on

- [Normalized division polynomials and their components](division-polynomials.md)
- [The codes of multiples of the generator](../model/point-codes.md)

## Sources

- [Section 2.2](../../sources/syntax-locators.md#section-22-division-polynomials)
