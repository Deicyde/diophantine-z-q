---
article_id: af_374b9276355457843f422392
declaration: theorem
origin: background
---

# Division polynomials compute multiples

The multiplication-by-$n$ formulas hold for $E$ over $K_0$: for every affine point
$P=(x,y)\in E(K_0)$ and every integer $n\ne0$,

1. $[n]P=O$ if and only if $\psi_n(P)=0$;
2. if $[n]P\ne O$, then
$$x([n]P)=x-\frac{\psi_{n+1}(P)\,\psi_{n-1}(P)}{\psi_n(P)^2},\qquad
y([n]P)=\frac{\psi_{2n}(P)}{2\,\psi_n(P)^4},$$

where $\psi_k$ are the normalized division polynomials of $y^2=x^3+Ax$ with
$A=-d^2=-11243+7950s$. More generally the same holds for $y^2=x^3+Ax$ over any field of
characteristic zero with $A\ne0$.

**Proof sketch.** This is the classical theorem on division polynomials (Sutherland,
Lecture 5, Lemmas 5.20 and 5.24 and Theorem 5.21; Silverman, Exercise 3.7). Put
$\phi_n=x\psi_n^2-\psi_{n+1}\psi_{n-1}$ and $\omega_n=(\psi_{n+2}\psi_{n-1}^2-\psi_{n-2}\psi_{n+1}^2)/(4y)$;
the even recurrence says $\psi_{2n}=2\psi_n\omega_n$, so the claimed ordinate is
$\omega_n/\psi_n^3$. One first shows that the normalized $f_n$ are the classical division
polynomials (an elliptic divisibility sequence, satisfying
$\psi_{m+n}\psi_{m-n}=\psi_{m+1}\psi_{m-1}\psi_n^2-\psi_{n+1}\psi_{n-1}\psi_m^2$), then by strong induction on
$n\ge1$ that $(\phi_n/\psi_n^2,\ \omega_n/\psi_n^3)$ satisfies $[n+1]P=[n]P+P$ as an identity in the
function field of the curve, starting from $f_1,\dots,f_4$. Part 1 follows by comparing
orders of poles at $O$: $\psi_n$ has divisor $\sum_{T\in E[n]}(T)-n^2(O)$ in characteristic
zero. Negative $n$ follow from $\psi_{-n}=-\psi_n$ and $[-n]P=-[n]P$.

## Depends on

- [The multiplication-by-n formulas](../../syntax/division-polynomial-multiplication.md)
- [Normalized division polynomials and their components](../../syntax/division-polynomials.md)
- [The generator curve $E$](generator-curve.md)

## Proof depends on

- [Agreement with the classical division polynomials](../../syntax/division-polynomials-classical.md)

## Sources

- [Division polynomials](../../../sources/model-locators.md#division-polynomials)
- [Sutherland lecture notes](../../../sources/model-locators.md#sutherland-lecture-notes)
- [Silverman](../../../sources/model-locators.md#silverman)
