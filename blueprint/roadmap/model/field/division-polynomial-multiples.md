---
article_id: af_374b9276355457843f422392
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.mulByN_formulas
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

**Proof sketch.** This is the classical theorem (Sutherland, Lecture 5, Lemmas 5.20 and
5.24 and Theorem 5.21; Silverman, Exercise 3.7). A route through Jacobian coordinates avoids
divisors and handles the identity uniformly. Represent points of $E$ by nonzero triples
$(X,Y,Z)$ with $Y^2=X^3+AXZ^4$, up to the weighted scaling $u\cdot(X,Y,Z)=(u^2X,u^3Y,uZ)$ with
$u\ne0$: the triple represents the affine point $(X/Z^2,Y/Z^3)$ if $Z\ne0$ and $O$ if $Z=0$. The
Jacobian doubling formula sends a representative of $Q$ to a representative of $[2]Q$, for
every $Q$, and the Jacobian addition formula sends representatives of two *distinct* points
$Q_1\ne Q_2$ to a representative of $Q_1+Q_2$ (including the cases where one of them is $O$
or $Q_1=-Q_2$).

Fix an affine $P=(x,y)$, put $\phi_n=x\psi_n^2-\psi_{n+1}\psi_{n-1}$ and $\omega_n=\psi_{2n}/(2\psi_n)$
(a polynomial in $x,y$), and write $J_n(P)=(\phi_n(P),\omega_n(P),\psi_n(P))$. The doubling and
adding identities $\mathrm{dbl}(J_k)=J_{2k}$ and $\mathrm{add}(J_{k+1},J_k)=(-1)\cdot J_{2k+1}$ ($k\ge1$)
hold at every point of the curve: at the generic point of $y^2=x^3+Ax$, in the function field,
no $\psi_n$ with $n\ne0$ vanishes, so there the abscissas of the multiples can be computed by
strong induction from the recurrences of $\psi$ (the duplication formula for $n=2m$, the chord
through $[m+1]P$ and $[m]P$ for $n=2m+1$), which gives the identities in the coordinate ring;
evaluating at $P$ gives them at $P$. Claim: for every $n\ge1$, $J_n(P)$ is a
representative of $[n]P$ (in particular a nonzero triple). Strong induction on $n$:

- $n=1$: $\phi_1=x$, $\omega_1=y$, $\psi_1=1$.
- $n=2k$, $k\ge1$: $J_k(P)$ represents $[k]P$, so its double represents $[2k]P$, and the double
  of $J_k$ is $J_{2k}$.
- $n=2k+1$, $k\ge1$: $J_{k+1}(P)$ and $J_k(P)$ represent $[k+1]P$ and $[k]P$, which are distinct
  because their difference is $P\ne O$; so their sum $\mathrm{add}(J_{k+1},J_k)(P)=(-1)\cdot J_{2k+1}(P)$
  represents $[2k+1]P$, and so does $J_{2k+1}(P)$.

Reading off the third coordinate gives part 1 for $n\ge1$. If $\psi_n(P)\ne0$, then
$[n]P=(\phi_n/\psi_n^2,\ \omega_n/\psi_n^3)$ evaluated at $P$, and
$\phi_n/\psi_n^2=x-\psi_{n+1}\psi_{n-1}/\psi_n^2$, $\omega_n/\psi_n^3=2\psi_n\omega_n/(2\psi_n^4)=\psi_{2n}/(2\psi_n^4)$:
part 2. Negative $n$ follow from $\psi_{-n}=-\psi_n$ (so $\psi_{-n\pm1}=-\psi_{n\mp1}$ and
$\psi_{-2n}=-\psi_{2n}$) and $[-n]P=-[n]P=(x([n]P),-y([n]P))$.

## Depends on

- [The multiplication-by-n formulas](../../syntax/division-polynomial-multiplication.md)
- [Normalized division polynomials and their components](../../syntax/division-polynomials.md)
- [The generator curve $E$](generator-curve.md)

## Sources

- [Division polynomials](../../../sources/model-locators.md#division-polynomials)
- [Sutherland lecture notes](../../../sources/model-locators.md#sutherland-lecture-notes)
- [Silverman](../../../sources/model-locators.md#silverman)
