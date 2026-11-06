---
article_id: af_d277cf2c0669f6ff3b4e08f3
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Syntax.normDiv_eq_preΨ', ZInQ.Syntax.divPsi_eq_Ψ, ZInQ.Syntax.mk_divPsi, ZInQ.Syntax.psiEval_eq_evalEval_ψ
---

# Agreement with the classical division polynomials

Let $R$ be a commutative ring, $A\in R$, and let $W_A$ be the Weierstrass curve
$y^2=x^3+Ax$ ($a_1=a_2=a_3=a_6=0$, $a_4=A$), so that $b_2=b_6=0$, $b_4=2A$, $b_8=-A^2$. Let
$\mathrm{pre}\Psi_n\in R[x]$ and $\Psi_n\in R[x,y]$ ($n\in\mathbb Z$) be the classical
normalized division polynomials of $W_A$: $\mathrm{pre}\Psi_n$ is the normalized elliptic
divisibility sequence with initial values $0,1,1,\Psi_3,\mathrm{pre}\Psi_4$ and parameter
$(\Psi_2^{\rm Sq})^2$, where $\Psi_2^{\rm Sq}=4x^3+b_2x^2+2b_4x+b_6$,
$\Psi_3=3x^4+b_2x^3+3b_4x^2+3b_6x+b_8$, and
$\mathrm{pre}\Psi_4=2x^6+b_2x^5+5b_4x^4+10b_6x^3+10b_8x^2+(b_2b_8-b_4b_6)x+(b_4b_8-b_6^2)$; and
$\Psi_n=\mathrm{pre}\Psi_n\cdot2y$ for even $n$, $\Psi_n=\mathrm{pre}\Psi_n$ for odd $n$. Then
$$f_n=\mathrm{pre}\Psi_n\ \ (n\ge0),\qquad \psi_n=\Psi_n\ \ (n\in\mathbb Z).$$
Moreover $\Psi_n$ agrees with the classical bivariate division polynomial modulo the
curve equation, so the two take the same values at every point of $W_A$.

**Proof sketch.** For $W_A$: $\Psi_2^{\rm Sq}=4(x^3+Ax)$, so $(\Psi_2^{\rm Sq})^2=D_0$;
$\Psi_3=3x^4+6Ax^2-A^2=f_3$; and $\mathrm{pre}\Psi_4=2x^6+10Ax^4-10A^2x^2-2A^3=f_4$. The
normalized sequence satisfies $\mathrm{pre}\Psi_{2m}=\mathrm{pre}\Psi_{m-1}^2\mathrm{pre}\Psi_m\mathrm{pre}\Psi_{m+2}
-\mathrm{pre}\Psi_{m-2}\mathrm{pre}\Psi_m\mathrm{pre}\Psi_{m+1}^2$ and
$\mathrm{pre}\Psi_{2m+1}=\mathrm{pre}\Psi_{m+2}\mathrm{pre}\Psi_m^3\cdot\epsilon_m-\mathrm{pre}\Psi_{m-1}\mathrm{pre}\Psi_{m+1}^3\cdot\epsilon_m'$
with $(\epsilon_m,\epsilon'_m)=(D_0,1)$ for even $m$ and $(1,D_0)$ for odd $m$, which are the
recurrences of $f_n$. Strong induction on $n$ gives $f_n=\mathrm{pre}\Psi_n$; the formulas
for $\psi_n$ and $\Psi_n$, including $\psi_{-n}=-\psi_n$ and the oddness of the sequence,
then agree. The final assertion is the classical congruence between the two bivariate
families in the coordinate ring.

## Depends on

- [Normalized division polynomials and their components](division-polynomials.md)

## Sources

- [Section 2.2](../../sources/syntax-locators.md#section-22-division-polynomials)
