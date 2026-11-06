---
article_id: af_a03a7b607a14bb792f6ba8d4
declaration: theorem
origin: background
---

# Doubling and adding division-polynomial triples

Let $K$ be a field of characteristic zero, $A\in K$, $W:y^2=x^3+Ax$, and
$\mathcal O=K[x,y]/(y^2-x^3-Ax)$. For $n\in\mathbb Z$ put
$$\phi_n=x\psi_n^2-\psi_{n+1}\psi_{n-1},\qquad
\omega_n=\begin{cases}y\,\bigl(f_{n+2}f_{n-1}^2-f_{n-2}f_{n+1}^2\bigr),& n\text{ odd},\\[2pt]
\tfrac12\bigl(f_{n+2}f_{n-1}^2-f_{n-2}f_{n+1}^2\bigr),& n\text{ even},\end{cases}$$
so that $4y\,\omega_n=\psi_{n+2}\psi_{n-1}^2-\psi_{n-2}\psi_{n+1}^2$ and $\psi_{2n}=2\psi_n\omega_n$,
and let $J_n=(\phi_n,\omega_n,\psi_n)\in\mathcal O^3$. On triples use the weighted scaling
$u\cdot(X,Y,Z)=(u^2X,u^3Y,uZ)$ and the Jacobian doubling and addition formulas for $W$:
$$\mathrm{dbl}(X,Y,Z)=\bigl(U^2-8XY^2,\ -U(U^2-12XY^2)-8Y^4,\ 2YZ\bigr),\qquad U=3X^2+AZ^4,$$
and $\mathrm{add}\bigl((X_1,Y_1,Z_1),(X_2,Y_2,Z_2)\bigr)=(X_3,Y_3,Z_3)$ with
$$\begin{aligned}
Z_3&=X_1Z_2^2-X_2Z_1^2,\\
X_3&=X_1X_2^2Z_1^2-2Y_1Y_2Z_1Z_2+X_1^2X_2Z_2^2+AX_2Z_1^4Z_2^2+AX_1Z_1^2Z_2^4,\\
-Y_3&=-Y_1X_2^3Z_1^3+2Y_1Y_2^2Z_1^3-3X_1^2X_2Y_2Z_1^2Z_2+3X_1Y_1X_2^2Z_1Z_2^2+X_1^3Y_2Z_2^3\\
&\quad-2Y_1^2Y_2Z_2^3-AX_2Y_2Z_1^6Z_2-AX_1Y_2Z_1^4Z_2^3+AY_1X_2Z_1^3Z_2^4+AX_1Y_1Z_1Z_2^6 .
\end{aligned}$$
For points of $W$ with $Z_1Z_2\ne0$ and distinct abscissas these are the chord formulas: the
sum of $(X_i/Z_i^2,Y_i/Z_i^3)$ is $(X_3/Z_3^2,Y_3/Z_3^3)$. Then
for every integer $k\ge1$, in $\mathcal O^3$,
$$\mathrm{dbl}(J_k)=J_{2k},\qquad \mathrm{add}(J_{k+1},J_k)=(-1)\cdot J_{2k+1}.$$

These are polynomial identities for symbolic $k$; no division polynomial is expanded.

**Proof sketch.** The two expressions for $\omega_n$ agree with $4y\omega_n=\dots$ after
inserting $\psi_j=f_j$ or $2yf_j$ by parity, and $\psi_{2n}=2\psi_n\omega_n$ is the even
recurrence (the instance $(n+1,n-1)$ of the elliptic-sequence law). *Third components.*
$2\omega_k\psi_k=\psi_{2k}$ by the last remark, and
$\phi_{k+1}\psi_k^2-\phi_k\psi_{k+1}^2=-\psi_{2k+1}\psi_1=-\psi_{2k+1}$ by the elliptic-sequence law
at $(k+1,k)$. *First and second components.* Substitute $\phi_j$ and $4y\omega_j$ by their
definitions; each side becomes a polynomial in $x$, $y$ and the $\psi_j$ with
$j\in\{k-2,\dots,k+3\}\cup\{2k-1,2k,2k+1,2k+2\}$, and the difference reduces to zero using the
elliptic-sequence law at index pairs from $\{k-2,\dots,k+3\}$ (which express
$\psi_{2k-1},\dots,\psi_{2k+2}$ through the small indices) and the curve equation
$4y^2=4(x^3+Ax)$. For $k=1,2$ the indices $k-2<0$ are handled by $\psi_{-j}=-\psi_j$.

## Depends on

- [Normalized division polynomials and their components](../../syntax/division-polynomials.md)

## Proof depends on

- [Division polynomials form an elliptic sequence](division-polynomial-elliptic-sequence.md)

## Sources

- [Division polynomials](../../../sources/model-locators.md#division-polynomials)
- [Sutherland lecture notes](../../../sources/model-locators.md#sutherland-lecture-notes)
