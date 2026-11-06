---
article_id: af_121313091a3fb9c2242a4d65
declaration: theorem
origin: background
---

# Division polynomials form an elliptic sequence

Let $K$ be a field of characteristic zero, $A\in K$, and let $\psi_n$ ($n\in\mathbb Z$) be the
normalized division polynomials of $y^2=x^3+Ax$ (so $\psi_n=f_n$ for odd $n$, $\psi_n=2yf_n$
for even $n$, $\psi_{-n}=-\psi_n$). Let $\mathcal O=K[x,y]/(y^2-x^3-Ax)$. Then for all
$m,n\in\mathbb Z$, in $\mathcal O$,
$$\psi_{m+n}\,\psi_{m-n}=\psi_{m+1}\,\psi_{m-1}\,\psi_n^2-\psi_{n+1}\,\psi_{n-1}\,\psi_m^2 .$$
Equivalently, with $\phi_n=x\psi_n^2-\psi_{n+1}\psi_{n-1}$,
$$\phi_m\psi_n^2-\phi_n\psi_m^2=-\psi_{m+n}\,\psi_{m-n}.$$
In particular the same identities hold between the values $\psi_k(x_0,y_0)$ at every point
$(x_0,y_0)\in K^2$ of the curve.

The identity is used only symbolically: the indices are arbitrary integers and no $\psi_n$ is
ever expanded.

**Proof sketch.** This is the elliptic-sequence law for the normalized elliptic divisibility
sequence $W_n=\psi_n$ with $W_1=1$, $W_2=\psi_2=2y$, $W_3=f_3$, $W_4=2yf_4$, whose defining
recurrences
$W_{2m+1}=W_{m+2}W_m^3-W_{m-1}W_{m+1}^3$ and
$W_2W_{2m}=W_m\bigl(W_{m+2}W_{m-1}^2-W_{m-2}W_{m+1}^2\bigr)$ are the instances $(m+1,m)$ and
$(m+1,m-1)$ of the law. (In $\mathcal O$ one has $W_2^2=4(x^3+Ax)$, so $D_0=W_2^4$ and the
two parity cases of the manuscript's odd recurrence become the single formula above.) The
law for all $(m,n)$ follows from these two recurrences by strong induction on $|m|+|n|$: by
the symmetries $W_{-k}=-W_k$ and the antisymmetry of both sides under $m\leftrightarrow n$ one
may assume $m>n\ge0$; the cases $n\le1$ are trivial or a recurrence; for larger indices
write $m$ and $n$ through their halves and combine instances with smaller indices (Ward's
argument for elliptic divisibility sequences). It suffices to prove the law for the
universal sequence over $\mathbb Z[b,c,d]$ with $W_2=b$, $W_3=c$, $W_4=bd$, an integral domain,
and specialize.

## Depends on

- [Normalized division polynomials and their components](../../syntax/division-polynomials.md)

## Proof depends on

- [Agreement with the classical division polynomials](../../syntax/division-polynomials-classical.md)

## Sources

- [Division polynomials](../../../sources/model-locators.md#division-polynomials)
- [Sutherland lecture notes](../../../sources/model-locators.md#sutherland-lecture-notes)
