---
declaration: theorem
origin: cited
---

# An actual even form with rational normalized phase

Fix a sign $\sigma$, unit squareclasses at a finite support $S_0$ containing $2N$, and a positive squarefree
$D_0$ in that filter with $L_*(\sigma D_0)\ne0$. For every fixed finite exclusion set $B$ prime to $D_0$ there is
an algebraic holomorphic cusp form of weight $3/2$, normalized by $a(D_0)=1$, with scalar characters $\psi$ and
$\eta$ such that $\psi/\eta=\chi_{-\sigma}$ and with the prescribed coefficient support, such that for every
retained positive squarefree $D$ in the original $S_0$ filter
$$a(D)=z_Dr_D,\qquad z_D\in\mu_{2^\infty},\quad r_D\in\mathbb Q,\qquad r_D^2=L_*(\sigma D)/L_*(\sigma D_0).$$
It satisfies, at every good prime $p$ outside $S_0\cup B$ and every index,
$$a(p^2n)=\{\eta(p)a_p-\psi(p)(-n/p)\}a(n)-p\,\eta(p)^2a(n/p^2).\tag{E.12}$$
Nonzero retained squarefree coefficients have integral $v_2a(D)$, and $v_2a(D)-\omega(D)$ has a finite attained
minimum. The form and the initial sieve are fixed before this minimum is chosen, and later exclusions do not
allow a new minimum.

**Proof sketch.** Waldspurger's local theory (ICM 1983, Theorem 1 and Proposition 1; JMPA, Proposition 18)
gives a nonzero $D_0$-Whittaker functional in the Shimura–Waldspurger packet of $E^{(\sigma)}$, and local
projections keep it nonzero while fixing the local types; at unramified primes the coefficient is $1$. For the
whole good-Hecke eigenspace, Waldspurger's Corollary 2 (pp. 483–484), with weight $k=3$, gives
$$a(D)^2=\psi(D/D_0)\,\frac{\sqrt D\,L(E^{(\sigma D)},1)}{\sqrt{D_0}\,L(E^{(\sigma D_0)},1)}\,a(D_0)^2,\tag{E.10}$$
without its auxiliary hypothesis, since $D/D_0$ is a $2$-adic square. Ramsey's algebraic model (Definition 3.1,
Theorem 4.2, Remark 4.4) gives an algebraic vector with $a(D_0)=1$ by flat field extension. Galois conjugation
followed by the matching character twist gives $\tau(a(D))=\nu(D/D_0)\,a(D)$, so $a(D)/z_D$ is rational
(E.11). The recurrence is the Shimura $T(p^2)$ formula, and the closed form
$a(Dm^2)=z_D\eta(m)r_D\prod A_{p,r}(D)$ has integral factors. The lower bound (E.9) for $v_2L_*$ and (E.11)
bound $v_2a(D)-\omega(D)$ below, so the minimum is attained.

## Depends on

None.

## Proof depends on

- [The fixed-form even scalar (3.2)](even-scalar.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:app-even-phase` (L7791–8205); its use in
  Section 7 (L2553–2575)

## Manuscript check

Mapped by AI review and read once for structure; not yet checked line by line. The citation that carries the
most weight, Waldspurger's Corollary 2 with the removal of its auxiliary condition for a pair in one $2$-adic
squareclass, is not yet checked against the print, and neither are Ramsey's Definition 3.1, Theorem 4.2 and
Remark 4.4.
