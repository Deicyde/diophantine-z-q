---
article_id: af_f7839fae50b08b4f384080bf
---

# Gauss's point count on $y^2=x^3-x$

For a prime $p\equiv1\pmod4$, the number of solutions of $y^2=x^3-x$ over $\mathbb F_p$ is
$p+2A$, where $p=A^2+B^2$ and $-(A+Bi)$ is congruent to $1$ modulo $2+2i$. The proof here goes
through a quartic Jacobi sum. Since $\mathbb Z[i]$ contains a primitive fourth root of unity, there
is a character $\chi$ of $\mathbb F_p$ of order $4$ with values in $\mathbb Z[i]$; its square is the
quadratic character. The point count is $p$ plus the sum of $\chi(x^3-x)^2$, which the substitution
$t=x^2$ turns into $J+\bar J$ for the Jacobi sum $J=J(\chi,\chi^2)$. Then $J\bar J=p$, and pairing
$t$ with $t^{-1}$ in the sum defining $J$ shows $J\equiv-1\pmod{2+2i}$.

In the form used by Deuring's identity, the count says that $p-\#\{y^2=x^3-x\}$ is
$\frac14\sum_{N(\alpha)=p}u(\alpha)\alpha$: the Gaussian integers of norm $p$ are the four associates
of $\pi$ and of $\bar\pi$ for $\pi=A+Bi$, and the primary unit picks out $-\pi$ and $-\bar\pi$.

Throughout, $p$ is a prime, $\left(\frac{\cdot}{p}\right)$ the quadratic character of
$\mathbb F_p$ (with value $0$ at $0$), and $\bar z$ the complex conjugate of $z\in\mathbb Z[i]$.

- [Quartic characters of $\mathbb F_p$ with values in $\mathbb Z[i]$](quartic-character.md)
- [The point count of $y^2=x^3-x$ as a quartic Jacobi sum](quartic-jacobi-sum.md)
- [The quartic Jacobi sum is $-1$ modulo $2+2i$](jacobi-sum-congruence.md)
- [Gauss's theorem on the points of $y^2=x^3-x$](gauss-count.md)
- [Gauss's point count on $y^2=x^3-x$](gauss-point-count.md)
- [Gauss's point count holds](gauss-point-count-holds.md)
