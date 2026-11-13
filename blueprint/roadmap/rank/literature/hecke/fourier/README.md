---
article_id: af_d567852df9caa0247f051eac
---

# The Fourier identity for the Hecke character

The functional equation of a periodic twist needs the finite Fourier transform $\hat c$ of the
coefficient function $c$ to be supported on $(1+i)\mathbb Z[i]$ and to equal a constant multiple of
$c$ there. For the finite part $\omega_d$ of the Hecke character, on $(\mathbb Z/4d)^2$, this subsection
proves it with the constant $4d(1+i)\left(\frac2d\right)$ for every odd squarefree
$d\equiv1\pmod4$.

The Chinese remainder theorem splits $\hat\omega_d$ into a 2-part, a sum over $(\mathbb Z/4)^2$ of the
primary unit against fourth roots of unity, and an odd part, a sum over $(\mathbb Z/d)^2$ of the
Jacobi symbol of the norm against $d$-th roots of unity. The 2-part is a finite table:
$4(1+i)u(\mu)$ at $(1+i)\mu$, and $0$ off $(1+i)\mathbb Z[i]$. The odd part is multiplicative in
$d$, and at an odd prime $p$ it is the two-dimensional quadratic Gauss sum
$\sum_{x,y}\chi(x^2+y^2)e(xn_1+yn_2)=p\,\chi(n_1^2+n_2^2)$, which follows from the one-variable
quadratic Gauss sum by completing the square.

Throughout, $\left(\frac an\right)$ is the Jacobi symbol as in
[the Hecke character](../gaussian/hecke-character.md), and $N(\nu)=\nu_1^2+\nu_2^2$.

- [The Fourier transform of $\omega_d$ splits into a 2-part and an odd part](fourier-factorization.md)
- [The 2-part of the Fourier transform](fourier-two-part.md)
- [Quadratic Gauss sums over $\mathbb F_p$ in one and two variables](quadratic-gauss-sums.md)
- [The odd part of the Fourier transform](odd-gauss-sum.md)
- [The Fourier identity for $\omega_d$](fourier-identity.md)
