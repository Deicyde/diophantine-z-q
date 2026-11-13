---
article_id: af_a85e9b0c0ccf96becdae35af
---

# Theta series of $\mathbb Z[i]$ and Hecke's continuation

This subsection carries out Hecke's method for the Gaussian integers, with no reference to elliptic
curves. For a shift $(a,b)$ of the lattice $\mathbb Z^2$, the theta kernel
$\theta_{a,b}(x)=\sum_{(m,n)}((m+a)+i(n+b))e^{-\pi((m+a)^2+(n+b)^2)x}$ is a product of
one-variable theta functions, and Poisson summation in one variable gives the transformation law
$\theta_{a,b}(1/x)=x^2\theta^*_{a,b}(x)$ with a dual kernel $\theta^*_{a,b}$. Both kernels decay
faster than every power of $x$, so their Mellin transforms $\Lambda_{a,b}$, $\Lambda^*_{a,b}$ are
entire and satisfy $\Lambda_{a,b}(2-s)=\Lambda^*_{a,b}(s)$.

On $\operatorname{Re}s>3/2$ the Mellin transform is $\pi^{-s}\Gamma(s)$ times the lattice Dirichlet
series $\sum((m+a)+i(n+b))((m+a)^2+(n+b)^2)^{-s}$, which therefore has an entire continuation.
Splitting $\mathbb Z^2$ into residue classes modulo $M$ gives the same for every series
$T_c(s)=\sum_\alpha c(\alpha\bmod M)\,\alpha\,N(\alpha)^{-s}$ over the Gaussian integers, and
grouping its terms by the norm turns it into an ordinary Dirichlet series. When the finite Fourier
transform of $c$ is supported on $(1+i)\mathbb Z[i]$ and is a multiple of $c$ there, the completed
function $\Lambda_c$ satisfies a functional equation under $s\mapsto2-s$.

Throughout, a point $\alpha\in\mathbb Z^2$ is also the Gaussian integer $\alpha_1+\alpha_2i$, with
norm $N(\alpha)=\alpha_1^2+\alpha_2^2$, and an infinite sum over $\mathbb Z^2$ is read as $0$ where
the family is not summable.

- [The weight-two theta kernels of a shifted lattice](theta-kernels.md)
- [The completed lattice functions and their functional equation](theta-mellin.md)
- [The lattice Dirichlet series and its entire continuation](lattice-series.md)
- [Periodic twists of the lattice series and their continuation](twisted-series.md)
- [The functional equation of a periodic twist under a Fourier relation](twisted-functional-equation.md)
