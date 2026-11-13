---
article_id: af_f279aed34cfc6d668a69cc19
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.chiC, ZInQ.Contrib.HeckeFE.gP, ZInQ.Contrib.HeckeFE.chiC_isQuadratic, ZInQ.Contrib.HeckeFE.chiC_ne_one, ZInQ.Contrib.HeckeFE.chiC_zero, ZInQ.Contrib.HeckeFE.chiC_sq_of_ne_zero, ZInQ.Contrib.HeckeFE.chiC_inv_eq, ZInQ.Contrib.HeckeFE.jacobiSym_eq_chiC, ZInQ.Contrib.HeckeFE.sum_chi_psi_mul, ZInQ.Contrib.HeckeFE.sum_psi_sq, ZInQ.Contrib.HeckeFE.sum_psi_complete_sq, ZInQ.Contrib.HeckeFE.gP_sq, ZInQ.Contrib.HeckeFE.gP_ne_zero, ZInQ.Contrib.HeckeFE.gauss2D
---

# Quadratic Gauss sums over $\mathbb F_p$ in one and two variables

Let $p$ be a prime, $\chi$ the quadratic character of $\mathbb F_p$ with complex values ($\chi(0)=0$),
$e(t)=e^{2\pi i\tilde t/p}$ for $t\in\mathbb F_p$ with $\tilde t$ any integer representing $t$, and
$g=\sum_{t\in\mathbb F_p}\chi(t)e(t)$ the quadratic Gauss sum.

1. $\chi$ is quadratic (every value of $\chi$ is $0$, $1$ or $-1$), and $\chi$ is not the trivial character if $p\ne2$.
   $\chi(0)=0$; $\chi(t)^2=1$ for $t\ne0$; $\chi(w^{-1})=\chi(w)$ for every $w$. For every integer
   $m$, the Jacobi symbol $\left(\frac mp\right)$ is $\chi(m\bmod p)$.
2. If $p\ne2$, then $\sum_t\chi(t)e(tm)=\chi(m)\,g$ for every $m\in\mathbb F_p$.
3. If $p\ne2$ and $t\ne0$, then $\sum_xe(tx^2)=\chi(t)\,g$.
4. If $p\ne2$ and $t\ne0$, then $\sum_xe(tx^2+nx)=e\bigl(-n^2/(4t)\bigr)\sum_xe(tx^2)$ for every
   $n\in\mathbb F_p$.
5. If $p\ne2$, then $g^2=\chi(-1)\,p$ and $g\ne0$.
6. (The two-dimensional quadratic Gauss sum.) If $p\ne2$, then for all $n_1,n_2\in\mathbb F_p$
   $$\sum_{x,y\in\mathbb F_p}\chi(x^2+y^2)\,e(xn_1+yn_2)=p\,\chi(n_1^2+n_2^2).$$

**Proof sketch.** (1) Properties of the quadratic character; for $w\ne0$,
$\chi(w^{-1})\chi(w)=1$ and $\chi(w)^2=1$. For prime $p$ the Jacobi symbol is the Legendre symbol.

(2) For $m\ne0$, the Gauss sum of $\chi$ with the additive character $t\mapsto e(tm)$ is
$\chi(m)^{-1}g$, and $\chi(m)^{-1}=\chi(m)$; for $m=0$ the sum $\sum_t\chi(t)$ vanishes as $\chi$
is nontrivial.

(3) The number of $x$ with $x^2=s$ is $1+\chi(s)$, so $\sum_xe(tx^2)=\sum_s(1+\chi(s))e(ts)$; the
sum of $e(ts)$ over $s$ is $0$, and (2) evaluates the rest.

(4) Complete the square: $tx^2+nx=t\bigl(x+n/(2t)\bigr)^2-n^2/(4t)$, and shift $x$.

(5) The standard evaluation of the square of a quadratic Gauss sum; $g\ne0$ because
$\chi(-1)p\ne0$.

(6) By (2) and (5), $\chi(m)=g^{-1}\sum_t\chi(t)e(tm)$ for every $m$. Insert this for
$m=x^2+y^2$, exchange the sums, and separate the variables. For $t\ne0$ each inner sum is evaluated
by (4) and (3), giving $\chi(t)^2g^2e\bigl(-(n_1^2+n_2^2)/(4t)\bigr)$; the term $t=0$ vanishes.
Substitute $w=-1/(4t)$, use (2) once more, and simplify with (5) and $\chi(-1)^2=1$.

## Depends on

None.

## Sources

- [Gauss and Jacobi sums](../../../../../sources/hecke-locators.md#gauss-and-jacobi-sums)
