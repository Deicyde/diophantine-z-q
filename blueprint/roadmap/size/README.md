---
article_id: af_88f5a1aa1179848ba5e4bf39
---

# The cutoff and polynomial size

This chapter supplies the quantitative half of input B: the fixed constants of the
specification are bounded, the guard cutoff $T$ is identified with a closed expression
below $2^{2^{2^{9013}}}$, and the specified polynomial $P_*$ is shown to have degree below
$2\uparrow\uparrow7$ and coefficients below $2\uparrow\uparrow8$. The constants $D$, $T$,
$H_{\rm cat}$, $N_s$, $M_0$, $c_*$, $\ell$ and the program literal $c_3$ are astronomically
large. None of them is ever evaluated: every statement about them is proved symbolically from
their defining expressions, by monotonicity of powers and elementary logarithm estimates.
The finite computations that remain are small, closed comparisons and congruences, and
one traversal of the template library that computes syntax heights.

The fixed constants are those of the specification:
$P_s=\prod_{p\le324}p$, $W=4P_s$, the catalogue product $H_{\rm cat}$ and maximum $H_{\max}$,
$N_s=P_sH_{\rm cat}$, the least formal multiple $M_0=\mathrm{LFM}(N_s)$, $c_*=4M_0$,
$\ell=12P_s^{2916}H_{\rm cat}^{732}$, $F_0=324!$, $D=F_0\,3^{256F_0^4}$, $G_0=116064000000$,
$E_0=10(DG_0)^2$, $R=\max(D,H_{\max},c_*,10^{12})$, $Q=R^{RE_0}$,
$B_{\rm cm}=D^2\,3^{21000D^2}+1$, $C_{\rm cm}=2B_{\rm cm}+4096(1028+5D+84000D^2)$,
$A_{\rm ht}=2\cdot10^{13}\max(1,C_{\rm cm},Q^{17})$ and $T=(48A_{\rm ht})^{13}$.

## The literal cutoff

Proposition 12.1 has three ingredients. First, the prime catalogue is controlled by the
catalogue bound: every unit class modulo $W$ has twenty-two primes above $324$ below
$X=2^{W^8}$, so $H_{\max}<X$, $H_{\rm cat}\le X^{22W}$ and $\log_2N_s<2^{4613}$. The
manuscript derives the same statement with the cutoff $2^{W^3}$ from the explicit progression
estimate of Bennett, Martin, O'Bryant and Rechnitzer; here the cutoff is $2^{W^8}$, and the
catalogue bound is proved from an effective Dirichlet theorem in the progressions chapter. Second, the least formal multiple has a
successful index at most $N_s^{10}$: multiplying $P_0$ by the product of its reduction
orders at the odd places above $N_s$ puts it in the kernel of reduction there, and a
further factor $N_s^4$ pushes it deep into the filtration at every place above $N_s$,
including the place above $2$, where $P_0$ already starts in the third filtration subgroup.
Third, a chain of symbolic estimates gives $c_*<2^{2^{4617}}<2^{2^{8008}}<D$, hence $R=D$,
identifies the maximum in $A_{\rm ht}$ as $Q^{17}$, and bounds $T$.

The small explicit bounds and the catalogue estimates, then the constants derived from them,
are in their own section.

- [Bounds for the fixed constants](constants/README.md)

The existence of a successful formal multiple, with the reduction and filtration facts it
needs, forms the next section.

- [The least formal multiple](formal-multiple/README.md)

Together these give the proposition.

- [The literal cutoff](cutoff.md)

## Degree and coefficient bounds

Section 12.1 bounds $P_*$ without expanding it. Integer polynomials carry the coefficient
$\ell^1$ norm and the total degree; pairs representing elements of
$\mathbb Z[X][\sqrt2]$ carry the weighted norm $\|a\|_1+2\|b\|_1$. Both are
submultiplicative, and substitution multiplies degrees and raises norms to the power of the
outer degree. The division polynomials then satisfy $\deg f_n\le(n+1)^3$ and
$\|f_n\|\le2^{100(n+1)^3}$, the coordinates of $\iota(n)$ for $|n|\le T$ have height at most
$2^{2^{30}(T+1)^3}$, and each of the three finite constructors has degree at most $B^4$ and
norm at most $2^{B^8}$ for $B=T+1$.

- [Norms, division polynomials and the finite constructors](norms/README.md)

A syntax height is attached to every node of every template and to every recipe. At height
$h$ a polynomial has degree and logarithmic norm at most $B^{8h}$; the library traversal
gives template heights at most $249$, the recipe rules give root height $256$, and the
final comparison with the towers uses only $T<2^{2^{2^{9013}}}$.

- [Syntax heights and the final comparison](majorants/README.md)

With the witness accounting of the specification chapter, this is the size part of input B.

- [Variable, degree and coefficient bounds](syntax-bounds.md)
