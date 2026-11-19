# The coefficient sources

Sections 7.1, 7.2 and 7.5 of the manuscript, with Appendix E, the first part of Appendix F and the five-prime
bound of Appendix G.

Throughout, $E=E_\ell$ for one fixed $\ell$ with $\operatorname{corank}_{\mathbb Z_2}\mathrm{Sel}_{2^\infty}(E/\mathbb Q)=1$,
$N$ is its conductor and $\pi:X_0(N)\to E$ a modular parametrization with $\pi(\infty)=0$. For a squarefree
parameter $h$, $L_*(h)$ is the central value of $L(E^{(h)},s)$ normalized by the periods fixed by $\pi$ and the
integral lattice, $s(h)$ is the length of $\mathrm{Sha}(E^{(h)}/\mathbb Q)[2^\infty]$ when it is finite, and
$\omega(h)$ is the number of prime factors of $h$. Constants depend on the fixed curve, its lattice and the
allowed local types at $2N$, and are fixed before any conductor, companion field or binary dimension varies.

The proof reads two families of coefficients. The *even source* comes from Kato's Euler system. Appendix E's
main result is one Kato class, retained with its smoothing, for a whole binary family of quadratic twists at
once, with a height-one divisibility and a central reciprocity whose constants do not depend on the conductors.
It gives one scalar whose central valuation has active-prime term exactly $-2\omega(h)$, and then an actual
weight $3/2$ form whose squarefree coefficients read the central values.

- [One retained Kato system and its two comparisons (K1)–(K3)](kato-system.md)
- [The fixed-form even scalar (3.2)](even-scalar.md)
- [An actual even form with rational normalized phase](even-form.md)
- [Nonvanishing in a prescribed unit filter](nonvanishing.md)

The *odd source* is Appendix F's main result. Write $m=|h_*|$ for a fixed negative genus partner. An
*admissible* $D$ is positive, squarefree, prime to the fixed support and in the prescribed unit classes; then
$K_D=\mathbb Q(\sqrt{Dh_*})$ is imaginary, split at $2N$, without extra units, and the conductor-one point is the
unaveraged sum
$$P_D=\sum_{[\mathfrak a]\in\operatorname{Pic}(\mathcal O_{K_D})}\chi_{h_*}(\mathrm N\mathfrak a)\,\pi\bigl(x_D^{[\mathfrak a]}\bigr).\tag{O.1}$$
Weighted ternary theta series on the definite quaternion algebra ramified at a detecting prime $\ell_0$ and at
infinity are holomorphic forms of weight $3/2$ with an exact Hecke recurrence, and their coefficients equal,
modulo $2^M$ and with no class number divided out, a fixed multiple of a finite-field Kummer image of $P_D$
(O.7). Visibility (O.8) turns a visible coefficient into a simple zero.

- [One witness and a compatible detecting sequence (3.7), (O.2)](odd-witness.md)
- [The actual odd theta form and its recurrence (O.6)](odd-theta-form.md)
- [The unaveraged weighted theta comparison (O.7)](theta-comparison.md)
- [Visibility and the native genus index (O.8)](visibility.md)
