# Heegner classes and the uniform bound

Section 8 and Sections 9.1–9.4 of the manuscript.

Here $K=\mathbb Q(\sqrt k)$ is imaginary quadratic, split at every prime dividing $2N$, and not $\mathbb Q(i)$ or
$\mathbb Q(\sqrt{-3})$. *Active* primes are good odd primes split in $K$; *derivative* primes are good inert primes
outside all current supports. The finite coefficients are $A_i=(\mathbb Z/2^i)[t]/t^i$ and
$M_i=(T_2E\otimes A_i)(\chi_h\Psi_i)$, or $A_i[G]$ with the universal quadratic character for a binary group $G$,
where $\Psi_i=(1+t)^{\xi_i}$ is one moving character, trivial at $2N$ and ramified at a moving prime $r_i$, used for
the whole family. Put $\Lambda=\mathbb Z_2[[t]]$ and $\mathscr O=\widehat{\Lambda_{(2)}}$.

Section 8 builds actual classes from Heegner points, with one multiplier that does not depend on the field, the
conductor or the family, and a closed functional paired with them; their determinant coordinate is calibrated at
the centre against the index of the ring-class point. Every map, homotopy and boundary witness is retained.

- [One moving character for the complete active list](moving-character.md)
- [Local conditions, the derived Kummer condition and duality](local-conditions.md)
- [Finite Heegner descent with one multiplier (4.1), (4.2)](finite-heegner.md)
- [The paired functional and the class-functional coordinate](paired-functional.md)
- [Central specialization and arithmetic calibration (4.5), (4.6)](central-calibration.md)
- [Unused-prime comparison and the corrected coordinate (4.7)](common-coordinate.md)
- [The unknown base has zero coordinate if its derivative vanishes](base-zero.md)

Section 9 passes these diagrams through two limits, with maps, homotopies, cup products, classes and boundary
witnesses together, since ranks alone would not suffice. The *inner limit*, over coefficient stages, uses one
nonprincipal ultrafilter to obtain matrices over $\Lambda$. The *outer limit*, over varying companion fields with a
bounded number of companion primes, gives a discrete valuation ring with uniformizer $2$, in which a minimal
counterexample to a uniform bound is reduced by derivative switches. The result is the varying-companion estimate
(5.5), which gives (3.5).

- [Finite free models and the inner limit](inner-limit.md)
- [The reduced generic residual rank bound (5.1)](residual-bound.md)
- [Evaluation and the outer valuation ring (5.2), (5.3)](outer-dvr.md)
- [The common kernel and a rank-two test (5.4)](kernel-detection.md)
- [Derivative local conditions and the determinant-preserving switch](derivative-switch.md)
- [Uniform ring lower bound and height-one regularity (5.5)](uniform-lower-bound.md)
