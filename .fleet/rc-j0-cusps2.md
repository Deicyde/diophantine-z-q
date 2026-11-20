# Cusp specialization and the based Jacobian

The width-`N` branch `j ↦ j(q^N), j_N ↦ j(q)` selects the rational cusp at zero on the modular normalization. `tendsto_zero` proves that the actual `S`-translated chart converges to it in the complex scheme topology, and `tendsto_infinity` gives the width-one base cusp. `algebraicCusp_limit` assigns every cusp orbit a geometric point over the algebraic closure of ℚ inside ℂ; every representative has that same limit. The assigned points at zero and infinity are the scalar extensions of the specified rational points.

The based represented Jacobian and `aj0` classify the diagonal minus the constant section. `algebraicCuspClass_factors` supplies the exact orbit factorization for the torsion reduction. The Albanese factor and `weighted_comparison_from_limits` give the prescribed torus values for the actual cusp classes, given the compatible target and analytic chart. All 15 new Lean files passed, with 115 declarations audited for standard axioms only.

Next: realize the fixed projective Weierstrass curve as an abelian variety and identify its complex points with the chosen periods, compatibly with the interior map at the fixed scale. Apply the existing Elkik torsion print to these actual geometric classes. For scale rationality, the independently specified isogeny quotient still needs its interior cusp-tail identification; the factorization of the at-scale map does not provide it.

Inherited issue: the sources cited at tex 1784 omit the normalized-newform statement. See the report for the existing source audit and the unverified Elkik locator.

Report: `docs/research/rc-j0-cusps2.md`. Results and verification: `scratch/rc-j0-cusps2/log.md`.

Result commit: `e334b97434808f2d7c4100b439c5ce5f236d4cab` (before this handoff commit).
