# cr3-kummer log
## KummerAt.lean
- kummerAt b e (Kummer map at root e of x^3+bx), kummerAt_add (hom), kummerAtHom, tRootPt. Compiled first try (coefficients for linear_combination from sympy pseudo-division).
## Delta.lean
- delta, deltaHom (complete 2-descent map), delta_eq_sqc_kummer, delta_two_nsmul, halving lemma exists_two_nsmul_eq_of_squares (explicit formula, coefficients by sympy). Fixes: field_simp left 4⁻¹ → used div_eq_iff; sign of one linear_combination coefficient.
