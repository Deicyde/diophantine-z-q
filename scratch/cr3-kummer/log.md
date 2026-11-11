# cr3-kummer log
## KummerAt.lean
- kummerAt b e (Kummer map at root e of x^3+bx), kummerAt_add (hom), kummerAtHom, tRootPt. Compiled first try (coefficients for linear_combination from sympy pseudo-division).
## Delta.lean
- delta, deltaHom (complete 2-descent map), delta_eq_sqc_kummer, delta_two_nsmul, halving lemma exists_two_nsmul_eq_of_squares (explicit formula, coefficients by sympy). Fixes: field_simp left 4⁻¹ → used div_eq_iff; sign of one linear_combination coefficient.
## Image.lean
- sqfRep (squarefree rep of a square class), loc_map/loc_cast_of_loc_rat, delta_eq_one_iff (kernel = 2C_d(Q) over Q), selRep, selRep_mem_sel2, selRep_eq_iff. Fixes: rw [h1] rewrote inside n.sign → calc; if_pos deprecated → simp only [h, ↓reduceIte].
