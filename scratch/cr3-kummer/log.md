# cr3-kummer log
## KummerAt.lean
- kummerAt b e (Kummer map at root e of x^3+bx), kummerAt_add (hom), kummerAtHom, tRootPt. Compiled first try (coefficients for linear_combination from sympy pseudo-division).
## Delta.lean
- delta, deltaHom (complete 2-descent map), delta_eq_sqc_kummer, delta_two_nsmul, halving lemma exists_two_nsmul_eq_of_squares (explicit formula, coefficients by sympy). Fixes: field_simp left 4⁻¹ → used div_eq_iff; sign of one linear_combination coefficient.
## Image.lean
- sqfRep (squarefree rep of a square class), loc_map/loc_cast_of_loc_rat, delta_eq_one_iff (kernel = 2C_d(Q) over Q), selRep, selRep_mem_sel2, selRep_eq_iff. Fixes: rw [h1] rewrote inside n.sign → calc; if_pos deprecated → simp only [h, ↓reduceIte].
## Counting.lean
- card_quotient_two_eq_card_ker (finite T: #T/2T = #T[2]), eight_le_card_quotient_two (structure theorem; surjection A → Z/2 × T/2T). Fixes: Prod.smul_snd names, nsmul_eq_mul for omega.
## Torsion2.lean
- ker_two_nsmul_eq, card_ker_two_nsmul_eq_four (#C_d(K)[2]=4).
## RK9.lean, Statements.lean, root Rank.lean
- loc_of_mem_sel2_of_infinite_order (RK9). CertifiedRankRk, CertifiedRankTYZRk, CertifiedRankTYZClRk; certifiedRankSel_of_certifiedRankRk, certifiedRankTYZ_of_certifiedRankTYZRk, certifiedRankTYZCl_of_certifiedRankTYZClRk, certifiedRank_of_certifiedRankRk (all with hfg). Axioms: propext, Classical.choice, Quot.sound. lake build ZInQKernel.RouteK.Rank OK.
