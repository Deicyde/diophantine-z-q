# p0-local log

- Merged origin/wip/nt-prop0. Copied the .lake build cache from the main clone (same base commit).
- Covering.lean: Loc, SqEq, loc_mul_sq_iff / loc_congr_sq (Inv), loc_torsion (Tor), Cov, cov_iff_loc,
  kummer (on shortCurve (-d^2)), loc_iff_kummer (Lemma 1.2), Sel2, CertifiedRankSel, classInt, selPair,
  Prop0Statement (iff + surjectivity onto Sel2), selPair_injective, classInt_natClass,
  exists_point_of_loc, certifiedRank_of_sel. Compiles, no sorry.
- PadicSquare.lean: isSquare_of_norm_sub_one_lt (one Hensel lemma for all p: ‖u-1‖ < ‖2‖²), (P) general
  sqEq_add_of_norm_lt_two_sq, odd sqEq_add_of_norm_lt, sqEq_add_of_norm_le_two_adic; unitPart,
  isSquare_iff_even_valuation (SQ(c)), isSquare_coe_iff_toZMod (SQ(a)), isSquare_coe_iff_toZModPow_two (SQ(b)),
  isSquare_padic_iff, isSquare_two_adic_iff; RT: isSquare_intCast_of_residue, isSquare_intCast_div_of_residue,
  isSquare_ratCast_of_residue, isSquare_intCast_div_two_adic, isSquare_ratCast_two_adic. Compiles.
- Real.lean: loc_real_iff (d a b : ℝ), loc_real_iff_int. Compiles.
- Covering.lean additions: sqEq_of_mul_sqEq, SqEq.of_mul_sq, loc_of_sqEq_torsion (torsion witnesses).
- BadOdd.lean: padic_norm_natCast_of_squarefree, padic_norm_ne_zpow_odd, loc_padic_dvd_iff (Lemma B, §4.4
  statement unchanged). Proof by comparing ‖x‖ with ‖d‖ = p⁻¹ (no valuation case split needed). No sorry.
- lake build ZInQKernel OK; #print axioms certifiedRank_of_sel, loc_padic_dvd_iff: propext, Classical.choice, Quot.sound.
