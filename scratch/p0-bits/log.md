# p0-bits log

- Merged origin/wip/p0-local and origin/wip/p0-charsum (no conflict); build OK.
- Bits.lean: classCond_dvd_iff_rows, loc_padic_selPair_iff_rows (leaf 1), loc_real_selPair_iff (leaf 2),
  not_dvd_classInt / not_dvd_selPair (leaf 4) compiled.
- Leaf 3 against the explicit §2.5 class condition: isSquare_two_adic_signedProd_iff, classCond_two_iff
  (a1=0, b1=μ·u, a0+λ·u=b0+λ·v), classCond_two_iff_D (with (R): row (D)), classCond_two_and_R_iff. Compiled.
- p0-two had no report yet (only a merge commit) at this point.
