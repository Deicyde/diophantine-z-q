# redei-four log

- Bridge.lean: OddGClStatement now requires 1 < n (false at n = 1); added redeiB_one_lt and
  supplied it in gCl_dProd_eq_gBit. Other Bridge statements take B nonempty already.
- Drafted Redei/FourRank.lean (chi_psi, odd_card_range_sq_iff, genusMap counting,
  range_sq_eq_ker_chi, card_ker_sq_eq, card_ker_psi, odd_gCl_iff, oddGClStatement, redeiFormula).
- FourRank.lean compiles (lake env lean), no errors; added to Redei.lean.
- Dropped hR from the TYZCl / TYZClRk main-theorem variants (in place, no cycle); docstrings, print_axioms updated. lake build ZInQKernel OK (9918 jobs).
