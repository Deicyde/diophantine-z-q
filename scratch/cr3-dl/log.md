# cr3-dl log

- Wrote ZInQKernel/RouteK/RankDL.lean: sel_of_selmerCertified, CertifiedRankDLRk, slots_d₂_facts,
  exists_infinite_order_of_certifiedRankTYZRk_of_selmerCertified, certifiedRankDLRk_of_certifiedRankTYZRk,
  exists_point_of_selmerCertified_of_infinite_order, poleSoluble_of_slots_infinite_order,
  poleCompleteness_of_certifiedRankDLRk, CertifiedRankDLAdmRk (+ both implications),
  main variant ..._sixContactMin_certifiedRankDLRk.
- Fix: `obtain ⟨-, hcard, ...⟩` on SelmerCertified cleared dependents; use `_`.
- lake build ZInQKernel.RouteK.RankDL: OK. Import line + print_axioms entries added.
