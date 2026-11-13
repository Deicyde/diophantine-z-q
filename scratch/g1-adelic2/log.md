# g1-adelic2 results log

- 03:12 Merged origin/wip/t30-adelic (already contained in fork main 883c4ddf).
  `ZInQKernel/Contrib/G1Adelic/Basic.lean` = `scratch/t30-adelic/Adelic.lean` (header changed only).
  `lake build ZInQKernel.Contrib.G1Adelic.Basic`: OK, 73 s; `#print axioms` of relIndex_eq_four,
  mem_sup_iff_forall, normalizer_component, gamma_count, gamma_order, gamma_count_Zint:
  [propext, Classical.choice, Quot.sound]. VERIFIED.
