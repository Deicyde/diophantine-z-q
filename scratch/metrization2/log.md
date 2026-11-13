# metrization2 results log

- Setup: scratch/metrization2/base/ = verbatim copies of scratch/metrization/{Base,ExtLine,part_*}.lean
  (Base.lean byte-identical to scratch/metrization/Base.lean, VERIFIED by cmp). MetrBase.lean (generated,
  gitignored) = metrization's build.sh assembly minus `#print axioms` lines; compiled to an olean with
  `lake env lean -o` in 2 min 38 s, 0 errors (VERIFIED), used only for fast iteration.
- part_nondeg1.lean (step 1 linear algebra exists_null_of_det_eq_zero; baseVal, evalAt_pullback_base, evalAt_of_left_eq, one_left_eq, unitSection_comp_hom, one_mem_dom, evalAt_sub, evalAt_one_sec, germ_mem_of_evalAt_one): compiles on top of MetrBase olean, 0 errors (VERIFIED).
- part_nondeg2.lean: def ProductMapLocalStructure (glue); productLocalStructure_of : ProductMapLocalStructure → ProductLocalStructure; step 2 fderiv_evalAt_apply_eq_zero; step 3 hasDerivAt_line_zero (translation via the group law). Compiles, 0 errors; axioms propext, Classical.choice, Quot.sound (VERIFIED).
- part_nondeg3.lean: pts_eq_of_evalAt (points of an affine open determined by values);
  `jacDetNondegenerate_of : ProductMapLocalStructure → ZInQ.Metrization.JacDetNondegenerate`;
  `metrizationExists_of_productMap : HodgeLatticeTheorem → AnalyticUniformizationOfDim →
  ProductMapLocalStructure → MetrizationExists`. Compiles on top of MetrBase, 0 errors; all three
  `#print axioms`: propext, Classical.choice, Quot.sound (VERIFIED). Hypotheses `A.dim = g` and
  `IsZLattice ℝ Λ` of JacDetNondegenerate are unused (only discreteness of Λ is used).
