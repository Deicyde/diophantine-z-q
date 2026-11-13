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
- part_unif0.lean: verbatim copies of leaf-push2's cptObj, CPts, cEvalAt, cDom, IsUniformization
  (ZInQKernel/HDecomp/LeafPush2/R22.lean l. 22-56) and UniformizationExists (T.lean l. 26-37), in
  namespace ZInQ.LeafPush2, with `AbVar` = Base's ZInQ.DefFaltings.AbVar (a copy of PkgI3.AbVar).
- Checked (VERIFIED by diff of 12-line windows): Base.lean's GroupModel, ptC, evalAt, dom,
  IsAnalyticUniformization, genericFibre match ZInQKernel/HDecomp/Faltings/Models.lean.
- part_unif1.lean: θ : A_L(ℂ)_τ → 𝒢(ℂ)_τ (q ↦ Spec ℂ → A_L ≅ 𝒢_L → 𝒢) with inverse χ built from
  the monoidal functor Over.pullback (Spec L → Spec 𝓞_L); theta_mul, theta_injective,
  theta_surjective, evalAt_theta. `analyticUniformizationOfDim_of_uniformizationExists :
  ZInQ.LeafPush2.UniformizationExists → ZInQ.Metrization.AnalyticUniformizationOfDim` (apply T35 to
  A_L over L at σ = τ; dim A_L = dim A by G0Dim.dim_baseChange). Compiles, 0 errors; axioms
  propext, Classical.choice, Quot.sound (VERIFIED).
- build.sh → Metrization2.lean (5735 lines, `import Mathlib` only): `lake env lean
  scratch/metrization2/Metrization2.lean` 0 errors in 26 s (Mathlib loaded); no `sorry`, no `axiom`
  (grep); `#print axioms` of jacDetNondegenerate_of, productLocalStructure_of,
  metrizationExists_of_productMap, analyticUniformizationOfDim_of_uniformizationExists,
  HSyn.G0Split.heightAdditivity_of_metrization_v4: propext, Classical.choice, Quot.sound (VERIFIED).
- part_pml1.lean (toward ProductMapLocalStructure): ev (evaluation at complex points of any scheme) with ev_comp, ev_res, ev_add, ev_mul, ev_zero, ev_one, ev_pow, ev_sum, ev_ne_zero_of_mem, mem_basicOpen_of_ev_ne_zero; exists_sum_of_isPushout (every element of a CommRingCat pushout is Σ inl α·inr β, via the universal property and Subring.closure). Compiles, 0 errors (VERIFIED).
- part_pml2.lean: core_local (local structure of X₁ ×_S X₂, S affine, at complex points: affine opens V_i, Q = V₁ ×_S V₂ affine with Γ(Q) a pushout, basic open D(h) ⊆ j⁻¹W, t = a/h^N, H = h^{N+1}); compiles, 0 errors (VERIFIED).
- part_pml3.lean: `productMapLocalStructure : ProductMapLocalStructure` (from core_local with
  S = Spec 𝓞_L, W = m⁻¹U, t = m^*s); hence `jacDetNondegenerate : JacDetNondegenerate` and
  `productLocalStructure : ProductLocalStructure`, no hypotheses.
- part_final2.lean: `heightAdditivity_of_metrization_v5` (N1, H5, AnalyticUniformizationUnique,
  HodgeLatticeTheorem, T35, ProductHodgeLattice) and `metrizationExists_of_uniformizationExists`
  (HodgeLatticeTheorem, T35).
- Rebuilt Metrization2.lean (6164 lines): `lake env lean` 0 errors in 45 s; no sorry, no axiom;
  all new `#print axioms`: propext, Classical.choice, Quot.sound (VERIFIED).
- Kernel-world check: `lake build ZInQKernel.HDecomp.LeafPush2.T ZInQKernel.HDecomp.Faltings.Models`
  (17 modules, 1 min 57 s). build_kernel.sh → Kernel.lean (imports ZInQKernel.HDecomp.LeafPush2.T;
  appends metrization's part_g0dim, the statements AnalyticUniformizationOfDim, JacDetNondegenerate,
  ProductLocalStructure and metrization's germ lemmas verbatim, plus this task's parts, with
  `open PkgI3 (AbVar)` as in the kernel's Models.lean; no copy of T35 or of AbVar). `lake env lean`
  0 errors (17.5 s); `#print axioms` of jacDetNondegenerate, productLocalStructure,
  analyticUniformizationOfDim_of_uniformizationExists (the latter now against the kernel's own
  ZInQ.LeafPush2.UniformizationExists over PkgI3.AbVar): propext, Classical.choice, Quot.sound
  (VERIFIED).
- Final re-check 06:39: build.sh + lake env lean Metrization2.lean 0 errors; build_kernel.sh + lake env lean Kernel.lean 0 errors; no sorryAx in any #print axioms (VERIFIED).
