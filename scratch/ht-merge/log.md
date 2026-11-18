# ht-merge results log

## 2026-11-17

* Base: origin/wip/ht-abvar 8344578f6; origin/main (d435851d2) was not an ancestor; merged cleanly (no conflicts).
* (1) VERIFIED (grep over ZInQKernel/, scratch/, all .lean): `DeRhamScholze.ScholzeDeRhamAlg` is applied in exactly one
  place, `DeRhamScholze.dual_deRham_of_scholze` (DeRhamScholze.lean L325: `hS p F A.X 1`, A : PkgI4.I3.AbVar F, F finite
  over Q_p, degree 1). Every other theorem (isDeRhamTensorOver_of_scholze, deRhamVpAbVarDirect_of_scholze,
  hodgeTateDecompHom_of_scholze, hodgeTateDecompOr_of_*, lemDeRhamDescent_tate, TT.hodgeTateDecompOr_of_scholzeMilne,
  HTAbVar.hodgeTateDecompAbVar_of_scholze) reaches hS only through dual_deRham_of_scholze. No other consumer. Merge allowed.
* (2) Consumers (VERIFIED by reading):
  - deRhamVpAbVarDirect: a LEAF row (Berger, kinds.tsv L8); derham-scholze's discharge is not on ht-abvar's dry-run route.
  - hodgeTateDecompAbVar (TailS L347, for every g) -> deRhamComparisonHT_of_leavesT (TailS L2059) -> r10 : R10 amended
    (ZInQ.Contrib.R10.DeRhamComparisonHT, every A) at scratch/ht-abvar/HTDryRun.lean L626 (HTMergeDryRun L627, all +1) -> uses of r.r10: L686 g8_g12_hf_pz, L688
    g12DetPZ_of_inputs, L720 g8_g11_hf, L784 g9Glue_of_deRhamComparisonHT, L791 g9GlueNoT23_of_deRhamComparisonHT.
    g8_g11_hf (Consumers.lean L553), g8_g12_hf_pz (PicZeroCharZeroCopy L815), g12DetPZ_of_twistFinite (C8Conrad L179) pass
    R10 only to h9g : G9GlueNoT23 (TailA L2017, hypothesis `A.dim = 2`); G9Glue (TailA L2007) also has `A.dim = 2`.
    The proof g9GlueNoT23_of_fieldEmb (TailC L14121) applies R10 as `hR10 ℓ F A' 2 (hdim')` and R10Weights as `hW ℓ F A'`
    with A'.dim = 2 (A' = base change of the abelian surface A to a completion, localModel_of_abVarBaseChange L14390).
  - Conclusion: every end consumer applies the leaf only to abelian surfaces (A'.dim = 2). But the intermediate
    statements (the H field hodgeTateDecompAbVar, R10 / bundle field r10, and the four theorems of task part (3)) quantify
    over every g. A g = 2 leaf cannot prove them unchanged.
* Leaf statement chosen: general g (`DeRhamScholze.HTMerge.ScholzeH1AbVar`), flagged generalization (on-the-spot);
  manuscript-exact `ScholzeH1AbSurf` (g = 2) also stated, implied by it, and proves `HodgeTateDecompAbSurf` (H field at
  g = 2). Reason: the four theorems kept unchanged by task part (3) and the H field / R10 quantify over every g.
* Manuscript (VERIFIED, read): lem:de-rham-descent L10939-10951 (abelian surface), Scholze L10954-10965, Hodge numbers
  L10996; step C3 citation L735-737; bibitems L11010-11018.
* Count (VERIFIED, scratch/ht-merge/count.py on kinds.tsv H rows): current 5/24 on 29; ht-abvar spec 5/27 on 32;
  ht-merge spec 5/26 on 31. New row passes render_open.kinds_row_problems (flag_class pending-review,unverified-locator).
* Build: copied ht-abvar's .lake/build (ZInQKernel oleans, ir) into this worktree; `lake build
  ZInQKernel.Contrib.OneProof.HTAbVarScholze` rebuilds the closure changed by main (LPrefix etc.).
* Compile (VERIFIED, 11-17): lake build ScholzeH1AbVar ok (12341 jobs; no warnings); Axioms.lean: Iff.rfl copy, old/new
  conclusion examples, 10 theorems standard axioms; Discharges.lean: `#discharges: 30 open hypotheses, 11762 theorems
  checked, 25 discharge one`, new: deRhamVpAbVarDirect and hodgeTateDecompOr each by HTMerge.* still assuming exactly
  [ScholzeH1AbVar, T10_TateDuality]; HTMergeDryRun.lean compiles, frozenTarget_hm / sixContactMin_of_open73HM /
  sixContactMin_of_open72_hm standard axioms.
