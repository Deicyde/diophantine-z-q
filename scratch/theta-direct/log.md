# theta-direct results log

Task theta-direct, started 2026-11-16 00:00 PST. Base a40d5c4d (wip/theta-direct = fork main + STATUS w76).

## Step 0: merge of origin/wip/theta-fold (8e3dbdea)
* `git merge --no-edit origin/wip/theta-fold`: CONFLICTS in STATUS.md, ZInQKernel/OneProof/Main.lean,
  docs/one-proof/{CONTRIBUTING.md,OPEN.md,open-statements.json,pages-wanted.md},
  scratch/contrib-kit/DischargesTest-output.txt. Merge aborted (`git merge --abort`), as instructed. VERIFIED.
* Went the copy route: theta-fold's definitions copied verbatim into helper modules under
  ZInQKernel/Contrib/OneProof/ThetaDirect/ (each file names its source and line range):
  * UseForm.lean: theta-fold TailK.lean l.283-346 (`ThetaSplit.ThetaRatiosAtQM`, `Jmap_ne_zero`,
    `thetaPointOfFibre_of_qm_atQM`);
  * Kron.lean, Split.lean, Glue.lean: theta-fold's LinYangKron/LinYangSplit/LinYangGlue (import lines only changed);
  * Printed.lean: theta-fold LinYangPrinted.lean l.4-100 (siegelEis, igusaChi10E/12E, IgusaThetaExpressions) and
    l.139-210 (thetaConst_omega_analyticAt); linyang-printed LinYangPrintedFull.lean l.2993-3310 (modularity of
    siegelEis) and l.3330-3338. `LinYangEx29All` / `LinYangEx29` NOT copied.

## Plan (no Lin–Yang)
* Valence (proved in kernel: ValenceFormulaGammaStar from valenceFormulaCocompactEq_proof + shimizuCovolumeO1_proof;
  EllipticOrderDvd = ellipticOrderDvd_proof): a holomorphic weight-2m form for Γ* vanishing at r pairwise
  inequivalent points where a second weight-2m form is nonzero vanishes identically once 12r > m.
* Automorphy of ψ₆∘Ω, χ₁₂∘Ω (normalized) from siegelEis modularity + IgusaThetaExpressions + GammaStarGen.
* R1: ψ₆·Σθ⁸ = c₁·∏θ² on Ω(ℍ) (weight 20, one node τ₂₄); R2: (Σθ⁸)²χ₁₂ = c₂(Σθ⁸)⁵ + c₃(∏θ²)² (weight 40,
  nodes √2+i and τ₂₄). c_i algebraic from algebraic theta ratios at the nodes (CM24 at Ω₂₄; genus one at Ω₀).
* Then e_k(θ⁸)/(Σθ⁸)^k algebraic where j_θ ∈ ℚ∖0 (IgusaAlg k, weighted homogeneity) ⇒ ThetaRatiosAtQM.

## Step 1 (compiled, VERIFIED)
* Helper modules build: UseForm, Kron, Split, Glue, Printed (`lake build ...ThetaDirect.Printed`, 12131 jobs).
* ThetaDirect/Valence.lean compiles: `valenceGS` (ValenceFormulaGammaStar from valenceFormulaCocompactEq_proof +
  shimizuCovolumeO1_proof), `eq_zero_of_nodes` (vanishing at r inequivalent nodes for weight 2m < 24r),
  `auto_mul/sub/const_mul/pow`, `autoGS` (automorphy of S(Ω z)/((z−3)(z+1))^w for Γ* from modularity at M4, M6;
  even w).
* ThetaDirect/Nodes.lean compiles: `nodeAlg_om24` (θ_m/θ_00 algebraic at Ω₂₄ = Ω(τ₂₄)), `nodeAlg_cm4`
  (θ_m/θ_00 algebraic at Ω₀ = Ω(√2+i)), via genus-one values at i (θ01(i) = θ10(i), Jacobi).

## Step 2 (compiled, VERIFIED)
* ThetaDirect/Relations.lean: `psi6Th_modular`, `chi12Th_modular` (from IgusaThetaExpressions + siegelEis_modular +
  spAct_mem); `auto6`, `auto12` (Γ*-automorphy of ψ₆∘Ω, χ₁₂∘Ω normalized); analyticity by fun_prop; nodes
  `tau4 = √2+i`, `tau24` (G20 vanishes at tau4, not at tau24 ⇒ inequivalent);
  `rel1 : ψ₆(Ω z)·Σθ⁸(Ω z) = c₁·∏θ²(Ω z)` (weight 20, node τ₂₄), `rel2 : (Σθ⁸)²χ₁₂ = c₂(Σθ⁸)⁵ + c₃(∏θ²)²`
  (weight 40, nodes √2+i, τ₂₄), for all z with Im z > 0.
* ThetaDirect.lean: `c1_mem`, `c2_mem`, `c3_mem` (algebraic), `qmThetaSymmetricAlg_of`,
  `thetaRatiosAtQM_of_symAlg`, MAIN `thetaRatiosAtQM_of_igusa : IgusaThetaExpressions → ThetaRatiosAtQM`,
  `thetaRatiosAtQM_of_igusa'` (consumer form `QMHauptmodul → ThetaRatiosAtQM`), `thetaPointOfFibre_of_igusa`.
* `lake build ZInQKernel.Contrib.OneProof.ThetaDirect`: OK (12137 jobs). `#print axioms` of all main theorems:
  [propext, Classical.choice, Quot.sound] (scratch/theta-direct/axioms.txt).
* No macro/notation/#eval in the contributor files (CONTRIBUTING.md bar): the membership tactic is an inline
  `repeat (first | ...)` block; `𝔸` written out as `algebraicClosure ℚ ℂ`; linyang-printed's `SpMat` renamed to
  `GapTheta.Mat4` in the §6 copy.
* Fold dry run (python only, on a /tmp copy of the base's ZInQKernel/OneProof/H): theta-fold's plumb.py applies
  unchanged to a40d5c4d (24 files edited, all assertions pass).

## Step 3 (VERIFIED): leaf-free
* py/psi6_check.py (exact, sympy): psi6T and chi12T are invariant under the signed permutations of gt-theta's
  squared laws at M4 and M6, formally in the ten t_m = θ_m² (and in the four second-order theta constants).
* ThetaDirect/Modular.lean compiles: `psi6Th_M4/M6`, `chi12Th_M4/M6` from `GapTheta.sq4/sq6` (no leaf).
* Relations/ThetaDirect rebased on Modular: no `IgusaThetaExpressions` anywhere. Printed.lean deleted;
  Analytic.lean keeps `thetaConst_omega_analyticAt` (theta-fold LinYangPrinted l.139-210, namespace HDec.ThetaDirect).
* MAIN: `HDec.ThetaDirect.thetaRatiosAtQM_proof : ThetaRatiosAtQM` (no hypotheses); `thetaRatiosAtQM_of_qmHauptmodul`,
  `thetaPointOfFibre_of_qmPeriod`. `lake build ZInQKernel.Contrib.OneProof.ThetaDirect` OK (12138 jobs); axioms
  standard (axioms.txt).
* #discharges (Main + Discharges + ThetaDirect, 13007 jobs): 62 open hypotheses, 2804 theorems checked, 7 discharge
  one; no line for thetaRatiosAlgebraic (expected: use form). Saved: discharges.txt.
* Fold patch: fold/make_fold.py → fold/fold.patch (867 lines, 29 files), fold-deleted.txt; not built.

## Step 4: fold check (VERIFIED)
* Patched copy /tmp/td_foldcheck (git archive HEAD + fold.patch, build dirs copied): first build failed only in
  Contrib/OneProof/X0ModuliUsed.lean l.334/363/387 (extra calls of sixContactMin_of_open29); added to make_fold.py
  (patch now 905 lines, 30 files). Rebuild: Main + Discharges OK (13006 jobs).
* Patched tree: `#print axioms ZInQ.OneProof.frozenTarget` standard; `#discharges: 61 open hypotheses, 2799 theorems
  checked, 7 discharge one` (base 62). Saved: fold/foldcheck-axioms-discharges.txt, fold/FoldAx.lean.
* Relations.lean docstring: the c_i values implied by LinYangThetaCurve stated as unchecked (c₁ = −3⁵,
  c₂ = 2⁻¹⁸3⁻⁶, c₃ = 3⁴2⁻¹²; arithmetic from that statement, not used). Module rebuilt OK.
