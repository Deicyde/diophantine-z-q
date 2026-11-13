# atkin-li results log

## 2026-11-13
- 09:26 start, fresh. Merged origin/wip/gz-theta (9720252a); resolved NOTICE conflict (kept
  rleaf-elliptic entry + gz-theta's seven-module entry, ring-class entry).
- 09:34 VERIFIED (compiled, lake build): ZInQKernel.Contrib.GZTheta.NewCMProof and .New32 build.
- 09:35 VERIFIED (compiled): ZInQKernel/Contrib/GZTheta/NewCMFinal.lean:
  `newCM : NewCM`, `heckeThetaNewform : ZInQ.GZDecomp.HeckeThetaNewform`,
  `frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner :
   SixContactMin → TYZThm35ReadingA → FHNonvanishing → GrossZagierHeegner → FrozenTarget`.
  Proof of newCM: F = cmForm etaForm32 d (q-expansion injective); TC
  `Newform.exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul`
  gives g of level M ∣ 32d², χ trivial, same eigenvalues for p ∤ 2d; gz-theta
  `level_eq_of_assoc` ⇒ M = 32d²; TC `eq_qExpansion_coeff_one_smul_of_forall_prime_heckeTCuspNat_eq_smul`
  ⇒ F = g ∈ cuspFormsNew.
  #print axioms: all three = [propext, Classical.choice, Quot.sound]
  (scratch/atkin-li/Check.lean, out_check_axioms.txt).
