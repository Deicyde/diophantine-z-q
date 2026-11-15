# gz-fh results log

Task: split `ZInQ.GZDecomp.FHNonvanishing` (hL2 of `ZInQ.OneProof.frozenTarget`) into
Friedberg–Hoffstein (printed leaf) + twisted root number (printed leaf) + glue proved in Lean.

## 2026-11-15
- Base 24f97774 (wip/w72). Statement read verbatim: `ZInQKernel/Contrib/GZDecomp/Decomp.lean:109` (VERIFIED read).
- Reused lemmas (VERIFIED read): `GZStatements.heegnerHyp_iff_split`, `jacobiSym_neg_level`,
  `coprime_of_heegnerHyp` (`ZInQKernel/Contrib/GZStatements/Compat.lean`).
- Mathlib has Dirichlet's theorem `Nat.forall_exists_prime_gt_and_eq_mod` (PrimesInAP.lean:443, VERIFIED read).
- Tau Ceti vendored: `CuspForm.twist` exists (Twist/Basic.lean) but no newform-ness of twists and no
  twisted Fricke eigenvalue (VERIFIED by grep) -> twisted root number stated as a printed leaf.
- `scratch/gz-fh/FH.lean`: `ZInQ.GZFH.fhNonvanishing_of_printed : FriedbergHoffsteinB → TwistNewformRootNumber → FHNonvanishing`
  compiles, axioms [propext, Classical.choice, Quot.sound] (VERIFIED, lake env lean, ~1 min).
  Helpers proved: `exists_padicInt_of_isSquare_div`, `zmod_of_isSquare_div`, `mod_eight_of_isSquare_div`,
  `heegner_neg_prime`.
- `ZInQKernel/Contrib/OneProof/FHNonvanishing.lean` = FH.lean without `#print axioms`; `lake build
  +ZInQKernel.Contrib.OneProof.FHNonvanishing` succeeded (VERIFIED).
- Leaf ratings: FriedbergHoffsteinB = specialization of FH 1995 Thm B (recalled, UNVERIFIED) with idelic local
  conditions translated to `D/D₀ ∈ (ℚ_p^×)²`; TwistNewformRootNumber = IK Prop 14.20 / Atkin–Li specialized,
  Gauss sum evaluated (UNVERIFIED numbers).
- Refactor: glue lemmas `exists_aux_disc`, `not_dvd_of_mem_primeFactors`, `heegner_of_local`; FH hypothesis now
  also pins the level `M = N D₀²` of the twisted newform (weaker leaf).
- `ZInQKernel/Contrib/OneProof/FHNonvanishing/FE.lean` (VERIFIED compiles, standard axioms):
  `FriedbergHoffsteinB_FE` (root number as FE sign on 0<Re s<2), `TwistFunctionalEquation` (GLUE target),
  `fhNonvanishing_of_printed_fe`, `twistFunctionalEquation_of_twistNewformRootNumber`, `friedbergHoffsteinB_of_fe`,
  `completedL_eq_frickeCompletedL` (completedL M G = Tau Ceti frickeCompletedL on Re s > 0).
- `#discharges` (scratch/gz-fh/Discharges-output.txt, VERIFIED): `DISCHARGES [hL2] by fhNonvanishing_of_printed`
  (still assumes FriedbergHoffsteinB, TwistNewformRootNumber) and `by fhNonvanishing_of_printed_fe` (still assumes
  FriedbergHoffsteinB_FE, TwistFunctionalEquation); 65 open, 1292 checked, 7 discharge one.
- Main.lean edit checked in scratch (`gzfh_frozenTarget`), and `FHNonvanishingCd` corollary (`gzfh_fhNonvanishingCd`),
  both standard axioms.
- **TwistFunctionalEquation PROVED** (`ZInQKernel/Contrib/OneProof/FHNonvanishing/TwistFE.lean`, dev copy
  `scratch/gz-fh/TwistFricke.lean`; VERIFIED compiles, standard axioms): `slash_frickeGL_twist`
  (`(f ⊗ χ_D) ∣ W_{N D²} = χ_D(−N) ε_N(f) (f ⊗ χ_D)`), via `dft_chiDMod_nonunit` (primitivity witness),
  `dft_chiDMod_unit`, matrix identity `upperRightHom_mul_frickeGL`, `slash_twist_unit`, `dft_twistInv`.
- Restructured: `Contrib/OneProof/FHNonvanishing.lean` (final: `fhNonvanishing_of_friedbergHoffsteinB_FE :
  FriedbergHoffsteinB_FE → FHNonvanishing`) importing `FHNonvanishing/{Basic,FE,TwistFE}.lean`. Build OK.
- `#discharges` rerun (VERIFIED): `DISCHARGES [hL2] by fhNonvanishing_of_friedbergHoffsteinB_FE, still assumes:
  [FriedbergHoffsteinB_FE]`; plus the two older routes; 65 open, 1349 checked, 8 discharge one.
  `gzfh_frozenTarget` (Main edit with hFH : FriedbergHoffsteinB_FE) and `gzfh_fhNonvanishingCd` standard axioms.
