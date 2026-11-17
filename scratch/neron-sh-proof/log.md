# neron-sh-proof results log

Base: 0caafe66. Target: `GapSHPair.NeronBaseChangeStrictHenselization` (field `neronBaseChangeStrictHenselization`,
statement in ZInQKernel/Contrib/OneProof/StrictHenselizationPair.lean:1527, bundle field TailZ29/TailZ33).

## Plan (route)
- Prove the stronger chain Prop `ReductGlue.NeronBaseChangeUnramifiedDVR` (TailZ14:1502); the field follows by
  `GapSHPair.neronBaseChangeStrictHenselization_of_unramified`.
- (A) algebra: O ⊆ O₁ unramified, K₁/K separable algebraic, separable residue ⇒ every finite subset of O₁ lies in
  an O-subalgebra of O₁ étale over O (integral closure D of O in L = K(S), étale locus at 𝔫 = 𝔪₁ ∩ D).
- (B) geometry: for R → R₁ an ind-smooth algebra (directed union of smooth subalgebras) with
  Spec K₁ = Spec R₁ ×_R Spec K, a Néron model over R base-changes to a Néron model over R₁ (BLRLocalizes pattern).

## Build setup
- copied .lake/build and lean/.lake/build from the poincare-proof worktree (same base 0caafe66).

## Part A (VERIFIED, compiled: scratch/neron-sh-proof/PartA.lean, Mathlib only)
- `NeronSH.exists_etale_subalgebra`: O DVR with fraction field K, O' a valuation subring of K', K'/K separable,
  O → O' local, every irreducible of O irreducible in O', κ(O')/κ(O) separable ⇒ every finite s ⊆ O' lies in an
  O-subalgebra B ⊆ O' with `Algebra.Etale O B`. Proof: D = integral closure of O in L = K(s) (finite, Dedekind,
  flat); 𝔫 = 𝔪' ∩ D; D_𝔫 DVR, unramified over O (Mathlib `FormallyUnramified.of_map_maximalIdeal`), étale at 𝔫
  (`IsEtaleAt.of_isUnramifiedAt_of_flat`), D[1/f] étale; each x ∈ s is c/t with t ∉ 𝔫 (valuation-ring argument in
  D_𝔫); B = image of D[1/(f∏t)]. Strict henselianity is NOT used.

## Part B (VERIFIED, compiled: scratch/neron-sh-proof/PartB.lean, imports ZInQKernel.Contrib.OneProof.BLRLocalizes)
- `NeronSH.isNeronModelOver_indSmooth`: R → R₁ with `IndSmooth R R₁` (every finite subset of R₁ in a smooth
  R-subalgebra), R₁ ↪ K₁, Spec K₁ = Spec R₁ ×_R Spec K (IsPullback) ⇒ `CToPrinted.IsNeronModelOver R K X →
  IsNeronModelOver R₁ K₁ (X ×_R R₁)`. Uses EGA IV 8.8.2(ii)/17.7.8(ii) (proved in tree, CloudW01Spread),
  Mathlib `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`, gt-blr's `uqA`, `glue_cover`, `neron_ext`.
  Stages: smooth subalgebras B ⊆ R₁ (directed by IndSmooth); second limit over B ⊇ B_i for descending
  V_{K₁} → X_K to (Spec B_j ×_{B_i} W) ×_R K.

## Part C / result (VERIFIED, compiled: scratch/neron-sh-proof/Full.lean = Parts A+B+C)
- `NeronSH.neronBaseChangeUnramifiedDVR_proof : ReductGlue.NeronBaseChangeUnramifiedDVR` (BLR 7.2 Thm 1 form).
- `NeronSH.neronBaseChangeStrictHenselization_proof : GapSHPair.NeronBaseChangeStrictHenselization` (the field).
- `#print axioms`: both [propext, Classical.choice, Quot.sound].
- K' = localization of O' at image of O∖0 (π irreducible in O' ⇒ uniformizer), so Spec K' = Spec O' ×_O Spec K
  (`isPullback_spec`, Mathlib `Algebra.isPushout_of_isLocalization`, `isPullback_SpecMap_of_isPushout`).

## Deliverable checks (VERIFIED)
- `ZInQKernel/Contrib/OneProof/NeronBaseChangeStrictHenselization.lean` (56 KB) built by
  `lake build +ZInQKernel.Contrib.OneProof.NeronBaseChangeStrictHenselization` (68 s; Main/Discharges up to date).
- `#discharges` (scratch/neron-sh-proof/Discharges.lean, output discharges.txt, module-system warnings stripped):
  `DISCHARGES [OpenResearchLeaves26.neronBaseChangeStrictHenselization] by NeronSH.neronBaseChangeStrictHenselization_proof`,
  `still assumes: []`, axioms [propext, Classical.choice, Quot.sound]; 56 open hypotheses, 2965 theorems, 8 discharge one.
- autofold spec scratch/neron-sh-proof/autofold.json; `--dry-run`: strict count 34/11 on 45 -> 33/11 on 44,
  strictest 34/11 -> 33/11. The dry-run module (FoldCheck.lean = dry run minus line 1) compiles:
  `HDec.HSyn.sixContactMin_of_open36` depends on [propext, Classical.choice, Quot.sound].
