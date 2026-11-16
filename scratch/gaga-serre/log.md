# gaga-serre results log

## Setup
- Merged origin/main (2880fef1e) into wip/gaga-serre (clean merge, c6a75cf2b). Fork PR #35 (uniformizationLeafAll
  outright) has NOT landed on origin/main (cloud-b3/w17-pub-uniformization is not an ancestor of origin/main):
  sga1-fix's route is kept. VERIFIED (git merge-base --is-ancestor).
- Build tree copied (cp -r, reflink) from ~/dzq-wt/sga1-fix (.lake/build and lean/.lake/build).
  `lake build ZInQKernel.Contrib.OneProof.SGA1Printed ...QuasiProjective` succeeds (9270 jobs, no rebuild).

## S1.lean (stage 1) — VERIFIED compiles, standard axioms
- `SerreGAGA.IsProjVar X` := IsReduced X.left ∧ ∃ N finite, closed immersion i : X → ℙ(N; Spec ℂ) over ℂ
  (ℙ = vendored Jacobian-Challenge ProjectiveSpace, base change of Proj ℤ[x_N]).
- LEAF `SerreGAGA.SerreGAGAMorphism`: ∀ X Y projective varieties, ∀ F : CPt X → CPt Y, IsAnMorphism X Y F →
  ∃ f : X ⟶ Y, ∀ P, F P = P ≫ f.
- `isProjVar (A : AbVar ℂ)`: GeometricallyIntegral.isIntegral_of_subsingleton (reduced) + vendored
  GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral + IsProper.of_comp (ℙ separated)
  + IsClosedImmersion.of_isPreimmersion (closed range from universally closed).
- `sga1_XII_4_4_of_serre : SerreGAGAMorphism → SGA1_XII_4_4`; `gagaMorphism_of_serre hM hL hPC hC hS`.
- `anFunAt_eventually` (AnFunAt is an open condition), `isAnMorphism_iff_germ` (IsAnMorphism ↔ continuous and
  pulls back germs of holomorphic functions at each point: Serre's definition of a holomorphic map).
