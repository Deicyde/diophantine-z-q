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

## S2.lean (stage 2) — VERIFIED compiles, standard axioms (all four #print axioms)
- `exists_affineChart_le`: P ∈ U(ℂ) ⇒ an AffineChart c (affine open, ℂ-algebra generators) with P ∈ c.U ⊆ U.
- `SerreHolAt X F P` := ∃ c : AffineChart X, P ∈ c.U(ℂ) ∧ ∃ H analytic at (c.f i P)ᵢ with F = H ∘ (c.f i ·)ᵢ near P
  (Serre's sheaf of holomorphic functions of X^h: locally the restriction of a holomorphic function of the
  coordinates of an affine piece U ↪ 𝔸^k).
- `anFunAt_iff_serreHolAt [LocallyOfFiniteType X.hom]`: AnFunAt X F P ↔ SerreHolAt X F P.
- `isAnMorphism_iff_serre`: IsAnMorphism X Y F ↔ continuous ∧ pulls back SerreHolAt germs at every point.
- Fix noted: `AnalyticOnNhd.eval_continuousLinearMap (ContinuousLinearMap.id ..)` timed out (isDefEq); used
  `AnalyticAt.aeval_mvPolynomial` with `f := id` + `simpa [coe_aeval_eq_eval]` instead.

## Contribution ZInQKernel/Contrib/OneProof/SerreGAGA.lean — VERIFIED
- `lake build ZInQKernel.Contrib.OneProof.SerreGAGA` succeeds (9271 jobs). Imports SGA1Printed and the vendored
  QuasiProjective only.
- Leaf restated over Serre's own objects: `IsSerreHolMap X Y F` := continuous (analyticTopology) ∧ ∀ P s,
  SerreHolAt Y s (F P) → SerreHolAt X (s ∘ F) P. `SerreGAGAMorphism` := ∀ X Y, IsProjVar X → IsProjVar Y →
  ∀ F, IsSerreHolMap X Y F → ∃ f : X ⟶ Y, ∀ P, F P = P ≫ f.
- Glue: `isAnMorphism_iff_isSerreHolMap` (LOFT X, Y), `locallyOfFiniteType_of_isProjVar`, `isProjVar`,
  `sga1_XII_4_4_of_serre`, `gagaMorphism_of_serre hM hL hPC hC hS`.
- axioms (scratch/gaga-serre/axioms.txt): all seven declarations [propext, Classical.choice, Quot.sound].

## Autofold spec scratch/gaga-serre/autofold.json — VERIFIED dry run (python, no Lean)
- Same as sga1-fix's for uniformizationLeafAll (properCompactAn now cited SGA 1 XII 3.2 first); gagaMorphism :=
  SerreGAGA.gagaMorphism_of_serre ... {n}.serreGAGAMorphism with ONE new leaf serreGAGAMorphism (sga1_XII_4_4 dropped).
- `autofold.py --dry-run` at the merged base (main: gagaMorphism LEAF, uniformizationLeafAll GLUE): exit 0,
  "34/11 on 45 -> 38/10 on 48; strictest 34/11 -> 38/10" (autofold-dryrun.txt).
- With kinds.tsv's gagaMorphism row temporarily set to consequence/GLUE/GLUE as on origin/wip/leaf-fold32 (11-16
  re-rating; file restored after): "33/12 on 45 -> 38/10 on 48; strictest 33/12 -> 38/10" = −2 GLUE in both columns.

## Chain build, #discharges, fold dry-run compile — VERIFIED
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges`: success, 13698 jobs, 29m47s (build-main.txt).
- DischargesCheck.lean → discharges.txt: gagaMorphism DISCHARGED by SerreGAGA.gagaMorphism_of_serre, still assumes
  [MumfordComplexTorus, SGA1_XII_3_3a, ProperCompactAn, SGA1_XII_2_4, SerreGAGAMorphism], standard axioms;
  "#discharges: 56 open hypotheses, 3051 theorems checked, 18 discharge one".
- FoldDryRun.lean compiles; sixContactMin_of_open36 standard axioms.

## S3.lean / chart independence — VERIFIED, moved into SerreGAGA.lean
- `anFunAt_iff_forall_chart`: AnFunAt X F P ↔ ∀ AffineChart c ∋ P, ∃ H analytic, F = H ∘ c.f near P
  (basic open D(s) ⊆ U, isLocalization_basicOpen, g = p(f)/q(f)^m). `serreHolAt_iff_forall_chart` corollary.
- SerreGAGA.lean rebuilt; axioms.txt: 9 declarations, standard axioms.
