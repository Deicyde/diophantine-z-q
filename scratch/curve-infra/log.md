# curve-infra results log

## Scope (VERIFIED, read docs/research/image-plane.md §1, §7)
image-plane's `ImagePlaneFinal.lean` proves (IC) `ImageClosed`, (AD) `AlgDep`, C2K, (G1'), MobiusGlue-from-T5
with standard axioms; (L0) `FiniteGlobalSections` is used by no theorem of its §1.
=> image-plane's proof needs none of AD, IC, L0. Per task: prove AD in general
(dim = trdeg of function field for integral schemes locally of finite type over a field).

## Alg.lean
- `ringKrullDim_eq_of_isIntegral_of_injective`, `ringKrullDim_mvPolynomial_field`: verbatim from g0-dim.
- `exists_dim_eq_trdeg`: R domain, finite type over field K (same universe) ⇒ ∃ s, dim R = s ∧ trdeg K R = s.
- `trdeg_eq_of_isLocalization`: trdeg K F = trdeg K R for F = Frac R.
- compile: 0 errors, 0 warnings (VERIFIED, 09:20).

## Dim.lean (Mathlib only)
- §2 copied verbatim from g0-dim: `topologicalKrullDim_eq_iSup_of_openEmbedding`, `scheme_dim_eq_of_iso`, `spec_dim`.
- `fnFieldAlgebra K X f : Algebra K X.functionField` := (ΓSpecIso K).inv ≫ f.appTop ≫ germToFunctionField ⊤.
- `dim_affineOpen_eq_trdeg`: U nonempty affine open ⇒ dim U = (trdeg K K(X)).toENat.
- `dim_eq_trdeg`: X integral, f : X ⟶ Spec K locally of finite type ⇒ dim X = (trdeg K K(X)).toENat.
- Props (def ... : Prop with docstrings): `DimEqTrdeg`, `DimEqTrdegAlg`, `AlgDepOfTrdegOne`; theorems
  `dimEqTrdeg`, `dimEqTrdegAlg`, `algDepOfTrdegOne`.
- compile: 0 errors, 0 warnings; all three axioms [propext, Classical.choice, Quot.sound] (VERIFIED, run_Dim.txt).
