import ZInQKernel.Contrib.CloudR2Poincare.L1.RetainedModelScalarKernel
import ZInQKernel.Contrib.CloudR2Poincare.L1.ScalarKernelComparisons

/-! Transport the ACTUAL scalar kernel comparison from the ACTUAL universally
quasi-isomorphic retained model through a flat coefficient localization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Actual field scalar zero-kernel preservation for the ORIGINAL integer Čech
complex, derived from the actual retained comparison, flat localization,
and reduced rank one. All maps in the conclusion are the canonical maps. -/
theorem isIso_originalScalarCechKernel_of_retainedComparison
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [IsProper f] [GeometricallyIntegral f]
    (M : X.Modules) [M.IsInvertible]
    (hM : ∀ y : Y, Scheme.Pic.map (f.fiberι y) (Scheme.Pic.mk M) = 1)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hcover : ⨆ i, U i = ⊤)
    (hU : ∀ (q : ℕ) (t : Fin (q + 1) → ι), IsAffineOpen (⨅ l, U (t l)))
    (S : Type u) [CommRing S] [_root_.IsReduced S] [Algebra Γ(Y, ⊤) S]
    [Module.Flat Γ(Y, ⊤) S]
    (P : CochainComplex (ModuleCat.{u} S) ℤ) [P.IsStrictlyGE 0]
    {m n : Type u} [Fintype m] [Fintype n]
    (b0 : Module.Basis n S (P.X 0)) (b1 : Module.Basis m S (P.X 1))
    (φ : P ⟶ ((ModuleCat.extendScalars (algebraMap Γ(Y, ⊤) S)).mapHomologicalComplex _).obj
      (Scheme.Modules.cechModuleComplex f M U)) [QuasiIso φ]
    (universal : ∀ (B : Type u) [CommRing B] [Algebra S B],
      QuasiIso (((ModuleCat.extendScalars (algebraMap S B)).mapHomologicalComplex _).map φ))
    (K : Type u) [Field K] (ψ : S →+* K) :
    IsIso (kernelComparison ((Scheme.Modules.cechModuleComplex f M U).d 0 1)
      (ModuleCat.extendScalars (ψ.comp (algebraMap Γ(Y, ⊤) S)))) := by
  let A := Γ(Y, ⊤)
  let α : A →+* S := algebraMap A S
  letI : Algebra S K := ψ.toAlgebra
  let E := ModuleCat.extendScalars α
  let F := ModuleCat.extendScalars ψ
  let C := Scheme.Modules.cechModuleComplex f M U
  let CE : CochainComplex (ModuleCat.{u} S) ℤ := (E.mapHomologicalComplex _).obj C
  haveI : QuasiIso ((F.mapHomologicalComplex _).map φ) := universal K
  have hP := isIso_retainedModel_scalarKernelComparison f M hM U hcover hU S P b0 b1 φ universal K ψ
  have negP : IsZero (P.X (-1)) := P.isZero_of_isStrictlyGE 0 (-1) (by omega)
  have negCE : IsZero (CE.X (-1)) := E.map_isZero (C.isZero_of_isStrictlyGE 0 (-1) (by omega))
  have hCE := isIso_kernelComparison_of_universal_nonnegative_map F (K := P) (L := CE) φ negP negCE hP
  haveI : IsIso (kernelComparison (E.map (C.d 0 1)) F) := hCE
  haveI : IsIso (kernelComparison (C.d 0 1) E) := isIso_kernelComparison_extendScalars_of_flat A S _
  have hEF : IsIso (kernelComparison (C.d 0 1) (E ⋙ F)) := by
    rw [kernelComparison_comp_functor]
    infer_instance
  exact isIso_kernelComparison_of_functor_iso (C.d 0 1) (E ⋙ F)
    (ModuleCat.extendScalars (ψ.comp α)) (ModuleCat.extendScalarsComp α ψ).symm hEF

end ZInQ.Contrib.CloudR2Poincare.L1
