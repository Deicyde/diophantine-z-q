import ZInQKernel.Contrib.CloudR2Poincare.L1.RetainedCechModel
import ZInQKernel.Contrib.CloudR2Poincare.L1.ScalarFreeMatrix
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Rebase an ACTUAL retained finite-free comparison

This transports the actual comparison map through a further scalar extension,
using the literal extension-of-scalars composition isomorphism. Its universal
quasi-isomorphism property is retained even for nonflat target algebras.
No native provider is rebuilt and no new model is supplied by a caller of the
final face-compatible-model construction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Scalar extension preserves both actual strict degree bounds. -/
theorem scalarExtendedComplex_strictBounds
    {R S : Type u} [CommRing R] [CommRing S] (β : R →+* S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (lo hi : ℤ)
    [P.IsStrictlyGE lo] [P.IsStrictlyLE hi] :
    CochainComplex.IsStrictlyGE
      (((ModuleCat.extendScalars β).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) lo ∧
      CochainComplex.IsStrictlyLE
        (((ModuleCat.extendScalars β).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hi := by
  constructor
  · rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact (ModuleCat.extendScalars β).map_isZero (P.isZero_of_isStrictlyGE lo n hn)
  · rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact (ModuleCat.extendScalars β).map_isZero (P.isZero_of_isStrictlyLE hi n hn)

/-- The actual scalar extension of a finite free module is finite free. -/
theorem scalarExtension_free_finite
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M] :
    Module.Free S ((ModuleCat.extendScalars (algebraMap R S)).obj M) ∧
      Module.Finite S ((ModuleCat.extendScalars (algebraMap R S)).obj M) := by
  classical
  rcases subsingleton_or_nontrivial S with hs | hs
  · letI : Subsingleton S := hs
    haveI : Subsingleton ((ModuleCat.extendScalars (algebraMap R S)).obj M) :=
      Module.subsingleton S _
    exact ⟨inferInstance, inferInstance⟩
  · letI : Nontrivial S := hs
    letI : Nontrivial R := nontrivial_of_ne (0 : R) 1 (by
      intro h
      have h' := congrArg (algebraMap R S) h
      rw [map_zero, map_one] at h'
      exact zero_ne_one h')
    let b : Module.Basis (ULift.{u} (Fin (Module.finrank R M))) R M :=
      (Module.finBasis R M).reindex Equiv.ulift.symm
    let E := ModuleCat.extendScalars (algebraMap R S)
    let e := E.mapIso b.equivFun.toModuleIso ≪≫
      (extendScalarsCoordinates R S (ULift.{u} (Fin (Module.finrank R M)))).toModuleIso
    exact ⟨Module.Free.of_equiv e.toLinearEquiv.symm,
      Module.Finite.equiv e.toLinearEquiv.symm⟩

/-- The actual comparison after scalar extension and a proved coefficient triangle. -/
def retainedMapAfterScalarExtension
    {A R S : Type u} [CommRing A] [CommRing R] [CommRing S]
    (α : A →+* R) (β : R →+* S) (γ : A →+* S) (h : β.comp α = γ)
    {C : CochainComplex (ModuleCat.{u} A) ℤ} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : P ⟶ ((ModuleCat.extendScalars α).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :
    ((ModuleCat.extendScalars β).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      ((ModuleCat.extendScalars γ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C :=
  ((ModuleCat.extendScalars β).mapHomologicalComplex (ComplexShape.up ℤ)).map e ≫
    (Functor.mapHomologicalComplexCompIso
      ((ModuleCat.extendScalarsComp α β).symm ≪≫ eqToIso (congrArg ModuleCat.extendScalars h))
      (ComplexShape.up ℤ)).hom.app C

/-- The rebased comparison is quasi-isomorphic by the original ALL-algebra witness. -/
theorem quasiIso_retainedMapAfterScalarExtension
    {A R S : Type u} [CommRing A] [CommRing R] [CommRing S]
    (α : A →+* R) (β : R →+* S) (γ : A →+* S) (h : β.comp α = γ)
    {C : CochainComplex (ModuleCat.{u} A) ℤ} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : P ⟶ ((ModuleCat.extendScalars α).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
    (universal : ∀ (B : Type u) [CommRing B] [Algebra R B],
      QuasiIso (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex _).map e)) :
    QuasiIso (retainedMapAfterScalarExtension α β γ h e) := by
  letI : Algebra R S := β.toAlgebra
  haveI : QuasiIso (((ModuleCat.extendScalars β).mapHomologicalComplex _).map e) := universal S
  dsimp only [retainedMapAfterScalarExtension]
  infer_instance

/-- The same rebased comparison stays quasi-isomorphic under EVERY subsequent
scalar extension, including nonflat residue-field extensions. -/
theorem universal_quasiIso_retainedMapAfterScalarExtension
    {A R S : Type u} [CommRing A] [CommRing R] [CommRing S]
    (α : A →+* R) (β : R →+* S) (γ : A →+* S) (h : β.comp α = γ)
    {C : CochainComplex (ModuleCat.{u} A) ℤ} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : P ⟶ ((ModuleCat.extendScalars α).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
    (universal : ∀ (B : Type u) [CommRing B] [Algebra R B],
      QuasiIso (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex _).map e))
    (B : Type u) [CommRing B] [Algebra S B] :
    QuasiIso (((ModuleCat.extendScalars (algebraMap S B)).mapHomologicalComplex _).map
      (retainedMapAfterScalarExtension α β γ h e)) := by
  let E := (ModuleCat.extendScalars β).mapHomologicalComplex (ComplexShape.up ℤ)
  let F := (ModuleCat.extendScalars (algebraMap S B)).mapHomologicalComplex (ComplexShape.up ℤ)
  letI : Algebra R B := ((algebraMap S B).comp β).toAlgebra
  have hsingle := universal B
  let assoc := Functor.mapHomologicalComplexCompIso
    (ModuleCat.extendScalarsComp β (algebraMap S B)).symm (ComplexShape.up ℤ)
  haveI : QuasiIso (F.map (E.map e)) :=
    (quasiIso_iff_of_arrow_mk_iso (F.map (E.map e)) _
      (Arrow.isoMk (assoc.app P)
        (assoc.app (((ModuleCat.extendScalars α).mapHomologicalComplex _).obj C))
        (assoc.hom.naturality e).symm)).mpr hsingle
  dsimp only [retainedMapAfterScalarExtension]
  rw [Functor.map_comp]
  infer_instance

end ZInQ.Contrib.CloudR2Poincare.L1
