/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AlgebraicGeometry.Modules.Sheaf
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Presentation
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesComp

/-!
# Coherent sheaves on a scheme are locally cokernels of finite free sheaves

A coherent sheaf of modules `F` on a scheme `X` is, near every point, the cokernel of a morphism
of finite free sheaves: there is an open `U ∋ x` and an exact sequence
`𝒪_U^I ⟶ 𝒪_U^K ⟶ F|_U ⟶ 0` with `I`, `K` finite. This is the finite presentation of `F` over
the slice site (`SheafOfModules.IsCoherent.isFinitePresentation`) read on the open subscheme
(`AlgebraicGeometry.Scheme.Modules.presentationOverRestrict`).

The statement is given twice: for `AlgebraicGeometry.Scheme.Modules` and restriction along
`U.ι`, and for sheaves of modules over `AlgebraicGeometry.LocallyRingedSpace.ringSheaf` with
restriction `AlgebraicGeometry.LocallyRingedSpace.restrictModules`, the two restrictions being
identified by `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoRestrictModules`. The cokernel
is expressed by a colimit cokernel cofork rather than by `CategoryTheory.Limits.cokernel`, so that
no comparison of the colimit instances of the two spellings is needed.
-/

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **A coherent sheaf on a scheme is locally a cokernel of finite free sheaves**: every point
has an open neighbourhood `U` with a cokernel presentation `𝒪_U^I ⟶ 𝒪_U^K ⟶ F|_U ⟶ 0`,
`I` and `K` finite. -/
theorem Modules.exists_restrict_isColimit_cokernelCofork (X : Scheme.{u})
    (F : X.Modules) [F.IsCoherent] (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U) (I K : Type u) (_ : Finite I) (_ : Finite K)
      (ψ : SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ⟶ SheafOfModules.free K)
      (g : SheafOfModules.free K ⟶ F.restrict U.ι)
      (H : ψ ≫ g = 0), Nonempty (IsColimit (CokernelCofork.ofπ g H)) := by
  haveI := SheafOfModules.IsCoherent.cloudB3W17bOka_isFinitePresentation F
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  have hcov : IsOpenCover q.X := (Opens.coversTop_iff _ q.X).1 q.coversTop
  obtain ⟨i, hi⟩ : ∃ i, x ∈ q.X i := by
    have : x ∈ (⊤ : X.Opens) := trivial
    rw [← hcov.iSup_eq_top] at this
    exact Opens.mem_iSup.1 this
  haveI := hq
  let P := Modules.presentationOverRestrict (X := X) F (q.X i) (q.presentation i)
  have hfin := hq.isFinite_presentation i
  haveI : P.IsFinite := @Modules.isFinite_presentationOverRestrict _ F _ _ hfin
  haveI : Finite P.generators.I :=
    SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := P.generators)
  haveI : Finite P.relations.I :=
    SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := P.relations)
  exact ⟨q.X i, hi, P.relations.I, P.generators.I, inferInstance, inferInstance, _, _, _,
    ⟨P.isColimit⟩⟩

/-- Restriction of sheaves of modules on a scheme to an open `U` is the restriction
`AlgebraicGeometry.LocallyRingedSpace.restrictModules` of the underlying locally ringed space. -/
noncomputable def Modules.restrictFunctorIsoRestrictModules (X : Scheme.{u}) (U : X.Opens) :
    Modules.restrictFunctor U.ι ≅ X.toLocallyRingedSpace.restrictModules U :=
  Modules.restrictFunctorIsoPullback U.ι

/-- **A coherent sheaf on a scheme is locally a cokernel of finite free sheaves**, for sheaves
of modules over `AlgebraicGeometry.LocallyRingedSpace.ringSheaf` and restriction
`AlgebraicGeometry.LocallyRingedSpace.restrictModules`. -/
theorem exists_restrictModules_isColimit_cokernelCofork (X : Scheme.{u})
    (F : SheafOfModules.{u} X.toLocallyRingedSpace.ringSheaf) [hF : F.IsCoherent] (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U) (I K : Type u) (_ : Finite I) (_ : Finite K)
      (ψ : SheafOfModules.free
          (R := (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).ringSheaf) I ⟶
        SheafOfModules.free K)
      (g : SheafOfModules.free K ⟶ (X.toLocallyRingedSpace.restrictModules U).obj F)
      (H : ψ ≫ g = 0), Nonempty (IsColimit (CokernelCofork.ofπ g H)) := by
  obtain ⟨U, hU, I, K, hI, hK, ψ, g, H, ⟨hc⟩⟩ :=
    @Modules.exists_restrict_isColimit_cokernelCofork X F hF x
  let e := (Modules.restrictFunctorIsoRestrictModules X U).app F
  exact ⟨U, hU, I, K, hI, hK, ψ, g ≫ e.hom,
    (Category.assoc _ _ _).symm.trans ((H =≫ e.hom).trans zero_comp),
    ⟨IsColimit.ofIsoColimit hc (Cofork.ext e rfl)⟩⟩

end AlgebraicGeometry.Scheme
