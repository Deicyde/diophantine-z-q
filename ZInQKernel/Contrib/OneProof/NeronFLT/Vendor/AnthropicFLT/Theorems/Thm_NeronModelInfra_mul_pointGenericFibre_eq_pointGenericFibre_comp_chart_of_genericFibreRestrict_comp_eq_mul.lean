/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NeronModelInfra_mul_pointGenericFibre_eq_pointGenericFibre_comp_chart_of_genericFibreRestrict_comp_eq_mul
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_OmegaMinimalComponentData
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_NeronModelInfra_mul_pointGenericFibre_eq_pointGenericFibre_comp_chart_of_genericFibreRestrict_comp_eq_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.mul_pointGenericFibre_eq_pointGenericFibre_comp_chart_of_genericFibreRestrict_comp_eq_mul
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤))
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [IsIso e.1]
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (η : ↑(pullback z f))
    (T : ComponentReading R K gK d ω)
    (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀) (τ₀ : SchemeHomOver (U₀.ι ≫ pullback.fst z f ≫ z) T.f)
    (hτ₀ : (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K T.f (U₀.ι ≫ pullback.fst z f ≫ z) τ₀) T.e).1 =
            pullback.map (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U₀.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f) (hv₁ : v ≫ pullback.fst z T.f = U₀.ι ≫ pullback.fst z f)
    (hv₂ : v ≫ pullback.snd z T.f = τ₀.1)

    [Algebra R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)))]
    (halgZ : Z.fromSpecStalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))))))
    [Algebra R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)]
    (halgO : (U₀ : Scheme.{u}).fromSpecStalk ⟨η, hηU⟩ ≫ (U₀.ι ≫ pullback.fst z f ≫ z) =
      Spec.map (CommRingCat.ofHom (algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))))
    [Algebra R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))]
    (halg₁ : T.Y.fromSpecStalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)) ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))))))

    (K' F : Type u) [Field K'] [Algebra (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) K'] [IsFractionRing (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) K'] [Algebra R K'] [Algebra K K']
    [IsScalarTower R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) K'] [IsScalarTower R K K']
    [Field F] [Algebra ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F] [Algebra R F] [Algebra K F] [Algebra K' F] [Algebra (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) F]
    [IsScalarTower R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F] [IsScalarTower R K F] [IsScalarTower K K' F] [IsScalarTower (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) K' F]
    (hRO : (algebraMap (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) F) =
      (algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F).comp ((v.stalkMap ⟨η, hηU⟩).hom.comp
        ((pullback.fst z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom))
    [Algebra (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) F] [IsScalarTower R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) F]
    (hτF : (algebraMap (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) F) =
      (algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F).comp ((v.stalkMap ⟨η, hηU⟩).hom.comp
        ((pullback.snd z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom)) :
    (LXK.mul (Spec.map (CommRingCat.ofHom (algebraMap K F)))
        ⟨Spec.map (CommRingCat.ofHom (algebraMap K' F)) ≫
            (NeronModelInfra.schemeHomOverComp
              (pointGenericFibre (K := K) (K' := K')
                (⟨Z.fromSpecStalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)), halgZ⟩ :
                  SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)))))) z)) uK).1, by
          rw [Category.assoc, (NeronModelInfra.schemeHomOverComp _ uK).2, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← IsScalarTower.algebraMap_eq]⟩
        (NeronModelInfra.schemeHomOverComp
          (pointGenericFibre (K := K) (K' := F)
            (⟨(U₀ : Scheme.{u}).fromSpecStalk ⟨η, hηU⟩, halgO⟩ :
              SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))) (U₀.ι ≫ pullback.fst z f ≫ z)))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U₀.ι ≫ pullback.fst z f ≫ z)
              ⟨U₀.ι ≫ pullback.snd z f, by rw [Category.assoc, ← pullback.condition]⟩) e))).1 =
      (NeronModelInfra.schemeHomOverComp
        (pointGenericFibre (K := K) (K' := F)
          (⟨T.Y.fromSpecStalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)), halg₁⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))))) T.f))
        T.e).1 := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_mul_pointGenericFibre_eq_pointGenericFibre_comp_chart_of_genericFibreRestrict_comp_eq_mul.solution
