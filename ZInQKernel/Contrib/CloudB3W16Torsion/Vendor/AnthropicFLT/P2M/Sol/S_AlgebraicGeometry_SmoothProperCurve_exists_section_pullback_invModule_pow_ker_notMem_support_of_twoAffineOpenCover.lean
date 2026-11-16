/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_exists_section_pullback_invModule_pow_ker_notMem_support_of_twoAffineOpenCover. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_subsingleton_H1_and_finrank_H0_sectionsOf_pullback_invModule_pow_ker
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_section_pullback_invModule_pow_ker_notMem_support_of_twoAffineOpenCover

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
-- Original source-local namespace open deferred until after its declaration.
open AlgebraicCurve
open NeronModelInfra
open AlgebraicGeometry.RelPicard
open Opposite

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Modules.Hom.app_smul Surjective Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension Scheme.Modules.pushforward IsProper Scheme.Modules.pullback IsClosedImmersion.of_comp Scheme.Hom GeometricallyIntegral Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Scheme Scheme.Modules.Hom.id_app Scheme.IdealSheafData.ker_subschemeι IsClosedImmersion smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules.pullbackCongr IsClosedImmersion.lift IsClosedImmersion.lift_fac Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.Modules.toUnitSection Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackSection Scheme.Modules.pullbackSection_def Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit Scheme.IdealSheafData.IsInvertible SmoothProperCurve.subsingleton_H1_and_finrank_H0_sectionsOf_pullback_invModule_pow_ker Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso RelPicard.nonempty_pullback_sectionTwist_iso Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.IdealSheafData.IsInvertible.epi_unit_app_tensor_invModule_pow_and_exists_shortExact Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero Scheme.Modules.IsInvertible.pullbackSection_eq_zero_iff_mem_support Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso)
namespace SmoothProperCurve
export _root_.AlgebraicGeometry.SmoothProperCurve (subsingleton_H1_and_finrank_H0_sectionsOf_pullback_invModule_pow_ker)
namespace FibreNonvanishAux
open AlgebraicGeometry.SmoothProperCurve hiding specMap
open AlgebraicGeometry

variable {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (.of K))

noncomputable def appTopLinear {M N : X.Modules} (φ : M ⟶ N) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x N ⊤
    Γ(M, ⊤) →ₗ[K] Γ(N, ⊤) :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x N ⊤
  { toFun := fun v => φ.app ⊤ v
    map_add' := fun a b => map_add _ a b
    map_smul' := fun k v => by
      letI := Scheme.TwoAffineOpenCover.algebraOfHom x (⊤ : X.Opens)
      show φ.app ⊤ ((algebraMap K Γ(X, ⊤) k) • v) = (algebraMap K Γ(X, ⊤) k) • φ.app ⊤ v
      exact Scheme.Modules.Hom.app_smul φ _ v }

theorem appTopLinear_apply {M N : X.Modules} (φ : M ⟶ N) (v : Γ(M, ⊤)) :
    appTopLinear x φ v = φ.app ⊤ v := rfl

noncomputable def isoSections {M N : X.Modules} (e : M ≅ N) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x N ⊤
    Γ(M, ⊤) ≃ₗ[K] Γ(N, ⊤) :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x N ⊤
  { appTopLinear x e.hom with
    invFun := appTopLinear x e.inv
    left_inv := fun v => by
      show e.inv.app ⊤ (e.hom.app ⊤ v) = v
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id,
        Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]
    right_inv := fun v => by
      show e.hom.app ⊤ (e.inv.app ⊤ v) = v
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id,
        Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] }

theorem exists_hom_app_top_eq (N : X.Modules) (v : Γ(N, ⊤)) :
    ∃ s : 𝟙_ X.Modules ⟶ N, s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = v := by
  let sec : N.val.sections :=
    PresheafOfModules.sectionsMk (M := N.val) (fun U => N.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op v)
      (by
        intro U V f
        show (N.presheaf ⋙ forget _).map f (N.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op v) =
          N.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op v
        have hf : (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f = (homOfLE (le_top : V.unop ≤ ⊤)).op :=
          Quiver.Hom.unop_inj (Subsingleton.elim _ _)
        rw [← hf, Functor.map_comp]
        rfl)
  refine ⟨N.unitHomEquiv.symm sec, ?_⟩
  have h1 := SheafOfModules.unitHomEquiv_apply_coe N (N.unitHomEquiv.symm sec) (op ⊤)
  rw [Equiv.apply_symm_apply] at h1

  have h2 : sec.val (op ⊤) = v := by
    show N.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op v = v
    have : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [this, CategoryTheory.Functor.map_id]
    rfl
  rw [← h2, h1]
  rfl

end AlgebraicGeometry.SmoothProperCurve.FibreNonvanishAux
open _root_.P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_section_pullback_invModule_pow_ker_notMem_support_of_twoAffineOpenCover.AlgebraicGeometry

open AlgebraicGeometry.SmoothProperCurve.FibreNonvanishAux

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (m : ℕ) (hm : 2 * g ≤ m) (hm₁ : 1 ≤ m) (𝒱 : C.TwoAffineOpenCover)
    (K : Type u) [Field K] [Algebra R K] :
    ∃ s : 𝟙_ (pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Modules ⟶
        (Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K))).obj
          ((ε.1.ker ^ m).invModule),
      ∀ z : Spec (CommRingCat.of K) ⟶ pullback c (Scheme.TwoAffineOpenCover.specMap R K),
        z ≫ pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K) =
            Scheme.TwoAffineOpenCover.specMap R K ≫ ε.1 →
        z ≫ pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K) = 𝟙 _ →
        z.base (IsLocalRing.closedPoint K) ∉ (Scheme.Modules.zeroSchemeIdeal s).support := by

  let S : Scheme.{u} := Spec (CommRingCat.of R)
  let sK : Spec (CommRingCat.of K) ⟶ S := Scheme.TwoAffineOpenCover.specMap R K
  let xK : pullback c sK ⟶ Spec (CommRingCat.of K) := pullback.snd c sK
  let F : pullback c sK ⟶ C := pullback.fst c sK
  let σ : Spec (CommRingCat.of K) ⟶ pullback c sK := rigSection c sK ε
  have hσx : σ ≫ xK = 𝟙 _ := by simp only [σ, xK, rigSection, pullback.lift_snd]
  have hσF : σ ≫ F = sK ≫ ε.1 := by simp only [σ, F, rigSection, pullback.lift_fst]

  suffices h : ∃ s : 𝟙_ (pullback c sK).Modules ⟶ (Scheme.Modules.pullback F).obj ((ε.1.ker ^ m).invModule),
      σ.base (IsLocalRing.closedPoint K) ∉ (Scheme.Modules.zeroSchemeIdeal s).support by
    obtain ⟨s, hs⟩ := h
    refine ⟨s, fun z hzF hzx => ?_⟩
    have hz : z = σ := pullback.hom_ext (hzF.trans hσF.symm) (hzx.trans hσx.symm)
    rw [hz]
    exact hs

  obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := ⟨m - 1, by omega⟩

  have hεc : ε.1 ≫ c = 𝟙 S := ε.2
  haveI : IsClosedImmersion (ε.1 ≫ c) := by rw [hεc]; infer_instance
  haveI : IsClosedImmersion ε.1 := IsClosedImmersion.of_comp ε.1 c
  have hIε : ε.1.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id ε.1 hεc
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c (𝟙 S)) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  haveI : SmoothOfRelativeDimension 1 xK :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have hσ1 : rigSection c (𝟙 S) ε ≫ pullback.snd c (𝟙 S) = 𝟙 S := by simp only [rigSection, pullback.lift_snd]
  have hI1 : (rigSection c (𝟙 S) ε).ker.IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c (𝟙 S) ε) hσ1
  have hσ1π : rigSection c (𝟙 S) ε ≫ pullback.fst c (𝟙 S) = ε.1 := by
    simp only [rigSection, pullback.lift_fst, Category.id_comp]
  haveI : IsClosedImmersion (σ ≫ xK) := by rw [hσx]; infer_instance
  haveI : IsClosedImmersion σ := IsClosedImmersion.of_comp σ xK
  have hIσ : σ.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id σ hσx

  let ψ : SchemeHomOver sK (𝟙 S) := ⟨sK, Category.comp_id _⟩
  let g₁ : pullback c sK ⟶ pullback c (𝟙 S) := baseChangeSnd c ψ
  let π : pullback c (𝟙 S) ⟶ C := pullback.fst c (𝟙 S)
  have hg₁π : g₁ ≫ π = F := by
    simp only [g₁, π, F, baseChangeSnd, pullback.lift_fst, Category.comp_id]
  have eT : ∀ r : ℕ, Nonempty ((Scheme.Modules.pullback F).obj ((ε.1.ker ^ r).invModule) ≅ (σ.ker ^ r).invModule) := by
    intro r
    obtain ⟨eπ⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso π ε.1
      (rigSection c (𝟙 S) ε) hσ1π hIε hI1 r).1
    obtain ⟨eψ⟩ := RelPicard.nonempty_pullback_sectionTwist_iso R c ε ψ r
    exact ⟨(Scheme.Modules.pullbackCongr hg₁π.symm).app _ ≪≫ ((Scheme.Modules.pullbackComp g₁ π).app _).symm ≪≫
      (Scheme.Modules.pullback g₁).mapIso eπ ≪≫ eψ⟩

  let P : (pullback c sK).Modules := (σ.ker ^ (d + 1)).invModule
  have hP : Scheme.Modules.IsInvertible P := (hIσ.pow (d + 1)).isInvertible_invModule
  let G : (pullback c sK).Modules := 𝟙_ _ ⊗ P
  let Gd : (pullback c sK).Modules := 𝟙_ _ ⊗ (σ.ker ^ d).invModule
  let i := (σ.ker ^ 1).subschemeι
  let η := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app G
  obtain ⟨-, ι, w, hSE⟩ :=
    Scheme.IdealSheafData.IsInvertible.epi_unit_app_tensor_invModule_pow_and_exists_shortExact
      σ.ker hIσ (𝟙_ _) (Scheme.Modules.isInvertible_unit _) (d + 1) 1 d rfl
  obtain ⟨em⟩ := eT (d + 1)
  obtain ⟨ed⟩ := eT d
  let θm : (Scheme.Modules.pullback F).obj ((ε.1.ker ^ (d + 1)).invModule) ≅ G := em ≪≫ (λ_ P).symm
  let θd : (Scheme.Modules.pullback F).obj ((ε.1.ker ^ d).invModule) ≅ Gd := ed ≪≫ (λ_ _).symm

  letI iGm := Scheme.TwoAffineOpenCover.moduleSectionsOfHom xK G ⊤
  letI iGd := Scheme.TwoAffineOpenCover.moduleSectionsOfHom xK Gd ⊤
  letI iFm := Scheme.TwoAffineOpenCover.moduleSectionsOfHom xK
    ((Scheme.Modules.pullback F).obj ((ε.1.ker ^ (d + 1)).invModule)) ⊤
  letI iFd := Scheme.TwoAffineOpenCover.moduleSectionsOfHom xK
    ((Scheme.Modules.pullback F).obj ((ε.1.ker ^ d).invModule)) ⊤
  have hGm : Module.finrank K Γ(G, ⊤) = d + 1 + 1 - g := by
    obtain ⟨-, h0⟩ :=
      AlgebraicGeometry.SmoothProperCurve.subsingleton_H1_and_finrank_H0_sectionsOf_pullback_invModule_pow_ker
        R c ε g hg (d + 1) (by omega) 𝒱 K
    obtain ⟨eH, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 (𝒱.pullback c K) xK
      ((Scheme.Modules.pullback F).obj ((ε.1.ker ^ (d + 1)).invModule))
    rw [← h0, ← eH.finrank_eq, (isoSections xK θm).finrank_eq]
  have hGd : Module.finrank K Γ(Gd, ⊤) = d + 1 - g := by
    obtain ⟨-, h0⟩ :=
      AlgebraicGeometry.SmoothProperCurve.subsingleton_H1_and_finrank_H0_sectionsOf_pullback_invModule_pow_ker
        R c ε g hg d (by omega) 𝒱 K
    obtain ⟨eH, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 (𝒱.pullback c K) xK
      ((Scheme.Modules.pullback F).obj ((ε.1.ker ^ d).invModule))
    rw [← h0, ← eH.finrank_eq, (isoSections xK θd).finrank_eq]

  suffices h : ∃ s' : 𝟙_ _ ⟶ G, σ.base (IsLocalRing.closedPoint K) ∉ (Scheme.Modules.zeroSchemeIdeal s').support by
    obtain ⟨s', hs'⟩ := h
    refine ⟨s' ≫ θm.inv, ?_⟩
    rwa [Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso]
  by_contra hall
  simp only [not_exists, not_not] at hall

  have hτ : σ.ker ≤ i.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, pow_one]
  let τ := IsClosedImmersion.lift σ i hτ
  have hτσ : τ ≫ σ = i := IsClosedImmersion.lift_fac σ i hτ
  have hA : ∀ s' : 𝟙_ _ ⟶ G, s' ≫ η = 0 := by
    intro s'

    have hmem := hall s'
    have hZ : Scheme.Modules.zeroSchemeIdeal (s' ≫ (λ_ P).hom) = Scheme.Modules.zeroSchemeIdeal s' :=
      Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso _ _
    rw [← hZ] at hmem
    have h0 : Scheme.Modules.pullbackSection σ (s' ≫ (λ_ P).hom) = 0 :=
      (Scheme.Modules.IsInvertible.pullbackSection_eq_zero_iff_mem_support hP _ σ).mpr hmem
    rw [Scheme.Modules.pullbackSection_def] at h0
    have h1 : (Scheme.Modules.pullback σ).map (s' ≫ (λ_ P).hom) = 0 :=
      (cancel_epi _).mp (h0.trans comp_zero.symm)
    rw [Functor.map_comp] at h1
    have h2 : (Scheme.Modules.pullback σ).map s' = 0 :=
      (cancel_mono _).mp (h1.trans zero_comp.symm)

    have h3 : (Scheme.Modules.pullback (τ ≫ σ)).map s' = 0 := by
      have nat := (Scheme.Modules.pullbackComp τ σ).hom.naturality s'
      have h5 : (Scheme.Modules.pullback τ).map ((Scheme.Modules.pullback σ).map s') = 0 := by
        rw [h2, Functor.map_zero]
      rw [Functor.comp_map, h5] at nat
      have h6 : (Scheme.Modules.pullbackComp τ σ).hom.app _ ≫ (Scheme.Modules.pullback (τ ≫ σ)).map s' = 0 :=
        nat.symm.trans zero_comp
      exact (cancel_epi _).mp (h6.trans comp_zero.symm)
    have h4 : (Scheme.Modules.pullback i).map s' = 0 := by
      have nat := (Scheme.Modules.pullbackCongr hτσ).hom.naturality s'
      rw [h3] at nat
      have h6 : (Scheme.Modules.pullbackCongr hτσ).hom.app _ ≫ (Scheme.Modules.pullback i).map s' = 0 :=
        nat.symm.trans zero_comp
      exact (cancel_epi _).mp (h6.trans comp_zero.symm)

    have nat := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.naturality s'
    have h5 : (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map s') = 0 := by
      rw [h4, Functor.map_zero]
    rw [Functor.comp_map, h5, Functor.id_map] at nat
    exact nat.trans comp_zero

  have hB : ∀ v : Γ(G, ⊤), η.app ⊤ v = 0 := by
    intro v
    obtain ⟨s', hs'⟩ := exists_hom_app_top_eq G v
    rw [← hs']
    have h := congrArg (fun φ => φ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) (hA s')
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app] at h
    exact h

  haveI : Mono (ShortComplex.mk ι _ w).f := hSE.mono_f
  have hC : Function.Surjective (appTopLinear xK ι) := by
    intro v
    obtain ⟨e, he⟩ := Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero (ShortComplex.mk ι _ w) hSE.exact ⊤ v (hB v)
    exact ⟨e, he⟩

  have hpos : 0 < Module.finrank K Γ(Gd, ⊤) := by rw [hGd]; omega
  haveI : Module.Finite K Γ(Gd, ⊤) := Module.finite_of_finrank_pos hpos
  have hle : Module.finrank K Γ(G, ⊤) ≤ Module.finrank K Γ(Gd, ⊤) := by
    have := LinearMap.finrank_range_le (appTopLinear xK ι)
    rwa [LinearMap.range_eq_top.mpr hC, finrank_top] at this
  rw [hGm, hGd] at hle
  omega
