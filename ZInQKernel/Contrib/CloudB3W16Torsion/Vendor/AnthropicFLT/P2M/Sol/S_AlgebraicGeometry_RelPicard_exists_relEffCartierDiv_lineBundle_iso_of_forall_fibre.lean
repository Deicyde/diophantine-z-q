/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibre_eq_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_tensorUnit
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_pullback_map_counit_app_ne_zero_of_forall_fibre
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_forall_fibre
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve

set_option maxHeartbeats 6400000 in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (𝟙_ (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).Modules)).H1 = g)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 = 1) :
    ∃ (D : RelEffCartierDiv c g t) (N : T.Modules), Scheme.Modules.IsInvertible N ∧
      Nonempty (D.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj N) ∧
      ∀ (d' : ℕ) (D' : RelEffCartierDiv c d' t) (N' : T.Modules), Scheme.Modules.IsInvertible N' →
        Nonempty (D'.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj N') → D'.I = D.I := by
  classical

  have hP1 := isLocallyFreeOfRank_pushforward_of_forall_fibre R c ε h𝔉 t M hM 1 hfib
  set q := pullback.snd c t with hq
  set P := (Scheme.Modules.pushforward q).obj M with hPdef
  have hP : Scheme.Modules.IsInvertible P := (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible P).mp hP1
  set X := (Scheme.Modules.pullback q).obj P with hXdef
  have hX : Scheme.Modules.IsInvertible X := hP.pullback q

  set φ : X ⟶ M := (Scheme.Modules.pullbackPushforwardAdjunction q).counit.app M with hφ
  have hev := Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit hX
  obtain ⟨s, hs⟩ : ∃ s : 𝟙_ (pullback c t).Modules ⟶ M ⊗ Scheme.Modules.dual X,
      (ihom.ev X).app (𝟙_ (pullback c t).Modules) ≫ s = φ ▷ Scheme.Modules.dual X :=
    ⟨CategoryTheory.inv ((ihom.ev X).app (𝟙_ (pullback c t).Modules)) (I := hev) ≫ φ ▷ Scheme.Modules.dual X,
      @IsIso.hom_inv_id_assoc _ _ _ _ _ hev _ _⟩

  have hNZ : ∀ (k : Type u) [Field k] (x : Spec (CommRingCat.of k) ⟶ T),
      Scheme.Modules.pullbackSection (mapOnProdOver c x rfl) s ≠ 0 := by
    intro k _ x h0
    exact pullback_map_counit_app_ne_zero_of_forall_fibre R c ε h𝔉 t M hM hfib x
      ((Scheme.Modules.IsInvertible.pullbackSection_transposeSection_eq_zero_iff
        (mapOnProdOver c x rfl) hX φ s hs).mp h0)

  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t
  have hMX : Scheme.Modules.IsInvertible (M ⊗ Scheme.Modules.dual X) := hM.tensor hX.dual.1
  obtain ⟨ePd⟩ := Scheme.Modules.IsInvertible.pullback_dual q hP
  obtain ⟨D, hDI, ⟨eD, heD⟩⟩ := RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal (f := c) (g := t) hMX s g (by
    intro k _ _ x
    rw [hMX.comap_zeroSchemeIdeal (mapOnProdOver c x rfl) s]

    have hcart : IsPullback (mapOnProdOver c x rfl) (pullback.snd c (x ≫ t)) q x :=
      isPullback_mapOnProdOver c x rfl

    letI : Algebra R k := (Spec.preimage (x ≫ t)).hom.toAlgebra
    have hxt : Spec.map (CommRingCat.ofHom (algebraMap R k)) = x ≫ t := by
      show Spec.map (CommRingCat.ofHom (Spec.preimage (x ≫ t)).hom) = _
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    obtain ⟨𝔉, -⟩ := h𝔉 0
    obtain ⟨𝔉k, -, -, -, -⟩ := 𝔉.exists_baseChange k
    obtain ⟨𝒱⟩ : Nonempty ((pullback c (x ≫ t)).TwoAffineOpenCover) := hxt ▸ ⟨𝔉k.twoAffineOpenCover⟩

    set g' := mapOnProdOver c x rfl with hg'
    have hPx : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback x).obj (Scheme.Modules.dual P)) :=
      hP.dual.1.pullback x
    obtain ⟨eNk⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k _ hPx
    have hcomp : g' ≫ q = pullback.snd c (x ≫ t) ≫ x := hcart.w
    let eDX : (Scheme.Modules.pullback g').obj (Scheme.Modules.dual X) ≅ 𝟙_ (pullback c (x ≫ t)).Modules :=
      (Scheme.Modules.pullback g').mapIso ePd.symm ≪≫
        ((Scheme.Modules.pullbackComp g' q).app (Scheme.Modules.dual P)) ≪≫
        ((Scheme.Modules.pullbackCongr hcomp).app (Scheme.Modules.dual P)) ≪≫
        ((Scheme.Modules.pullbackComp (pullback.snd c (x ≫ t)) x).app (Scheme.Modules.dual P)).symm ≪≫
        (Scheme.Modules.pullback (pullback.snd c (x ≫ t))).mapIso eNk ≪≫
        (Functor.Monoidal.εIso (Scheme.Modules.pullback (pullback.snd c (x ≫ t)))).symm
    let eF : (Scheme.Modules.pullback g').obj (M ⊗ Scheme.Modules.dual X) ≅ (Scheme.Modules.pullback g').obj M :=
      (Functor.Monoidal.μIso (Scheme.Modules.pullback g') M (Scheme.Modules.dual X)).symm ≪≫
        whiskerLeftIso _ eDX ≪≫ ρ_ _
    obtain ⟨𝒲, ⟨l0⟩, ⟨l1⟩⟩ := exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback c t M x
      (pullback.snd c (x ≫ t)) g' hcart _ eF 𝒱
    obtain ⟨hW1, hW0⟩ := hfib k x 𝒲
    have hF1 : Module.finrank k (𝒱.sectionsOf (pullback.snd c (x ≫ t))
        ((Scheme.Modules.pullback g').obj (M ⊗ Scheme.Modules.dual X))).H1 = 0 := by
      haveI := l1.toEquiv.subsingleton
      exact Module.finrank_zero_of_subsingleton
    have hF0 : Module.finrank k (𝒱.sectionsOf (pullback.snd c (x ≫ t))
        ((Scheme.Modules.pullback g').obj (M ⊗ Scheme.Modules.dual X))).H0 = 1 := by
      rw [l0.finrank_eq, hW0]

    have hO0 := finrank_H0_unit_fibre_eq_one c k (x ≫ t) 𝒱
    have hcart1 : IsPullback (mapOnProdOver c (x ≫ t) (Category.comp_id (x ≫ t)))
        (pullback.snd c (x ≫ t)) (pullback.snd c (𝟙 _)) (x ≫ t) :=
      isPullback_mapOnProdOver c (x ≫ t) (Category.comp_id (x ≫ t))
    obtain ⟨𝒲1, -, ⟨m1⟩⟩ := exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback c (𝟙 _)
      (𝟙_ (pullback c (𝟙 (Spec (CommRingCat.of R)))).Modules) (x ≫ t) (pullback.snd c (x ≫ t))
      (mapOnProdOver c (x ≫ t) (Category.comp_id (x ≫ t))) hcart1 (𝟙_ _)
      (Functor.Monoidal.εIso (Scheme.Modules.pullback (mapOnProdOver c (x ≫ t) (Category.comp_id (x ≫ t))))) 𝒱

    obtain ⟨𝒲2, hU0, hU1, -, ⟨m2⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      (fibreAt c (𝟙 _) (x ≫ t)) (fibreAt c (𝟙 _) (x ≫ t)) (Iso.refl _) (Category.id_comp _) 𝒲1
      (fibreModule c (𝟙 _) (x ≫ t) (𝟙_ _)) (𝟙_ _)
      ((Functor.Monoidal.εIso (Scheme.Modules.pullback _)) ≪≫
        ((Scheme.Modules.pullbackId _).app _).symm)
    have h𝒲 : 𝒲2 = 𝒲1 := by
      cases 𝒲2; cases 𝒲1; simp only at hU0 hU1; subst hU0; subst hU1; rfl
    subst h𝒲
    have hO1 : Module.finrank k (𝒱.sectionsOf (pullback.snd c (x ≫ t)) (𝟙_ _)).H1 = g := by
      rw [m1.finrank_eq, ← m2.finrank_eq]; exact hg k (x ≫ t) 𝒲2

    have hχ : (Module.finrank k (𝒱.sectionsOf (pullback.snd c (x ≫ t))
          ((Scheme.Modules.pullback g').obj (M ⊗ Scheme.Modules.dual X))).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd c (x ≫ t))
          ((Scheme.Modules.pullback g').obj (M ⊗ Scheme.Modules.dual X))).H1
      = (Module.finrank k (𝒱.sectionsOf (pullback.snd c (x ≫ t)) (𝟙_ _)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd c (x ≫ t)) (𝟙_ _)).H1 + g := by
      rw [hF0, hF1, hO0, hO1]; push_cast; ring
    obtain ⟨Dx, hDx, -⟩ := RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq (f := c) (x ≫ t)
      (hMX.pullback g') (Scheme.Modules.pullbackSection g' s) (hNZ k x) 𝒱 g hχ
    exact ⟨Dx, hDx⟩)

  refine ⟨D, Scheme.Modules.dual P, ?_, ⟨eD.symm ≪≫ (whiskerLeftIso M ePd.symm)⟩, ?_⟩
  · exact hP.dual.1
  · intro d' D' N' hN' hiso
    exact relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_forall_fibre R c ε h𝔉 t M hM hfib
      D' D N' (Scheme.Modules.dual P) hN' hP.dual.1 hiso.some (eD.symm ≪≫ (whiskerLeftIso M ePd.symm))
