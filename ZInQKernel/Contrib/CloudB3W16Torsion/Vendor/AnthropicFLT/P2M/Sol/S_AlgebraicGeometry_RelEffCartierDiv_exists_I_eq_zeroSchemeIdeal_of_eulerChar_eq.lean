/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_invModule_zeroSchemeIdeal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_eulerChar_tensor_lineBundle_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

namespace T1Ws13

theorem cover_ext {X : Scheme.{u}} (𝒱 𝒲 : X.TwoAffineOpenCover) (h0 : 𝒱.U0 = 𝒲.U0) (h1 : 𝒱.U1 = 𝒲.U1) :
    𝒱 = 𝒲 := by
  cases 𝒱; cases 𝒲; cases h0; cases h1; rfl

theorem invModuleSection_comp_eqToHom {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    I.invModuleSection ≫ eqToHom (by rw [h]) = J.invModuleSection := by
  subst h; simp

end T1Ws13

set_option maxHeartbeats 6400000 in
open T1Ws13 in
theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    {M : (pullback f x).Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ (pullback f x).Modules ⟶ M) (hs : s ≠ 0)
    (𝒱 : (pullback f x).TwoAffineOpenCover) (d : ℕ)
    (hχ : (Module.finrank k (𝒱.sectionsOf (pullback.snd f x) M).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd f x) M).H1
      = (Module.finrank k (𝒱.sectionsOf (pullback.snd f x) (𝟙_ (pullback f x).Modules)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd f x) (𝟙_ (pullback f x).Modules)).H1 + d) :
    ∃ D : RelEffCartierDiv f d x, D.I = Scheme.Modules.zeroSchemeIdeal s ∧
      ∃ e : M ≅ D.lineBundle, s ≫ e.hom = D.I.invModuleSection := by
  classical

  obtain ⟨r, ⟨I, hfin, hflat, hlofp, hrk⟩, hD⟩ :=
    RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper x hM s hs
  subst hD
  set D : RelEffCartierDiv f r x := ⟨Scheme.Modules.zeroSchemeIdeal s, hfin, hflat, hlofp, hrk⟩ with hDdef

  have hZ : (Scheme.Modules.zeroSchemeIdeal s).IsInvertible := RelEffCartierDiv.isInvertible_I D
  obtain ⟨e, he⟩ := Scheme.Modules.IsInvertible.exists_iso_invModule_zeroSchemeIdeal hM s hZ

  let ι₁ : (𝟙_ (pullback f x).Modules ⊗ D.lineBundle) ≅
      (Scheme.Modules.pullback (𝟙 (pullback f x))).obj M :=
    (λ_ D.lineBundle) ≪≫ e.symm ≪≫ ((Scheme.Modules.pullbackId (pullback f x)).app M).symm
  obtain ⟨𝒱₂, hU0, hU1, ⟨l0⟩, ⟨l1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso (pullback.snd f x) (pullback.snd f x)
      (Iso.refl _) (Category.id_comp _) 𝒱 M (𝟙_ (pullback f x).Modules ⊗ D.lineBundle) ι₁
  have h𝒱 : 𝒱₂ = 𝒱 := cover_ext 𝒱₂ 𝒱 (by rw [hU0]; rfl) (by rw [hU1]; rfl)
  subst h𝒱

  have hunit : Scheme.Modules.IsInvertible (𝟙_ (pullback f x).Modules) := Scheme.Modules.isInvertible_unit _
  have hχ2 := RelEffCartierDiv.eulerChar_tensor_lineBundle_eq x D (𝟙_ (pullback f x).Modules) hunit 𝒱₂
  have e0 := l0.finrank_eq
  have e1 := l1.finrank_eq

  have hrd : r = d := by
    have : (r : ℤ) = d := by
      rw [e0, e1] at hχ2
      linarith
    exact_mod_cast this
  subst hrd
  exact ⟨D, rfl, e, he⟩
