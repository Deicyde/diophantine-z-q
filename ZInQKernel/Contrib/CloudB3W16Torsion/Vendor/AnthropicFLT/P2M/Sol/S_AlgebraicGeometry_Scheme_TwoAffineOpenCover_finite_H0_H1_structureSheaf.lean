/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finite_H0_H1_structureSheaf. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isProper
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finite_H0_H1_structureSheaf

set_option autoImplicit false

universe u

namespace TwoChartCech
export TwoChartCech (Cover Sections Sections.cechDiff_apply Cover.lineBundle_r0_apply Cover.lineBundle_r1_apply kerMap cokerMap)
namespace Sk1
open TwoChartCech

universe uR uK uC

variable {R : Type uR} [CommRing R]
variable {K0 K1 : Type uK} [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
variable {C0 C1 : Type uK} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

theorem kerMap_bijective_of_bijective (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0)
    (ι1 : K1 →ₗ[R] C1) (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (h0 : Function.Bijective ι0)
    (h1 : Function.Injective ι1) : Function.Bijective (kerMap dK d ι0 ι1 comm) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply h0.1
    exact congrArg Subtype.val hxy
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := h0.2 y
    have hx : x ∈ LinearMap.ker dK := by
      rw [LinearMap.mem_ker] at hy ⊢
      apply h1
      rw [map_zero, ← LinearMap.comp_apply, ← comm, LinearMap.comp_apply, hy]
    exact ⟨⟨x, hx⟩, rfl⟩

theorem cokerMap_bijective_of_bijective (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0)
    (ι1 : K1 →ₗ[R] C1) (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (h0 : Function.Surjective ι0)
    (h1 : Function.Bijective ι1) : Function.Bijective (cokerMap dK d ι0 ι1 comm) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.mem_ker] at hq
    change Submodule.Quotient.mk (ι1 y) = 0 at hq
    rw [Submodule.Quotient.mk_eq_zero] at hq ⊢
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hq
    obtain ⟨x, rfl⟩ := h0 c
    refine ⟨x, h1.1 ?_⟩
    rw [← hc, ← LinearMap.comp_apply, ← comm, LinearMap.comp_apply]
  · intro q
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨y, rfl⟩ := h1.2 c
    exact ⟨Submodule.Quotient.mk y, rfl⟩

end TwoChartCech.Sk1

open CategoryTheory AlgebraicGeometry in

theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (.of R)) [IsProper c] :
    Module.Finite R (𝒱.structureSheafSections c).H0 ∧ Module.Finite R (𝒱.structureSheafSections c).H1 := by
  obtain ⟨h0, h1⟩ := (AlgebraicGeometry.OModulePresheaf.cechFinite_toOrderedAffineCover_iff
    (OModulePresheaf.unit c) 𝒱).mp (OModulePresheaf.cechFinite_unit_of_isProper c 𝒱.toOrderedAffineCover)

  let S := (OModulePresheaf.unit c).twoChartSections 𝒱
  let T := 𝒱.structureSheafSections c
  let ι0 : S.M0 × S.M1 →ₗ[R] T.M0 × T.M1 :=
    { toFun := fun p => p, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let ι1 : S.M01 →ₗ[R] T.M01 :=
    { toFun := fun p => p, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have comm : T.cechDiff ∘ₗ ι0 = ι1 ∘ₗ S.cechDiff := by
    apply LinearMap.ext
    rintro ⟨x0, x1⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, TwoChartCech.Sections.cechDiff_apply,
      TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Cover.lineBundle_r1_apply,
      TwoChartCech.Cover.lineBundle_r0_apply, Units.val_one, one_mul]
    rfl
  have hι0 : Function.Bijective ι0 := ⟨fun _ _ h => h, fun p => ⟨p, rfl⟩⟩
  have hι1 : Function.Bijective ι1 := ⟨fun _ _ h => h, fun p => ⟨p, rfl⟩⟩
  haveI := h0
  haveI := h1
  exact ⟨Module.Finite.equiv (LinearEquiv.ofBijective _
      (TwoChartCech.Sk1.kerMap_bijective_of_bijective S.cechDiff T.cechDiff ι0 ι1 comm hι0 hι1.1)),
    Module.Finite.equiv (LinearEquiv.ofBijective _
      (TwoChartCech.Sk1.cokerMap_bijective_of_bijective S.cechDiff T.cechDiff ι0 ι1 comm hι0.2 hι1))⟩
