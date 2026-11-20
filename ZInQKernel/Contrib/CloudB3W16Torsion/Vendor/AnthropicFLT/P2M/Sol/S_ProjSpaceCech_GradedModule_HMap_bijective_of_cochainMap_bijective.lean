/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_ProjSpaceCech_GradedModule_HMap_bijective_of_cochainMap_bijective. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_ProjSpaceCech_GradedModule_HMap_bijective_of_cochainMap_bijective

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

universe u

noncomputable section

open Finset Function MvPolynomial

namespace ProjSpaceCech
export _root_.ProjSpaceCech (GradedModule GradedModule.cochain GradedModule.d GradedModule.Hom GradedModule.Hom.cochainMap GradedModule.Hom.cochainMap_comm GradedModule.Hom.cochainMapKer GradedModule.Hom.HMap)
open ProjSpaceCech

section HMapBijective

variable {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : GradedModule R n}

namespace GradedModule p2m_export "ProjSpaceCech.GradedModule" "cochain d Hom Hom.cochainMap Hom.cochainMap_comm Hom.cochainMapKer Hom.HMap mk" end GradedModule
open scoped ProjSpaceCech.GradedModule in
theorem GradedModule.HMap_bijective_of_cochainMap_bijective' (φ : GradedModule.Hom D₁ D₂)
    (h : ∀ i, Function.Bijective (GradedModule.Hom.cochainMap φ i)) (i : ℕ) :
    Function.Bijective (GradedModule.Hom.HMap φ i) := by
  classical
  have hcomm : ∀ k (x : GradedModule.cochain D₁ k),
      GradedModule.d D₂ k (GradedModule.Hom.cochainMap φ k x)
        = GradedModule.Hom.cochainMap φ (k + 1) (GradedModule.d D₁ k x) := fun k x => by
    rw [← LinearMap.comp_apply, GradedModule.Hom.cochainMap_comm, LinearMap.comp_apply]
  have hker : ∀ k (x : GradedModule.cochain D₁ k),
      GradedModule.Hom.cochainMap φ k x ∈ LinearMap.ker (GradedModule.d D₂ k)
        ↔ x ∈ LinearMap.ker (GradedModule.d D₁ k) := fun k x => by
    rw [LinearMap.mem_ker, LinearMap.mem_ker, hcomm]
    exact ⟨fun hx => (h (k + 1)).1 (by rw [hx, map_zero]), fun hx => by rw [hx, map_zero]⟩
  have hrange : ∀ k (y : GradedModule.cochain D₁ (k + 1)),
      GradedModule.Hom.cochainMap φ (k + 1) y ∈ LinearMap.range (GradedModule.d D₂ k)
        ↔ y ∈ LinearMap.range (GradedModule.d D₁ k) := fun k y => by
    constructor
    · rintro ⟨x', hx'⟩
      obtain ⟨x, rfl⟩ := (h k).2 x'
      exact ⟨x, (h (k + 1)).1 (by rw [← hcomm, hx'])⟩
    · rintro ⟨x, rfl⟩
      exact ⟨GradedModule.Hom.cochainMap φ k x, hcomm k x⟩
  have hkerbij : ∀ k, Function.Bijective (GradedModule.Hom.cochainMapKer φ k) := fun k => by
    constructor
    · intro x y hxy
      exact Subtype.ext ((h k).1 (congrArg Subtype.val hxy))
    · rintro ⟨z, hz⟩
      obtain ⟨x, rfl⟩ := (h k).2 z
      exact ⟨⟨x, (hker k x).mp hz⟩, rfl⟩
  rcases i with _ | j
  · exact hkerbij 0
  · simp only [GradedModule.Hom.HMap]
    constructor
    · refine (injective_iff_map_eq_zero _).mpr fun a ha => ?_
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      have ha' : GradedModule.Hom.cochainMapKer φ (j + 1) x
          ∈ (LinearMap.range (GradedModule.d D₂ j)).comap
              (LinearMap.ker (GradedModule.d D₂ (j + 1))).subtype :=
        (Submodule.Quotient.mk_eq_zero _).mp ha
      rw [Submodule.mem_comap, Submodule.subtype_apply] at ha'
      exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr ((hrange j x.1).mp ha'))
    · intro q
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨x, rfl⟩ := (hkerbij (j + 1)).2 w
      exact ⟨Submodule.Quotient.mk x, rfl⟩

end HMapBijective

end ProjSpaceCech

theorem solution {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : ProjSpaceCech.GradedModule R n}
    (φ : ProjSpaceCech.GradedModule.Hom D₁ D₂) (h : ∀ i, Function.Bijective (ProjSpaceCech.GradedModule.Hom.cochainMap φ i)) (i : ℕ) :
    Function.Bijective (ProjSpaceCech.GradedModule.Hom.HMap φ i) :=
  ProjSpaceCech.GradedModule.HMap_bijective_of_cochainMap_bijective' φ h i

end
