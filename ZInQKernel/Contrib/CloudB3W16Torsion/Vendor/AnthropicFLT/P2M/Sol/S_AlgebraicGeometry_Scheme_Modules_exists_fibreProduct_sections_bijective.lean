/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
-- Source P2M scope referred to a not-yet-declared local namespace; root scope retained.
open Opposite
open TopologicalSpace

namespace AlgebraicGeometry
export AlgebraicGeometry (Scheme Scheme.Modules)
namespace Scheme
export AlgebraicGeometry.Scheme (forget Γ Modules Opens evaluation)
namespace Modules
export AlgebraicGeometry.Scheme.Modules (toPresheaf pullback presheaf)
namespace FibreProductSections
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme
open AlgebraicGeometry

variable {X : Scheme.{u}}

noncomputable def evalForget (U : X.Opens) : TopCat.Presheaf Ab X ⥤ Type u :=
  (CategoryTheory.evaluation _ _).obj (op U) ⋙ CategoryTheory.forget Ab

noncomputable scoped instance (U : X.Opens) : PreservesLimitsOfShape WalkingCospan (evalForget (X := X) U) :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan
    ((CategoryTheory.evaluation (Opens X)ᵒᵖ Ab.{u}).obj (op U) ⋙ CategoryTheory.forget Ab.{u}))

noncomputable def sectionsFunctorAt (U : X.Opens) : X.Modules ⥤ Type u :=
  toPresheaf X ⋙ evalForget U

noncomputable scoped instance (U : X.Opens) :
    PreservesLimitsOfShape WalkingCospan (sectionsFunctorAt (X := X) U) := by
  unfold sectionsFunctorAt; infer_instance

theorem sectionsFunctorAt_map {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) (x : Γ(M, U)) :
    (sectionsFunctorAt U).map φ x = φ.app U x := rfl

end AlgebraicGeometry.Scheme.Modules.FibreProductSections




open CategoryTheory.Limits _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.FibreProductSections in

theorem solution
    {X : Scheme.{u}} {N₀ N₁ N₀₁ : X.Modules} (a : N₀ ⟶ N₀₁) (b : N₁ ⟶ N₀₁) :
    ∃ (L : X.Modules) (π₀ : L ⟶ N₀) (π₁ : L ⟶ N₁), π₀ ≫ a = π₁ ≫ b ∧
      (∀ U : X.Opens, Function.Injective fun s : Γ(L, U) => (π₀.app U s, π₁.app U s)) ∧
      (∀ (U : X.Opens) (s₀ : Γ(N₀, U)) (s₁ : Γ(N₁, U)), a.app U s₀ = b.app U s₁ →
        ∃ s : Γ(L, U), π₀.app U s = s₀ ∧ π₁.app U s = s₁) := by
  have key : ∀ U : X.Opens, ∃ e : (Γ(Limits.pullback a b, U) : Type u) ≃
      Types.PullbackObj ((sectionsFunctorAt U).map a) ((sectionsFunctorAt U).map b),
      ∀ s, (e s).1.1 = (pullback.fst a b).app U s ∧ (e s).1.2 = (pullback.snd a b).app U s := by
    intro U
    have hc := isLimitPullbackConeMapOfIsLimit (sectionsFunctorAt U) pullback.condition
      (pullbackIsPullback a b)
    exact ⟨PullbackCone.IsLimit.equivPullbackObj hc, fun s =>
      ⟨PullbackCone.IsLimit.equivPullbackObj_apply_fst hc s,
       PullbackCone.IsLimit.equivPullbackObj_apply_snd hc s⟩⟩
  refine ⟨Limits.pullback a b, pullback.fst a b, pullback.snd a b, pullback.condition, ?_, ?_⟩
  · intro U s t hst
    obtain ⟨e, he⟩ := key U
    apply e.injective
    refine Subtype.ext (Prod.ext ?_ ?_)
    · rw [(he s).1, (he t).1]; exact congrArg Prod.fst hst
    · rw [(he s).2, (he t).2]; exact congrArg Prod.snd hst
  · intro U s₀ s₁ h
    obtain ⟨e, he⟩ := key U
    refine ⟨e.symm ⟨(s₀, s₁), h⟩, ?_, ?_⟩
    · have := (he (e.symm ⟨(s₀, s₁), h⟩)).1
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    · have := (he (e.symm ⟨(s₀, s₁), h⟩)).2
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
