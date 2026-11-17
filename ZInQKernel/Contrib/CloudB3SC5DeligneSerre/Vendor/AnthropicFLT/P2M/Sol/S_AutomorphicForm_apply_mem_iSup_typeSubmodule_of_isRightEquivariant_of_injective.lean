/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective (git blob 9627fa9cdc0959c7a3f0838d746e61cd976f6ff1, sha256 e65c8fa88a5e453242e1adedcb7834e3f313b2187a1f1200b5c080e81c7e3471).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_isRightEquivariant_comp_subtype_eq_of_injective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective

set_option autoImplicit false

open _root_.AutomorphicForm
namespace AutomorphicForm
end AutomorphicForm
open _root_.P2MW.S_AutomorphicForm_apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective.AutomorphicForm

namespace AutomorphicForm
export _root_.AutomorphicForm (IsRightEquivariant typeSubmodule mem_typeSubmodule_of_isRightEquivariant exists_isRightEquivariant_comp_subtype_eq_of_injective)
namespace TypePush
open _root_.AutomorphicForm

variable {H K G : Type*} [Group H] [Group K] [Group G]

def rightRegular (j : H →* K) : Representation ℂ H (K → ℂ) where
  toFun k :=
    { toFun := fun u κ => u (κ * j k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    apply LinearMap.ext
    intro u
    funext κ
    show u (κ * j 1) = u κ
    rw [map_one, mul_one]
  map_mul' k k' := by
    apply LinearMap.ext
    intro u
    funext κ
    show u (κ * j (k * k')) = u (κ * j k * j k')
    rw [map_mul, mul_assoc]

theorem rightRegular_apply (j : H →* K) (k : H) (u : K → ℂ) :
    rightRegular j k u = fun κ => u (κ * j k) :=
  rfl

theorem map_typeSubmodule_le_of_isRightEquivariant (j : H →* K) (ι' : H →* G)
    (Text : (K → ℂ) →ₗ[ℂ] (G → ℂ)) (hText : IsRightEquivariant ι' (rightRegular j) Text)
    {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W) :
    (typeSubmodule j ρ).map Text ≤ typeSubmodule ι' ρ := by
  show (Submodule.span ℂ _).map Text ≤ _
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨f, ⟨T, hT, v, rfl⟩, rfl⟩
  have hTT : IsRightEquivariant ι' ρ (Text ∘ₗ T) := by
    intro k v' x
    show Text (T (ρ k v')) x = Text (T v') (x * ι' k)
    have h1 : T (ρ k v') = rightRegular j k (T v') := funext fun κ => hT k v' κ
    rw [h1]
    exact hText k (T v') x
  exact mem_typeSubmodule_of_isRightEquivariant hTT v

end AutomorphicForm.TypePush

open AutomorphicForm.TypePush in
theorem solution
    {H K G : Type*} [Group H] [Group K] [Group G]
    (j : H →* K) (ι' : H →* G) (hι' : Function.Injective ι')
    (C : Submodule ℂ (K → ℂ)) (hC : ∀ (k : H) (u : K → ℂ), u ∈ C → (fun κ => u (κ * j k)) ∈ C)
    (A : ↥C →ₗ[ℂ] (G → ℂ))
    (hA : ∀ (k : H) (u : ↥C) (x : G),
      A ⟨fun κ => (u : K → ℂ) (κ * j k), hC k u u.2⟩ x = A u (x * ι' k))
    {I : Type*} {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ H (W i)) (u : K → ℂ) (hu : u ∈ C)
    (hut : u ∈ ⨆ i, typeSubmodule j (ρ i)) :
    A ⟨u, hu⟩ ∈ ⨆ i, typeSubmodule ι' (ρ i) := by
  have hC' : ∀ (k : H) (u : K → ℂ), u ∈ C → rightRegular j k u ∈ C := fun k u h => hC k u h
  have hA' : ∀ (k : H) (u : ↥C) (x : G), A ⟨rightRegular j k u, hC' k u u.2⟩ x = A u (x * ι' k) :=
    fun k u x => hA k u x
  obtain ⟨Text, hText, hTextC⟩ :=
    AutomorphicForm.exists_isRightEquivariant_comp_subtype_eq_of_injective ι' hι' (rightRegular j) C hC' A hA'
  have hAu : A ⟨u, hu⟩ = Text u := by
    rw [← hTextC]
    rfl
  rw [hAu]
  have hle : (⨆ i, typeSubmodule j (ρ i)).map Text ≤ ⨆ i, typeSubmodule ι' (ρ i) := by
    rw [Submodule.map_iSup]
    exact iSup_mono fun i => map_typeSubmodule_le_of_isRightEquivariant j ι' Text hText (ρ i)
  exact hle ⟨u, hut, rfl⟩
