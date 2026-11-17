/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates (git blob 3e7fcf996d8c8aea69520cabb6bc4c792d34b9af, sha256 62eb1a7a41b555b31615397e42f0500c69fba7c2eedbc9c242379c5825f255f5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    {I : Type*} [Finite I] {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [∀ i, Module.Finite ℂ (W i)] (ρ : ∀ i, Representation ℂ K (W i)) :
    ∃ (n : ℕ) (ρc : K →* Matrix (Fin n) (Fin n) ℂ), Continuous ρc ∧
      ∀ (G : Type*) [Group G] (ι : K →* G), Function.Injective ι →
        (∀ (T : (Fin n → ℂ) →ₗ[ℂ] (G → ℂ)),
          (∀ (k : K) (x : Fin n → ℂ), T ((ρc k).mulVec x) = fun y => T x (y * ι k)) →
          ∀ x : Fin n → ℂ, T x ∈ ⨆ i, typeSubmodule ι (ρ i)) ∧
        (∀ f ∈ ⨆ i, typeSubmodule ι (ρ i), (∀ y : G, Continuous fun k : K => f (y * ι k)) →
          ∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] (G → ℂ)),
            (∀ (k : K) (x : Fin m → (Fin n → ℂ)), T (fun j => (ρc k).mulVec (x j)) = fun y => T x (y * ι k)) ∧
            LinearMap.range T = Submodule.span ℂ (Set.range fun k : K => fun y : G => f (y * ι k))) := by
  revert K I W ρ
  exact @_root_.P2MW.S_AutomorphicForm_exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates.solution
