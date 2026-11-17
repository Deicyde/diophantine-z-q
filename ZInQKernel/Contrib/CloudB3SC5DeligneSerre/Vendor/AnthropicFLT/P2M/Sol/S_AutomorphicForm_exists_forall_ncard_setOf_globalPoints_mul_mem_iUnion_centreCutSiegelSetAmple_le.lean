/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_exists_forall_ncard_setOf_globalPoints_mul_mem_iUnion_centreCutSiegelSetAmple_le (git blob 3032ba29aef3dc147c9efad6447400b4369a2274, sha256 fda465113c707eccfb4f6002c1b5217c842baadda96f4e619c7f8445eaaa7ac3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicLsXi
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RowIsometryInvariance
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_finite_setOf_exists_globalPoints_mul_mem_image_centreCutSiegelSetAmple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_exists_forall_ncard_setOf_globalPoints_mul_mem_iUnion_centreCutSiegelSetAmple_le

set_option autoImplicit false

namespace Ws23
namespace Mult
open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel

theorem finite_and_ncard_biUnion_le {α ι : Type*} [DecidableEq ι] (T : Finset ι) (E : ι → Set α) (M : ℕ)
    (hE : ∀ i ∈ T, (E i).Finite ∧ (E i).ncard ≤ M) :
    (⋃ i ∈ T, E i).Finite ∧ (⋃ i ∈ T, E i).ncard ≤ T.card * M := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    have hE' : ∀ i ∈ T, (E i).Finite ∧ (E i).ncard ≤ M := fun i hi => hE i (Finset.mem_insert_of_mem hi)
    obtain ⟨hfin, hcard⟩ := ih hE'
    obtain ⟨hafin, hacard⟩ := hE a (Finset.mem_insert_self a T)
    rw [Finset.set_biUnion_insert, Finset.card_insert_of_notMem ha]
    refine ⟨hafin.union hfin, ?_⟩
    calc (E a ∪ ⋃ i ∈ T, E i).ncard ≤ (E a).ncard + (⋃ i ∈ T, E i).ncard := Set.ncard_union_le _ _
      _ ≤ M + T.card * M := Nat.add_le_add hacard hcard
      _ = (T.card + 1) * M := by ring

end Ws23.Mult

open NumberField NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem solution
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ κ : ℝ) (hκ : 1 ≤ κ) (hc : 0 < c) (hd₁ : 0 < d₁)
    (T : Finset (AdelicGL2 (𝓞 F) F)) :
    ∃ N : ℕ, ∀ h : AdelicGL2 (𝓞 F) F,
      {γ : Matrix.GeneralLinearGroup (Fin 2) F |
          globalPoints (𝓞 F) F γ * h ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ}.Finite ∧
        {γ : Matrix.GeneralLinearGroup (Fin 2) F |
          globalPoints (𝓞 F) F γ * h ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ}.ncard ≤ N := by
  classical

  have h1 : ∀ w : InfinitePlace F,
      archComponent F w (glArch (𝓞 F) F (1 : AdelicGL2 (𝓞 F) F)) ∈ rowIsometrySubgroup (w.Completion) := by
    intro w
    rw [map_one, map_one]
    exact one_mem _
  have hA := AutomorphicForm.finite_setOf_exists_globalPoints_mul_mem_image_centreCutSiegelSetAmple
    F c u d₁ d₂ κ hc hd₁ 1 h1
  set A : Set (Matrix.GeneralLinearGroup (Fin 2) F) := {γ | ∃ s ∈ centreCutSiegelSetAmple F c u d₁ d₂ κ,
      globalPoints (𝓞 F) F γ * s ∈ (· * (1 : AdelicGL2 (𝓞 F) F)) '' centreCutSiegelSetAmple F c u d₁ d₂ κ} with hAdef
  refine ⟨T.card * A.ncard, fun h => ?_⟩

  let E : AdelicGL2 (𝓞 F) F → Set (Matrix.GeneralLinearGroup (Fin 2) F) := fun x =>
    {γ | globalPoints (𝓞 F) F γ * h ∈ (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ}
  have hE : ∀ x ∈ T, (E x).Finite ∧ (E x).ncard ≤ A.ncard := by
    intro x _
    by_cases hne : (E x).Nonempty
    · obtain ⟨γ₁, hγ₁⟩ := hne
      obtain ⟨s₁, hs₁, hs₁eq⟩ := hγ₁

      have hmap : Set.MapsTo (fun γ => γ * γ₁⁻¹) (E x) A := by
        intro γ hγ
        obtain ⟨s, hs, hseq⟩ := hγ
        refine ⟨s₁, hs₁, s, hs, ?_⟩

        dsimp only at hs₁eq hseq ⊢
        rw [mul_one, map_mul, map_inv]
        have e1 : s₁ = globalPoints (𝓞 F) F γ₁ * h * x⁻¹ := by rw [← hs₁eq, mul_inv_cancel_right]
        have e2 : s = globalPoints (𝓞 F) F γ * h * x⁻¹ := by rw [← hseq, mul_inv_cancel_right]
        rw [e1, e2]
        group
      have hinj : Set.InjOn (fun γ => γ * γ₁⁻¹) (E x) := fun a _ b _ hab => mul_right_cancel hab
      have hfin : (E x).Finite := Set.Finite.of_injOn hmap hinj hA
      exact ⟨hfin, Set.ncard_le_ncard_of_injOn _ hmap hinj hA⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  have hsub : {γ : Matrix.GeneralLinearGroup (Fin 2) F |
      globalPoints (𝓞 F) F γ * h ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ} = ⋃ x ∈ T, E x := by
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E]
  obtain ⟨hfin, hcard⟩ := Ws23.Mult.finite_and_ncard_biUnion_le T E A.ncard hE
  rw [hsub]
  exact ⟨hfin, hcard⟩
