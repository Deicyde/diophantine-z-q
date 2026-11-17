/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalConstituent_inf_eq_bot_or_le_of_isCuspConstituent (git blob 748e07941e87d744c10a0027c6dd77e9027e6956, sha256 8755279057f32deae48894fed85bc8796c6aee6ea1d94e1e0b58678fa04053d1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalConstituent_iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_inf_eq_bot_or_le_of_isCuspConstituent

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open _root_.AutomorphicForm
namespace AutomorphicForm
end AutomorphicForm
open _root_.P2MW.S_AutomorphicForm_CuspidalConstituent_inf_eq_bot_or_le_of_isCuspConstituent.AutomorphicForm
open _root_.AutomorphicForm.WindowedSiegel
open _root_.AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open _root_.AutomorphicForm.CuspidalConstituent
namespace AutomorphicForm.CuspidalConstituent
end AutomorphicForm.CuspidalConstituent
open _root_.P2MW.S_AutomorphicForm_CuspidalConstituent_inf_eq_bot_or_le_of_isCuspConstituent.AutomorphicForm.CuspidalConstituent
open scoped BigOperators

namespace AutomorphicForm
export _root_.AutomorphicForm (rowIsometryInclAt₀ ArchTypeFamily archCutSubmodule IsArchBiFinite CarrierPins productionPinsOf AdelicGL2 finiteAdelicGL2Subgroup rightConv rowIsometrySubgroup₀ IsFactorizableTestFn CuspidalConstituent.iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le)
namespace CuspidalConstituent
export _root_.AutomorphicForm.CuspidalConstituent (rightTranslate IsCuspSubrep IsCuspConstituent levelInvariantSubmodule iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le)
namespace C8F55
open _root_.AutomorphicForm.CuspidalConstituent
open _root_.AutomorphicForm

variable {F : Type} [Field F] [NumberField F]

theorem isCuspSubrep_iInf₂ {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {P : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) → Prop}
    (hP : ∀ W, P W → IsCuspSubrep F pins ξ W) {W₀ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (hW₀ : P W₀) :
    IsCuspSubrep F pins ξ (⨅ (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (_ : P W), W) := by
  refine ⟨(iInf₂_le W₀ hW₀).trans (hP W₀ hW₀).le, fun g hg φ hφ => ?_, fun w k φ hφ => ?_, fun f tys hf hbf φ hφ => ?_⟩
  · simp only [Submodule.mem_iInf] at hφ ⊢
    exact fun W hW => (hP W hW).rightTranslate_fin_mem g hg φ (hφ W hW)
  · simp only [Submodule.mem_iInf] at hφ ⊢
    exact fun W hW => (hP W hW).rightTranslate_arch_mem w k φ (hφ W hW)
  · simp only [Submodule.mem_iInf] at hφ ⊢
    exact fun W hW => (hP W hW).rightConv_mem f tys hf hbf φ (hφ W hW)

end AutomorphicForm.CuspidalConstituent.C8F55

open AutomorphicForm.CuspidalConstituent.C8F55 in
theorem solution
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V)
    (M : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hMk : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ φ ∈ M, rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ M)
    (hMhecke : ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F),
      (∀ i, ∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, ∃ u' ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, reps i = u * g * u') →
      (∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, ∃ u' ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, x = u * g * u') →
        ∃ i, ∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, x = reps i * u) →
      (∀ i j, (reps i)⁻¹ * reps j ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N → i = j) →
      ∀ φ ∈ M ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N,
        (fun x => ∑ i, φ (x * reps i)) ∈ M)
    (hMconv : ∀ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f → IsArchBiFinite F tys f →
      (∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, f (u * x) = f x ∧ f (x * u) = f x) →
      ∀ φ ∈ M, rightConv F φ f ∈ M) :
    V ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ⊓ M = ⊥ ∨
      V ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ≤ M := by
  classical
  by_cases hY : V ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ⊓ M = ⊥
  · exact Or.inl hY
  right

  set Y := V ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ⊓ M with hYdef
  set W₀ := ⨅ (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (_ : IsCuspSubrep F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ W ∧ Y ≤ W), W with hW₀
  have hVin : IsCuspSubrep F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V ∧ Y ≤ V :=
    ⟨hV.1, inf_le_left.trans (inf_le_left.trans inf_le_left)⟩
  have hW₀rep : IsCuspSubrep F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ W₀ := isCuspSubrep_iInf₂ (fun W hW => hW.1) hVin
  have hW₀V : W₀ ≤ V := iInf₂_le V hVin
  have hYW₀ : Y ≤ W₀ := le_iInf₂ fun W hW => hW.2
  have hW₀ne : W₀ ≠ ⊥ := fun h => hY (le_bot_iff.mp (h ▸ hYW₀))

  have hW₀eq : W₀ = V := (hV.2.2 W₀ hW₀rep hW₀V).resolve_left hW₀ne

  have hcut := AutomorphicForm.CuspidalConstituent.iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le
    F D ξ N hN tys V hV.1 M hMk hMhecke hMconv

  have : W₀ ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ≤ M := hcut
  rw [hW₀eq] at this
  exact this
