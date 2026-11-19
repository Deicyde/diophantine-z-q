/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep (git blob 401d9e32f2a7a790df4e519617502822518f6b51, sha256 8dc5e7d6d0a876aec0343b13109e928b710dc3e05d0920b19384a6341a2c7cda).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm.CuspidalConstituent

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace AutomorphicForm

namespace CuspidalSpectrum

variable (F : Type) [Field F] [NumberField F]

def IsCuspLift {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Prop :=
  ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (h : op φ ∈ cuspMemberSubmodule F Φ₀ ξ),
    S (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨op φ, h⟩

theorem isCuspLift_iff {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) :
    IsCuspLift F hΦ₀ σ ξ op S ↔
      ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (h : op φ ∈ cuspMemberSubmodule F Φ₀ ξ),
        S (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨op φ, h⟩ := Iff.rfl

theorem isCuspLift_of_forall_exists {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hS : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ), ∃ h : op φ ∈ cuspMemberSubmodule F Φ₀ ξ,
      S (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨op φ, h⟩) :
    IsCuspLift F hΦ₀ σ ξ op S := fun φ h => by
  obtain ⟨h', e⟩ := hS φ
  exact e

structure IsClosedCuspSubrep {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Prop where
  isClosed : IsClosed (M : Set ↥(cuspSubcarrier F hΦ₀ σ ξ))
  map_le_of_rightTranslate_fin : ∀ g ∈ finiteAdelicGL2Subgroup F,
    ∀ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      IsCuspLift F hΦ₀ σ ξ (rightTranslate F g) S →
        M.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M
  map_le_of_rightTranslate_arch : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
    ∀ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      IsCuspLift F hΦ₀ σ ξ (rightTranslate F (rowIsometryInclAt₀ F w k)) S →
        M.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M
  map_le_of_rightConv : ∀ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F),
    IsFactorizableTestFn F f → IsArchBiFinite F tys f →
      ∀ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
        IsCuspLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) S →
          M.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M

def IsIrreducibleCuspSubrep {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Prop :=
  IsClosedCuspSubrep F hΦ₀ σ ξ M ∧ M ≠ ⊥ ∧
    ∀ M' : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ), IsClosedCuspSubrep F hΦ₀ σ ξ M' → M' ≤ M → M' = ⊥ ∨ M' = M

theorem isClosedCuspSubrep_top {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) : IsClosedCuspSubrep F hΦ₀ σ ξ ⊤ :=
  ⟨isClosed_univ, fun _ _ _ _ => le_top, fun _ _ _ _ => le_top, fun _ _ _ _ _ _ => le_top⟩

theorem isClosedCuspSubrep_bot {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) : IsClosedCuspSubrep F hΦ₀ σ ξ ⊥ :=
  ⟨by simp, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ _ _ => by simp⟩

theorem not_isIrreducibleCuspSubrep_bot {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    ¬ IsIrreducibleCuspSubrep F hΦ₀ σ ξ ⊥ := fun h => h.2.1 rfl

theorem IsIrreducibleCuspSubrep.isClosedCuspSubrep {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    {hΦ₀ : IsSlabFundamentalDomain F α β Φ₀} {σ : ℝ} {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)} (h : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M) :
    IsClosedCuspSubrep F hΦ₀ σ ξ M := h.1

theorem IsIrreducibleCuspSubrep.ne_bot {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    {hΦ₀ : IsSlabFundamentalDomain F α β Φ₀} {σ : ℝ} {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)} (h : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M) : M ≠ ⊥ := h.2.1

theorem IsClosedCuspSubrep.inf {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    {hΦ₀ : IsSlabFundamentalDomain F α β Φ₀} {σ : ℝ} {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {M M' : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)}
    (h : IsClosedCuspSubrep F hΦ₀ σ ξ M) (h' : IsClosedCuspSubrep F hΦ₀ σ ξ M') :
    IsClosedCuspSubrep F hΦ₀ σ ξ (M ⊓ M') := by
  refine ⟨h.isClosed.inter h'.isClosed, fun g hg S hS => ?_, fun w k S hS => ?_, fun f tys hf hft S hS => ?_⟩
  · exact le_inf ((Submodule.map_mono inf_le_left).trans (h.map_le_of_rightTranslate_fin g hg S hS))
      ((Submodule.map_mono inf_le_right).trans (h'.map_le_of_rightTranslate_fin g hg S hS))
  · exact le_inf ((Submodule.map_mono inf_le_left).trans (h.map_le_of_rightTranslate_arch w k S hS))
      ((Submodule.map_mono inf_le_right).trans (h'.map_le_of_rightTranslate_arch w k S hS))
  · exact le_inf ((Submodule.map_mono inf_le_left).trans (h.map_le_of_rightConv f tys hf hft S hS))
      ((Submodule.map_mono inf_le_right).trans (h'.map_le_of_rightConv f tys hf hft S hS))

end CuspidalSpectrum

end AutomorphicForm

end
