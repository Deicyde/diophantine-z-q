/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt (git blob 945f35ac8330b31ca0d9b0c5c256c092dc902606, sha256 a042acc7d7ed28fc431754a08e9c7361711df21fcaaa67fef9124e2a4c30537e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_RepTheory_SmoothVectors
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open FLT.SmoothVectors
open AutomorphicForm

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def finiteAdelicGL2Subgroup : Subgroup (AdelicGL2 (𝓞 F) F) :=
  MonoidHom.ker (NumberField.AdelicLevel.glArch (𝓞 F) F)

theorem mem_finiteAdelicGL2Subgroup_iff (g : AdelicGL2 (𝓞 F) F) :
    g ∈ finiteAdelicGL2Subgroup F ↔ NumberField.AdelicLevel.glArch (𝓞 F) F g = 1 :=
  Iff.rfl

theorem isClosed_finiteAdelicGL2Subgroup :
    IsClosed (finiteAdelicGL2Subgroup F : Set (AdelicGL2 (𝓞 F) F)) := by
  have : finiteAdelicGL2Subgroup F
      = (NumberField.AdelicLevel.glArch (𝓞 F) F) ⁻¹' {1} := by
    ext g; exact Iff.rfl
  rw [this]
  exact (isClosed_singleton).preimage (NumberField.AdelicLevel.continuous_glArch (𝓞 F) F)

def IsKfSmooth (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  IsSmoothVector (finiteAdelicGL2Subgroup F)
    (RightTranslationFn.mk φ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ)

theorem isKfSmooth_iff (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    IsKfSmooth F φ ↔
      IsSmoothVector (finiteAdelicGL2Subgroup F) (RightTranslationFn.mk φ) :=
  Iff.rfl

theorem isSmoothVector_rightTranslationFn_const {G : Type*} [Group G] [TopologicalSpace G]
    {M : Type*} (c : M) :
    IsSmoothVector G (RightTranslationFn.mk (fun (_ : G) => c)) := by
  rw [isSmoothVector_iff_isOpen_stabilizer]
  convert isOpen_univ using 2
  rw [Set.eq_univ_iff_forall]
  intro g
  exact MulAction.mem_stabilizer_iff.mpr (RightTranslationFn.ext fun _ => rfl)

theorem isKfSmooth_const (c : ℂ) : IsKfSmooth F (fun _ => c) :=
  (isSmoothVector_rightTranslationFn_const c).restrict_subgroup (finiteAdelicGL2Subgroup F)

theorem isKfSmooth_zero : IsKfSmooth F (fun _ => (0 : ℂ)) := isKfSmooth_const F 0

theorem isSmoothVector_of_discreteTopology {G : Type*} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] {M : Type*} [MulAction G M] (v : M) : IsSmoothVector G v :=
  isOpen_discrete _

theorem isSmoothVector_bot_rightTranslationFn {G : Type*} [Group G] [TopologicalSpace G]
    {M : Type*} (φ : G → M) :
    IsSmoothVector (⊥ : Subgroup G) (RightTranslationFn.mk φ) :=
  isSmoothVector_of_discreteTopology _

def IsSmoothAutomorphicFnAt (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  IsAutomorphicFnAt F pins ξ φ ∧ IsKfSmooth F φ

def IsSmoothCuspAutomorphicFnAt (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  IsCuspAutomorphicFnAt F pins ξ φ ∧ IsKfSmooth F φ

theorem isSmoothAutomorphicFnAt_zero (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) :
    IsSmoothAutomorphicFnAt F pins ξ (fun _ => (0 : ℂ)) :=
  ⟨isAutomorphicFnAt_zero F pins ξ, isKfSmooth_zero F⟩

theorem isSmoothCuspAutomorphicFnAt_zero (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) :
    IsSmoothCuspAutomorphicFnAt F pins ξ (fun _ => (0 : ℂ)) :=
  ⟨isCuspAutomorphicFnAt_zero F pins ξ, isKfSmooth_zero F⟩

theorem isSmoothAutomorphicFnAt_one_trivial (pins : CarrierPins F)
    (hDfin : @pins.μ pins.D < ⊤) :
    IsSmoothAutomorphicFnAt F pins (1 : pins.Z →* ℂˣ) (fun _ => (1 : ℂ)) :=
  ⟨isAutomorphicFnAt_one_trivial F pins hDfin, isKfSmooth_const F 1⟩

theorem not_isSmoothCuspAutomorphicFnAt_one (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    [@IsProbabilityMeasure _ pins.nS pins.ν] :
    ¬ IsSmoothCuspAutomorphicFnAt F pins ξ (fun _ => (1 : ℂ)) :=
  fun h => not_isCuspAutomorphicFnAt_one F pins ξ h.1

end AutomorphicForm

end
