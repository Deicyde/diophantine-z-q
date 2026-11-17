/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_exists_isCompactOperator_isSymmetric_lift_rightConv (git blob 3e017fade42d9bf7bff2065ef04d923cde8b0628, sha256 1340063cc418b56f06e646ef72c26f37e64ddb4d3c89859394b88748dedc4be8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightConv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isCompactOperator_lift_rightConv_comp_cuspSubcarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_apply_mem_cuspSubcarrier_of_isLift_rightConv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isCompactOperator_isSymmetric_lift_rightConv

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open _root_.AutomorphicForm
namespace AutomorphicForm
end AutomorphicForm
open _root_.P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isCompactOperator_isSymmetric_lift_rightConv.AutomorphicForm
open _root_.AutomorphicForm.CuspidalConstituent
open _root_.AutomorphicForm.CuspidalSpectrum
namespace AutomorphicForm.CuspidalSpectrum
end AutomorphicForm.CuspidalSpectrum
open _root_.P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isCompactOperator_isSymmetric_lift_rightConv.AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace AutomorphicForm
export _root_.AutomorphicForm (AdelicGL2 rightConv IsFactorizableTestFn continuous_and_hasCompactSupport_of_isFactorizableTestFn CuspidalSpectrum.exists_isLift_rightConv CuspidalSpectrum.isCompactOperator_lift_rightConv_comp_cuspSubcarrier CuspidalSpectrum.apply_mem_cuspSubcarrier_of_isLift_rightConv)
namespace CuspidalSpectrum
export _root_.AutomorphicForm.CuspidalSpectrum (IsSlabFundamentalDomain HasModulus Carrier memberSubmodule contMemberSubmodule cuspMemberSubmodule toCarrier cuspSubcarrier toCuspSubcarrier toCuspSubcarrier_apply_coe IsLift flat exists_isLift_rightConv isCompactOperator_lift_rightConv_comp_cuspSubcarrier apply_mem_cuspSubcarrier_of_isLift_rightConv)
namespace C8S5
open _root_.AutomorphicForm.CuspidalSpectrum
open _root_.AutomorphicForm

variable {F : Type} [Field F] [NumberField F]

theorem cuspMember_le_member (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    cuspMemberSubmodule F Φ₀ ξ ≤ memberSubmodule F Φ₀ ξ := fun _ h => h.1.1.1

theorem cuspMember_le_contMember (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    cuspMemberSubmodule F Φ₀ ξ ≤ contMemberSubmodule F Φ₀ ξ := fun _ h => ⟨h.1.1.1, h.2⟩

def ιc {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    ↥(cuspMemberSubmodule F Φ₀ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
  LinearMap.codRestrict _ ((toCarrier F hΦ₀ σ ξ).comp (Submodule.inclusion (cuspMember_le_member Φ₀ ξ)))
    (fun φ => Submodule.le_topologicalClosure _
      ⟨Submodule.inclusion (cuspMember_le_member Φ₀ ξ) φ, by
        show (Submodule.inclusion (cuspMember_le_member Φ₀ ξ) φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspMemberSubmodule F Φ₀ ξ
        exact φ.2, rfl⟩)

theorem toCuspSubcarrier_apply_coe {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) :
    (toCuspSubcarrier F hΦ₀ σ ξ φ : Carrier F Φ₀ σ) = toCarrier F hΦ₀ σ ξ ⟨φ, cuspMember_le_member Φ₀ ξ φ.2⟩ := rfl

theorem eqOn_cuspSubcarrier_of_isLift {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    {Tfun : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ)} {T T' : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ}
    (hT : IsLift F hΦ₀ σ ξ Tfun T) (hT' : IsLift F hΦ₀ σ ξ Tfun T') :
    ∀ v ∈ cuspSubcarrier F hΦ₀ σ ξ, T v = T' v := by
  intro v hv
  have key : Set.EqOn T T' ((Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ))) :
        Set (Carrier F Φ₀ σ)) := by
    rintro _ ⟨ψ, hψ, rfl⟩
    have hψc : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ contMemberSubmodule F Φ₀ ξ := ⟨ψ.2, hψ.2⟩
    have e1 := hT.comm (ψ : AdelicGL2 (𝓞 F) F → ℂ) hψc
    have e2 := hT'.comm (ψ : AdelicGL2 (𝓞 F) F → ℂ) hψc
    have hψeq : (⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), hψc.1⟩ : ↥(memberSubmodule F Φ₀ ξ)) = ψ := Subtype.ext rfl
    rw [hψeq] at e1 e2
    show T (toCarrier F hΦ₀ σ ξ ψ) = T' (toCarrier F hΦ₀ σ ξ ψ)
    rw [e1, e2]
  have hcl := key.closure T.continuous T'.continuous
  have hv' : v ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ))) : Set (Carrier F Φ₀ σ)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hv
  exact hcl hv'

end AutomorphicForm.CuspidalSpectrum.C8S5

end

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm.CuspidalSpectrum.C8S5 in
theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hflat : flat F σ f = f) :
    ∃ Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      IsCompactOperator Tc ∧ (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)).IsSymmetric ∧
      ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ),
        Tc (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩ := by
  obtain ⟨hfc, hfs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  obtain ⟨T, T', hT, hT', hadj⟩ := AutomorphicForm.CuspidalSpectrum.exists_isLift_rightConv F α β Φ₀ hΦ₀ σ ξ hσ f hfc hfs
  rw [hflat] at hT'
  have hinv := (fun v hv => AutomorphicForm.CuspidalSpectrum.apply_mem_cuspSubcarrier_of_isLift_rightConv F hΦ₀ σ ξ hσ f hf T hT v hv)
  have heq := eqOn_cuspSubcarrier_of_isLift hΦ₀ σ ξ hT hT'
  set E := cuspSubcarrier F hΦ₀ σ ξ with hE
  let Tc : ↥E →L[ℂ] ↥E := T.restrict hinv
  refine ⟨Tc, ?_, ?_, ?_⟩
  ·
    have hcpt := AutomorphicForm.CuspidalSpectrum.isCompactOperator_lift_rightConv_comp_cuspSubcarrier F α β Φ₀ hΦ₀ σ ξ hσ f hf T hT
    have hclosed : IsClosed (E : Set (Carrier F Φ₀ σ)) := by
      rw [hE]; exact Submodule.isClosed_topologicalClosure _
    have := hcpt.codRestrict (V := E) (fun x => hinv x x.2) hclosed
    exact this
  ·
    intro x y
    show ⟪((Tc x : ↥E) : Carrier F Φ₀ σ), (y : Carrier F Φ₀ σ)⟫_ℂ = ⟪(x : Carrier F Φ₀ σ), ((Tc y : ↥E) : Carrier F Φ₀ σ)⟫_ℂ
    have e1 : ((Tc x : ↥E) : Carrier F Φ₀ σ) = T x := rfl
    have e2 : ((Tc y : ↥E) : Carrier F Φ₀ σ) = T y := rfl
    rw [e1, e2, ← ContinuousLinearMap.adjoint_inner_right, hadj, ← heq y y.2]
  · intro φ hφ'
    apply Subtype.ext
    show T (toCuspSubcarrier F hΦ₀ σ ξ φ : Carrier F Φ₀ σ) = _
    rw [toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
    have hφc : (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ contMemberSubmodule F Φ₀ ξ := cuspMember_le_contMember Φ₀ ξ φ.2
    have := hT.comm (φ : AdelicGL2 (𝓞 F) F → ℂ) hφc
    exact this
