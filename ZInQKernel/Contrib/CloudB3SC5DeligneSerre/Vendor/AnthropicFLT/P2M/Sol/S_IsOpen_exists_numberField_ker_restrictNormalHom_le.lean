/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_IsOpen_exists_numberField_ker_restrictNormalHom_le (git blob 20b1c22eb6876943f8e76582ade28d1073e470e0, sha256 90271adb1e11ef71ed0b98a705fdf3ee094b008d26e04ac43a58080c6d12a734).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_IsOpen_exists_numberField_ker_restrictNormalHom_le

set_option autoImplicit false

noncomputable section
namespace P2mWs11LV

theorem exists_numberField_ker_restrictNormalHom_le
    (L₁ L₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L₁] [FiniteDimensional ℚ L₂] :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
      (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        σ ∈ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker →
        (∀ x ∈ L₁, σ x = x) ∧ (∀ x ∈ L₂, σ x = x) := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Normal ℚ (AlgebraicClosure ℚ) :=
    normal_iff.mpr fun x =>
      ⟨(Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral, IsAlgClosed.splits _⟩
  let E : IntermediateField ℚ (AlgebraicClosure ℚ) := L₁ ⊔ L₂
  haveI : FiniteDimensional ℚ E := IntermediateField.finiteDimensional_sup L₁ L₂
  let Fi : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)
  haveI hfd : FiniteDimensional ℚ Fi := normalClosure.is_finiteDimensional ℚ E (AlgebraicClosure ℚ)
  haveI hn : Normal ℚ Fi := normalClosure.normal ℚ E (AlgebraicClosure ℚ)
  haveI : Algebra.IsSeparable ℚ Fi := Algebra.IsSeparable.of_integral ℚ Fi
  haveI hg : IsGalois ℚ Fi := IsGalois.mk
  have hE : E ≤ Fi := IntermediateField.le_normalClosure E
  have hinst : (Fi.algebra : Algebra ℚ Fi) = (DivisionRing.toRatAlgebra : Algebra ℚ Fi) :=
    Subsingleton.elim _ _
  refine ⟨Fi, inferInstance, ?_, ?_, inferInstance, ?_, ?_⟩
  · exact { to_charZero := inferInstance, to_finiteDimensional := hinst ▸ hfd }
  · exact hinst ▸ hg
  · exact hinst ▸ (inferInstance : IsScalarTower ℚ Fi (AlgebraicClosure ℚ))
  · intro σ hσ
    have h1 : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) Fi) σ = 1 :=
      MonoidHom.mem_ker.mp hσ
    have hfix : ∀ x : AlgebraicClosure ℚ, x ∈ Fi → σ x = x := by
      intro x hx
      have h2 := AlgEquiv.restrictNormal_commutes σ Fi ⟨x, hx⟩
      change (AlgEquiv.restrictNormalHom Fi σ) = 1 at h1
      rw [show σ.restrictNormal Fi = AlgEquiv.restrictNormalHom Fi σ from rfl, h1] at h2
      simpa using h2.symm
    exact ⟨fun x hx => hfix x (hE ((le_sup_left : L₁ ≤ E) hx)),
      fun x hx => hfix x (hE ((le_sup_right : L₂ ≤ E) hx))⟩

theorem exists_finiteDimensional_fixingSubgroup_le
    {H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (hH : IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ E, σ x = x) → σ ∈ H := by
  obtain ⟨E, hE, hEH⟩ := (krullTopology_mem_nhds_one_iff ℚ (AlgebraicClosure ℚ) H).mp (hH.mem_nhds H.one_mem)
  refine ⟨E, hE, fun σ hσ => hEH ?_⟩
  exact (IntermediateField.mem_fixingSubgroup_iff E σ).mpr fun x hx => hσ x hx

end P2mWs11LV
end

theorem solution
    {H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (hH : IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
      (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
      (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H := by
  obtain ⟨E, hE, hEH⟩ := P2mWs11LV.exists_finiteDimensional_fixingSubgroup_le hH
  haveI := hE
  obtain ⟨F, iF, iNF, iG, iA, iT, hF⟩ := P2mWs11LV.exists_numberField_ker_restrictNormalHom_le E E
  exact ⟨F, iF, iNF, iG, iA, iT, fun σ hσ => hEH σ (hF σ hσ).1⟩
