/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_IsEigenformWith_exists_ringHom_rationalHeckeAlgebraOne_mul_eq (git blob 82dc9e9e407e4e284cf51ffcd3b3e434ba49dd9d, sha256 ac588d7354754c0bf4ff589a3a0081fcbe84c9d3a4ffb9ed8cc038cf46f1bedb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_IsEigenformWith_exists_ringHom_rationalHeckeAlgebraOne_mul_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem CuspForm.IsEigenformWith.exists_ringHom_rationalHeckeAlgebraOne_mul_eq
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith ε h) (p : ℕ) [Fact p.Prime]
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    (S : Set ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ_[p] Ω]
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (ψ : R →+* Ω)
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff h ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M)) :
    letI := ModularCurve.heckeModuleOneBar M
    ∃ Λ : ↥(ModularCurve.rationalHeckeAlgebraOne p (ModularCurve.JOne M)) →+* Ω,
      (∀ c : ℚ_[p],
        Λ (algebraMap ℚ_[p] ↥(ModularCurve.rationalHeckeAlgebraOne p (ModularCurve.JOne M)) c)
          = algebraMap ℚ_[p] Ω c) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ℓ ∉ S →
        Λ (ModularCurve.rationalHeckeOne p (ModularCurve.JOne M) ⟨ℓ, hℓ⟩) * ψ (e ℓ) = ψ (b ℓ) ∧
        Λ (ModularCurve.rationalDiamondOne p (ModularCurve.JOne M) ℓ) * ψ (e ℓ) = 1 := by
  revert M ε h hh p hin hcomm S Ω R toC htoC ψ b e hb he
  exact @_root_.P2MW.S_CuspForm_IsEigenformWith_exists_ringHom_rationalHeckeAlgebraOne_mul_eq.solution
