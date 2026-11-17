/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_diamondFrobeniusSimilitudePairing_rationalTateModule_jH (git blob da0b91200116ce099186ae77bb83ee8170e15fd2, sha256 003a9f78f48b81220f1f4b4693f70b68144608e6c76cd3f5578714e7fb481241).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_diamondFrobeniusSimilitudePairing_rationalTateModule_jH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.exists_diamondFrobeniusSimilitudePairing_rationalTateModule_jH
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H) :
    ∃ B : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H)) →ₗ[ℚ_[p]]
        TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H)) →ₗ[ℚ_[p]] ℚ_[p],
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime)
          (x y : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H))),
        B ((ModularCurve.JH.tateEnd M H p
              (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
                ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ)).baseChange ℚ_[p] x) y =
          B x ((ModularCurve.JH.tateEnd M H p
              (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
                ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ)).baseChange ℚ_[p] y)) ∧
      (∀ (d : (ZMod M)ˣ) (x y : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H))),
        B ((ModularCurve.JH.tateEnd M H p (ModularCurve.diamondHBar M H d)).baseChange ℚ_[p] x) y =
          B x ((ModularCurve.JH.tateEnd M H p (ModularCurve.diamondHBar M H d)).baseChange ℚ_[p] y)) ∧
      (∀ v, B v v = 0) ∧
      (∀ v, (∀ w, B v w = 0) → v = 0) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            ∀ x y : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H)),
              B ((ModularCurve.JH.tateEnd M H p (ModularCurve.diamondHBar M H
                    (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))).baseChange
                  ℚ_[p] ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] x))
                ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] y) =
              (ℓ : ℚ_[p]) * B x y) := by
  revert M p H hin
  exact @_root_.P2MW.S_ModularCurve_exists_diamondFrobeniusSimilitudePairing_rationalTateModule_jH.solution
