/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_diamond_mul_coordDet_eq_of_basis_rationalTateModule_jH (git blob 4bd0c408936ad590f36da80bbfbda6a1b8978758, sha256 b6ee759d64e11b69239a4dfb6506928486c4bcf41ee3c52f1db7add8b965b41b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_diamond_mul_coordDet_eq_of_basis_rationalTateModule_jH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.diamond_mul_coordDet_eq_of_basis_rationalTateModule_jH
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Finset ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (b : Module.Basis (Fin 2)
      ↥(Algebra.adjoin ℚ_[p] (Set.range fun g : CohCarrier.Gen M (↑S : Set ℕ) =>
          (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p g).baseChange ℚ_[p]))
      (TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H))))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M) (hℓp : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) :
    (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p (CohCarrier.Gen.dia
        (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))).baseChange ℚ_[p] *
      (↑((b.repr ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] (b 0))) 0 *
            (b.repr ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] (b 1))) 1 -
          (b.repr ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] (b 1))) 0 *
            (b.repr ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] (b 0))) 1) :
        Module.End ℚ_[p] (TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H)))) =
      (ℓ : Module.End ℚ_[p] (TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H)))) := by
  revert M p H S hin b ℓ hℓ hℓS hℓM hℓp A hA σ hσ
  exact @_root_.P2MW.S_ModularCurve_diamond_mul_coordDet_eq_of_basis_rationalTateModule_jH.solution
