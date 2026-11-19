/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_frickeAlgEquiv_xHFunctionFieldBar (git blob b1958ee647959a50255641bee4883f46f0a183d5, sha256 27835990e27f7735787249e614bac998d29528dedf3e1e12e3a38e0733052601).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_frickeAlgEquiv_xHFunctionFieldBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_frickeAlgEquiv_xHFunctionFieldBar (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) :
    ∃ w : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      (∀ (ℓ : ℕ) [Fact ℓ.Prime]
          (hα : HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
          (hβ : HeckeBetaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
          [HasPrincipalDivisors (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
          (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hβ)
          (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ))
          (hNα : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hfinα)
          (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hα)
          (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ))
          (hNβ : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hfinβ)
          (x : JH M H),
        heckePic0HBarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut w • x)
          = SemilinearAut.ofAlgAut w • heckePic0HBar hα hβ hFIβ hfinα hNα x) ∧
      (∀ (d : (ZMod M)ˣ) (x : JH M H),
        diamondHBar M H d (SemilinearAut.ofAlgAut w • diamondHBar M H d x)
          = SemilinearAut.ofAlgAut w • x) ∧
      (∀ x : JH M H, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (A : ValuationSubring (AlgebraicClosure ℚ)),
        A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            ∀ x : JH M H,
              SemilinearAut.ofAlgAut w • (σ • x)
                = σ • diamondHBar M H
                    (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))
                    (SemilinearAut.ofAlgAut w • x)) := by
  revert M H
  exact @_root_.P2MW.S_ModularCurve_exists_frickeAlgEquiv_xHFunctionFieldBar.solution
