/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_isGalois_ord_dvd_twelve_qExpFunctionFieldC_gammaH_of_char_two (git blob 4536f36065c31d74222dbf68b66974d54b7bb674, sha256 586b940fe40a0a68da6700ba650659febcbf7c617cb98319c14c0ea2df88fc43).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_isGalois_ord_dvd_twelve_qExpFunctionFieldC_gammaH_of_char_two

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve ModularCurve

universe u in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_isGalois_ord_dvd_twelve_qExpFunctionFieldC_gammaH_of_char_two
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hM : ¬ 2 ∣ M)
    (K : Type u) [Field K] [IsAlgClosed K] [CharP K 2]
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hx : (x : LaurentSeries K) = jqModC K) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (ι : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] L),
      FiniteDimensional (IntermediateField.adjoin K ({ι x} : Set L)) L ∧
        IsGalois (IntermediateField.adjoin K ({ι x} : Set L)) L ∧
        ∀ P : Place K L, 0 < P.ord (ι x) → P.ord (ι x) ∣ 12 := by
  revert M H hM K x hx
  exact @_root_.P2MW.S_ModularCurve_exists_isGalois_ord_dvd_twelve_qExpFunctionFieldC_gammaH_of_char_two.solution
