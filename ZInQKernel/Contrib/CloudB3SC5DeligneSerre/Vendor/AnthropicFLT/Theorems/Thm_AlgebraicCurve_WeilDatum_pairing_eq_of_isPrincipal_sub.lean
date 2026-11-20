/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_WeilDatum_pairing_eq_of_isPrincipal_sub (git blob f307b9222318f073a37c454ec7a6fdac1b83ff8a, sha256 88bd45d6718c3e9ee84bde821fcadd433fa4c99a6f5f7edb3df063f76616ba26).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_WeilDatum
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_WeilDatum_pairing_eq_of_isPrincipal_sub

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.WeilDatum.pairing_eq_of_isPrincipal_sub {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]
    (hrec : WeilReciprocity K F)
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → ∃ c : K, u = algebraMap K F c)
    (hmove : ∀ (x : Pic0.torsion K F n) (S : Finset (Place K F)),
      ∃ D : Divisor.degZero (K := K) (F := F),
        Pic0.mk D = (x : Pic0 K F) ∧
        (∀ v ∈ (D : Divisor K F).support, Place.IsRational v) ∧
        (∀ v ∈ (D : Divisor K F).support, v ∉ S))
    (d d' : WeilDatum K F n)
    (hL : Divisor.IsPrincipal (d'.D₁ - d.D₁)) (hR : Divisor.IsPrincipal (d'.D₂ - d.D₂)) :
    d'.pairing = d.pairing := by
  revert K F n hrec hconst hmove d d' hL hR
  exact @_root_.P2MW.S_AlgebraicCurve_WeilDatum_pairing_eq_of_isPrincipal_sub.solution
