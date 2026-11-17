/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers (git blob 90992dc6af6758351018f575de3b5137628f065d, sha256 c54678648b98fea1750145696c71dc307a48e29e8fa8bae2700ffe0d2ab6ea83).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
universe u v
open IsDedekindDomain
theorem IsDedekindDomain.HeightOneSpectrum.finite_residueField_adicCompletionIntegers
    {R : Type u} [CommRing R] [IsDedekindDomain R] (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  revert R K v
  exact @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers.solution
