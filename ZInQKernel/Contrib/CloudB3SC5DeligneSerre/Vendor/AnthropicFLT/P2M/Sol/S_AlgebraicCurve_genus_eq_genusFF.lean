/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_genus_eq_genusFF (git blob 8934e762d271ad22040ee4577de7e86a6530fea1, sha256 f9dd80fa3422d4951453313c309f3980d7d4179003ce1a2a7a8d557caf44559d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RiemannRochRows
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_ell_canonicalDivisor_eq_genus_of_riemannRoch

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_genus_eq_genusFF

open AlgebraicCurve KaehlerDifferential

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates]
    (hRR : AlgebraicCurve.FunctionFieldRiemannRoch K F) (hWDA : AlgebraicCurve.WeilDualityAdelic K F)
    (hC : AlgebraicCurve.ConstantsAreBase K F) :
    AlgebraicCurve.genus K F = AlgebraicCurve.genusFF K F := by
  haveI : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄K])
  have h1 : (indexOfSpecialty (0 : Divisor K F) : ℤ) = (ell (canonicalDivisorOf hω - 0) : ℤ) := hWDA hω 0
  rw [sub_zero] at h1
  have h2 : (ell (canonicalDivisorOf hω) : ℤ) = (genus K F : ℤ) :=
    ell_canonicalDivisor_eq_genus_of_riemannRoch hRR hC hω
  have h3 : indexOfSpecialty (0 : Divisor K F) = Module.finrank K (H1 (0 : Divisor K F)) :=
    indexOfSpecialty_eq_finrank_H1 0
  have h4 : (indexOfSpecialty (0 : Divisor K F) : ℤ) = (genusFF K F : ℤ) := by
    rw [genusFF, ← h3]
  have : (genus K F : ℤ) = (genusFF K F : ℤ) := by
    rw [← h4, h1, h2]
  exact_mod_cast this
