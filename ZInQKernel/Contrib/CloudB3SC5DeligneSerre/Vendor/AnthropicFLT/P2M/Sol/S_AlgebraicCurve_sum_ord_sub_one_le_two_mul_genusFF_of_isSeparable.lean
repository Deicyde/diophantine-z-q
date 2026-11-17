/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable (git blob fa2d81ee7a144f917129e7ae5c4aa5d2c699e36c, sha256 e98fab30cbb633b6ac9dc319908b25c9ea4816b6055f55e6bcbe0276a5d66c06).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Differentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ord_sub_one_le_ordDiff_D_of_perfectField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable

open AlgebraicCurve

namespace HurwitzRamificationOverLine

variable {k : Type*} {F : Type*} [Field k] [Field F] [Algebra k F]

theorem ord_nonneg_of_ord_sub_algebraMap_pos (P : Place k F) (x : F) (a : k)
    (h : 0 < P.ord (x - algebraMap k F a)) : 0 ≤ P.ord x := by
  have h1 : P.adicValuation (x - algebraMap k F a) ≤ 1 :=
    P.adicValuation_le_one_iff.mpr (Or.inr h.le)
  have h2 : P.adicValuation (algebraMap k F a) ≤ 1 := P.adicValuation_algebraMap_le_one a
  have h3 : P.adicValuation x ≤ 1 := by
    have hx : x = (x - algebraMap k F a) + algebraMap k F a := by ring
    rw [hx]
    exact Valuation.map_add_le _ h1 h2
  rcases P.adicValuation_le_one_iff.mp h3 with hx0 | hx0
  · simp [hx0]
  · exact hx0

theorem D_sub_algebraMap (x : F) (a : k) :
    KaehlerDifferential.D k F (x - algebraMap k F a) = KaehlerDifferential.D k F x := by
  rw [map_sub, Derivation.map_algebraMap, sub_zero]

end HurwitzRamificationOverLine

theorem solution
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F)
    (T : Finset (Place k F)) (a : Place k F → k)
    (hT : ∀ P ∈ T, 0 < P.ord (x - algebraMap k F (a P)))
    (Tinf : Finset (Place k F)) (hTinf : ∀ P ∈ Tinf, P.ord x < 0) :
    ∑ P ∈ T, (P.ord (x - algebraMap k F (a P)) - 1) + ∑ P ∈ Tinf, (-P.ord x - 1) ≤
      2 * (genusFF k F : ℤ) - 2 +
        2 * (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by
  haveI := hfin
  haveI := hsep

  have hmain :=
    AlgebraicCurve.sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable k x hx hfin hsep T
      (fun P hP =>
        HurwitzRamificationOverLine.ord_nonneg_of_ord_sub_algebraMap_pos P x (a P) (hT P hP))
      Tinf hTinf

  have hDx : KaehlerDifferential.D k F x ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental k x hx

  have hloc : ∀ P ∈ T,
      P.ord (x - algebraMap k F (a P)) - 1 ≤ P.ordDiff (KaehlerDifferential.D k F x) := by
    intro P hP
    have hD : KaehlerDifferential.D k F (x - algebraMap k F (a P)) ≠ 0 := by
      rwa [HurwitzRamificationOverLine.D_sub_algebraMap]
    have h :=
      AlgebraicCurve.Place.ord_sub_one_le_ordDiff_D_of_perfectField (K := k) x P hD
    rwa [HurwitzRamificationOverLine.D_sub_algebraMap] at h
  have hsum :
      ∑ P ∈ T, (P.ord (x - algebraMap k F (a P)) - 1) ≤
        ∑ P ∈ T, P.ordDiff (KaehlerDifferential.D k F x) :=
    Finset.sum_le_sum hloc
  linarith
